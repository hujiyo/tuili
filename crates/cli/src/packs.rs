//! Registry-backed package imports for `:load` and the batch entry point.
//!
//! This module is deliberately internal to the CLI: the language layer only
//! knows that an imported namespace is already loaded, while the registry
//! decides where a package comes from, which files belong to it, and whether
//! the directory still matches `std.lock`.
//!
//! A `:load` first parses the file to find its `import` items. A file without
//! any import never touches the registry, and an import already satisfied by a
//! namespace loaded directly from a file does not either. The remaining
//! imports scan `lawpacks` in the current directory and verify the lock once
//! for the whole load; packages are then loaded depth-first, dependencies
//! before the package that imports them. An import whose namespace came from a
//! pack is always resolved here, so a changed version or hash is reported.
//!
//! A package whose manifest claims `trust = "official"` is loaded only when the
//! registry's `official.toml` lists its name, version and locked hash. A
//! missing whitelist or an unlisted release fails the import; the trust gate
//! option does not lower this check.
//!
//! The whole load runs on a cloned [`Library`] and a cloned package list. An
//! error at any step therefore leaves the session exactly as it was: no
//! declarations from a package and no package information survive a failed
//! load.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fs;
use std::path::{Component, Path, PathBuf};

use std_deduce_kernel::meta::{Scope, ScopeOrigin};
use std_deduce_lang::ast::Item;
use std_deduce_lang::module::escape_path;
use std_deduce_lang::{Library, LoadError, LoadOptions};
use std_deduce_lawpack::{
    read_whitelist, scan, verify_lock, LoadedPack, Manifest, PackError, Trust, Whitelist,
    LOCK_FILE, MANIFEST_FILE, OFFICIAL_FILE,
};

/// A pack successfully loaded into the current session.
///
/// `:inspect` prints `[name@version]` only for the declaration names this pack
/// itself contributed; the namespace alone is not enough, because the ledger is
/// flat and a declaration from another file could share the namespace. The hash
/// is kept so a later import can tell whether the registry still describes the
/// same content the session loaded. The trust level comes from the manifest and
/// is used to mark imports that are outside the active environment profile.
#[derive(Debug, Clone)]
pub(crate) struct LoadedPackInfo {
    pub(crate) name: String,
    pub(crate) version: String,
    pub(crate) trust: Trust,
    pub(crate) hash: String,
    pub(crate) namespace: String,
    /// The manifest's optional `<law-id>/<version>` corpus link. A certificate
    /// records the corpus file's hash, so the identity builder needs the link
    /// the pack was loaded with.
    pub(crate) corpus: Option<String>,
    /// Ledger names added by this pack's theory files, across all of them.
    pub(crate) decls: BTreeSet<String>,
}

/// One pack as the registry sees it after the lock has been verified.
struct RegistryPack {
    dir: PathBuf,
    manifest: Manifest,
    hash: String,
}

/// A scanned and lock-verified registry.
pub(crate) struct Registry {
    root: PathBuf,
    packs: HashMap<String, RegistryPack>,
    /// The official-release whitelist, absent when the registry has no
    /// `official.toml`. A manifest's `official` claim is honoured only through
    /// this list, so it travels with the registry that was opened.
    whitelist: Option<Whitelist>,
}

impl Registry {
    /// Scan `lawpacks` below the current working directory and verify its lock.
    ///
    /// Every error is returned, never only the first. A registry that does not
    /// exist, a bad manifest, a duplicate pack name, a missing lock and every
    /// lock mismatch are all fatal for the whole `:load`.
    pub(crate) fn open() -> Result<Registry, Vec<String>> {
        let cwd = std::env::current_dir().map_err(|error| {
            vec![format!(
                ".: error: 无法取得当前目录：{}",
                escape_path(&error.to_string())
            )]
        })?;
        Registry::open_at(cwd.join("lawpacks"))
    }

    pub(crate) fn open_at(root: PathBuf) -> Result<Registry, Vec<String>> {
        let found = scan(&root).map_err(|error| vec![render_pack_error(&error)])?;
        let mut errors: Vec<String> = found.errors.iter().map(render_pack_error).collect();

        // `scan` reports bad manifests but not duplicate names: two directories
        // may both declare the same `pack.name`. A name is the import key, so
        // it must be unique or the registry cannot choose one. A namespace is
        // likewise unique: two packs claiming one namespace could silently
        // merge their theories in the flat ledger.
        let mut by_name: BTreeMap<&str, &LoadedPack> = BTreeMap::new();
        let mut by_namespace: BTreeMap<&str, &LoadedPack> = BTreeMap::new();
        for pack in &found.packs {
            let name = pack.manifest.pack.name.as_str();
            if let Some(first) = by_name.insert(name, pack) {
                errors.push(diag(
                    &pack.dir,
                    &format!(
                        "包名 `{name}` 与 {} 重复，注册表中的包名必须唯一",
                        first.dir.display()
                    ),
                ));
            }
            if let Some(namespace) = pack.manifest.pack.namespace.as_deref() {
                if let Some(first) = by_namespace.insert(namespace, pack) {
                    errors.push(diag(
                        &pack.dir,
                        &format!(
                            "namespace `{namespace}` 与 {} 重复；两个包不能声明同一个 namespace",
                            first.dir.display()
                        ),
                    ));
                }
            }
        }
        if !errors.is_empty() {
            return Err(errors);
        }

        // The lock is verified once for this whole load. `verify_lock` also
        // reports every mismatch it finds instead of stopping at the first, and
        // returns the same lock it compared with the directory, so the hashes
        // used below are the verified ones rather than a second read.
        let report = verify_lock(&root).map_err(|lock_errors| {
            lock_errors
                .iter()
                .map(render_pack_error)
                .collect::<Vec<_>>()
        })?;

        let lock_path = root.join(LOCK_FILE);
        let mut hashes: BTreeMap<String, String> = report
            .lockfile
            .pack
            .into_iter()
            .map(|entry| (entry.name, entry.hash))
            .collect();

        // The whitelist is read after the lock verified, so the hashes it is
        // compared with are the ones the verification just compared. A file
        // that cannot be read or validated fails the whole registry instead of
        // letting an `official` claim through unchecked.
        let whitelist = read_whitelist(&root)
            .map_err(|errors| errors.iter().map(render_pack_error).collect::<Vec<_>>())?;

        let mut packs = HashMap::new();
        for pack in found.packs {
            let name = pack.manifest.pack.name.clone();
            let hash = hashes
                .remove(&name)
                .ok_or_else(|| vec![diag(&lock_path, &format!("锁中缺少包 `{name}` 的哈希"))])?;
            packs.insert(
                name,
                RegistryPack {
                    dir: pack.dir,
                    manifest: pack.manifest,
                    hash,
                },
            );
        }
        Ok(Registry {
            root,
            packs,
            whitelist,
        })
    }

    fn find(&self, name: &str) -> Option<&RegistryPack> {
        self.packs.get(name)
    }

    /// Check that an `official` claim is covered by the whitelist.
    ///
    /// The claim is honoured only when `official.toml` lists the pack's name,
    /// the manifest's version and the lock's content hash, all three at once.
    /// A registry without the file has no audited release, so the claim cannot
    /// be verified and is an error rather than a lower trust level: silently
    /// treating it as community would hide that the manifest asked for more.
    fn check_official(
        &self,
        manifest_path: &Path,
        manifest: &Manifest,
        hash: &str,
    ) -> Result<(), String> {
        let info = &manifest.pack;
        let Some(whitelist) = &self.whitelist else {
            return Err(diag(
                manifest_path,
                &format!(
                    "包 `{}` 声明 trust = \"official\"，但注册表没有官方白名单 `{OFFICIAL_FILE}`",
                    info.name
                ),
            ));
        };
        if !whitelist.covers(&info.name, &info.version, hash) {
            return Err(diag(
                manifest_path,
                &format!(
                    "包 `{}@{}` 声明 trust = \"official\"，但未列入官方白名单，或锁哈希与白名单不一致；\
                     official 只用于本项目审核过的发行版",
                    info.name, info.version
                ),
            ));
        }
        Ok(())
    }

    /// The registry root whose packs this instance describes.
    pub(crate) fn root(&self) -> &Path {
        &self.root
    }

    /// How many packs the registry and its lock agree on.
    pub(crate) fn pack_count(&self) -> usize {
        self.packs.len()
    }

    /// The manifest version of `name`.
    pub(crate) fn version(&self, name: &str) -> Option<&str> {
        self.find(name)
            .map(|pack| pack.manifest.pack.version.as_str())
    }

    /// The manifest trust level of `name`.
    pub(crate) fn trust(&self, name: &str) -> Option<Trust> {
        self.find(name).map(|pack| pack.manifest.pack.trust)
    }

    /// The locked content hash of `name`.
    pub(crate) fn hash(&self, name: &str) -> Option<&str> {
        self.find(name).map(|pack| pack.hash.as_str())
    }
}

/// Recursively load registry packages into one cloned library.
pub(crate) struct PackageLoader<'a> {
    registry: &'a Registry,
    lib: &'a mut Library,
    infos: &'a mut Vec<LoadedPackInfo>,
    /// Packages currently being loaded, outermost first. Used for cycle
    /// detection; a name here is not finished and must not be skipped.
    stack: Vec<String>,
    /// Packages already loaded in this session, including those loaded by the
    /// current `:load`. Re-importing one is a no-op.
    done: BTreeSet<String>,
}

impl<'a> PackageLoader<'a> {
    pub(crate) fn new(
        registry: &'a Registry,
        lib: &'a mut Library,
        infos: &'a mut Vec<LoadedPackInfo>,
    ) -> Self {
        let done = infos.iter().map(|info| info.name.clone()).collect();
        PackageLoader {
            registry,
            lib,
            infos,
            stack: Vec::new(),
            done,
        }
    }

    /// Load every package named by `imports`, in order.
    pub(crate) fn load_imports(
        &mut self,
        imports: &[String],
        importer: &Path,
    ) -> Result<(), String> {
        for name in imports {
            self.load_package(name, importer)?;
        }
        Ok(())
    }

    fn load_package(&mut self, name: &str, importer: &Path) -> Result<(), String> {
        if let Some(start) = self.stack.iter().position(|entry| entry == name) {
            let mut cycle = self.stack[start..].to_vec();
            cycle.push(name.to_owned());
            return Err(diag(
                importer,
                &format!("包依赖成环：{}", cycle.join(" → ")),
            ));
        }
        if self.done.contains(name) {
            return self.check_loaded_pack(name, importer);
        }

        // Copy what we need out of the registry borrow before recursively
        // loading dependencies: those calls need `&mut self`.
        let (dir, manifest, hash) = {
            let package = self.registry.find(name).ok_or_else(|| {
                diag(
                    importer,
                    &format!(
                        "注册表 `{}` 中没有包 `{name}`",
                        self.registry.root.display()
                    ),
                )
            })?;
            (
                package.dir.clone(),
                package.manifest.clone(),
                package.hash.clone(),
            )
        };
        let manifest_path = dir.join(MANIFEST_FILE);
        // An `official` claim is a statement about this project's audit, not
        // about the manifest author's self-assessment: it is honoured only for
        // a release the whitelist lists and the lock hash confirms. This gate
        // runs for every import, explicit or profile-driven, and the
        // `--allow-community-packs` option does not touch it: that flag lowers
        // the profile's trust requirement, it never accepts an unverified
        // `official` claim.
        if manifest.pack.trust == Trust::Official {
            self.registry
                .check_official(&manifest_path, &manifest, &hash)?;
        }
        let namespace = manifest.pack.namespace.clone().ok_or_else(|| {
            diag(
                &manifest_path,
                &format!("包 `{name}` 没有声明 namespace，不能导入"),
            )
        })?;

        // `import` names a package, but `Library::load` checks that the
        // imported name is a loaded *namespace*. A package whose name and
        // namespace differ can therefore never be imported; say so here,
        // instead of failing later with a misleading "not loaded" error.
        if namespace != name {
            return Err(diag(
                &manifest_path,
                &format!(
                    "包 `{name}` 的 namespace 是 `{namespace}`；import 名必须等于包声明的 namespace"
                ),
            ));
        }

        // Two different packs may not claim one namespace: that would silently
        // merge two theories in the flat ledger.
        if let Some(info) = self
            .infos
            .iter()
            .find(|info| info.name != name && info.namespace == namespace)
        {
            return Err(diag(
                &manifest_path,
                &format!(
                    "包 `{name}` 的 namespace `{namespace}` 与已加载包 `{}` 重复；两个包不能声明同一个 namespace",
                    info.name
                ),
            ));
        }
        for other in &self.stack {
            if let Some(other_pack) = self.registry.find(other) {
                if other_pack.manifest.pack.namespace.as_deref() == Some(namespace.as_str()) {
                    return Err(diag(
                        &manifest_path,
                        &format!(
                            "包 `{name}` 的 namespace `{namespace}` 与正在加载的包 `{other}` 重复"
                        ),
                    ));
                }
            }
        }

        let theory_files = self.collect_theory_files(name, &dir, &manifest, &manifest_path)?;
        // The manifest's scope is the pack default every rule inherits field
        // by field when it does not write that field itself.
        let pack_scope = Scope {
            effective_from: manifest.pack.effective_from.clone(),
            effective_to: manifest.pack.effective_to.clone(),
            jurisdiction: Some(manifest.pack.jurisdiction.clone()),
            territory: Some(manifest.pack.territory.clone()),
            origin: ScopeOrigin::PackDefault,
            ..Scope::default()
        };
        self.stack.push(name.to_owned());
        let loaded = self.load_theory_files(name, &namespace, &theory_files, &pack_scope);
        self.stack.pop();
        let decls = loaded?;

        self.infos.push(LoadedPackInfo {
            name: name.to_owned(),
            version: manifest.pack.version.clone(),
            trust: manifest.pack.trust,
            hash,
            namespace,
            corpus: manifest.pack.corpus.clone(),
            decls,
        });
        self.done.insert(name.to_owned());
        Ok(())
    }

    /// Validate and read the manifest's `kind = "theory"` entries.
    ///
    /// Only theory entries are opened. Every path must be relative, may not
    /// contain `..`, must be unique within the pack, and must resolve to a
    /// regular file that is not a symbolic link and is valid UTF-8. A pack
    /// without at least one theory file cannot be imported.
    fn collect_theory_files(
        &self,
        name: &str,
        dir: &Path,
        manifest: &Manifest,
        manifest_path: &Path,
    ) -> Result<Vec<TheoryFile>, String> {
        let mut theory_files = Vec::new();
        let mut seen: BTreeSet<String> = BTreeSet::new();
        for (index, file) in manifest.files.iter().enumerate() {
            if file.kind.as_deref() != Some("theory") {
                continue;
            }
            let raw = file.path.as_deref().ok_or_else(|| {
                diag(
                    manifest_path,
                    &format!("包 `{name}` 的第 {} 个 theory 文件条目缺少 path", index + 1),
                )
            })?;
            let relative = validate_theory_path(raw).map_err(|message| {
                diag(
                    manifest_path,
                    &format!("包 `{name}` 的 theory 文件 `{raw}`：{message}"),
                )
            })?;
            if !seen.insert(relative.clone()) {
                return Err(diag(
                    manifest_path,
                    &format!("包 `{name}` 的 theory 文件路径 `{raw}` 重复"),
                ));
            }
            let path = dir.join(&relative);
            let metadata = fs::symlink_metadata(&path).map_err(|error| {
                diag(
                    &path,
                    &format!("无法读取包 `{name}` 的 theory 文件：{error}"),
                )
            })?;
            if metadata.file_type().is_symlink() {
                return Err(diag(
                    &path,
                    &format!("包 `{name}` 的 theory 文件不能是符号链接"),
                ));
            }
            if !metadata.is_file() {
                return Err(diag(
                    &path,
                    &format!("包 `{name}` 的 theory 文件不是普通文件"),
                ));
            }
            let bytes = fs::read(&path).map_err(|error| {
                diag(
                    &path,
                    &format!("无法读取包 `{name}` 的 theory 文件：{error}"),
                )
            })?;
            let src = String::from_utf8(bytes).map_err(|_| {
                diag(
                    &path,
                    &format!("包 `{name}` 的 theory 文件不是有效的 UTF-8"),
                )
            })?;
            theory_files.push(TheoryFile {
                relative,
                path,
                src,
            });
        }
        if theory_files.is_empty() {
            return Err(diag(
                manifest_path,
                &format!("包 `{name}` 没有可导入的 theory 文件"),
            ));
        }
        Ok(theory_files)
    }

    /// Load one package's theory files in manifest order.
    ///
    /// Each file's imports are resolved recursively before the file itself is
    /// given to [`Library::load`], so a dependency is always loaded first. A
    /// package theory file must declare exactly the manifest's namespace.
    ///
    /// Returns the ledger names the pack added, across all its theory files.
    /// They are collected from the environment diff around each load rather
    /// than from a theory's declaration list: the ledger is flat, so a file
    /// loaded earlier can share the namespace, and only the names this pack
    /// really inserted may be attributed to it by `:inspect`.
    fn load_theory_files(
        &mut self,
        name: &str,
        namespace: &str,
        files: &[TheoryFile],
        pack_scope: &Scope,
    ) -> Result<BTreeSet<String>, String> {
        let mut decls = BTreeSet::new();
        for file in files {
            let path = file.path.to_string_lossy().into_owned();
            let items = std_deduce_lang::parser::parse(&file.src)
                .map_err(|error| LoadError::at(error.msg, error.line, error.col).render(&path))?;
            let file_namespace = items.iter().find_map(|item| match item {
                Item::Import(_) => None,
                Item::Namespace(namespace) => Some(namespace.as_str()),
                _ => None,
            });
            if file_namespace != Some(namespace) {
                let actual = file_namespace
                    .map(|namespace| format!("`{namespace}`"))
                    .unwrap_or_else(|| "无 namespace".to_owned());
                return Err(diag(
                    &file.path,
                    &format!(
                        "theory 文件 `{}` 的 namespace {actual} 与包 `{name}` 的清单 namespace `{namespace}` 不一致",
                        file.relative
                    ),
                ));
            }
            let imports = imports_of(&items);
            self.load_imports(&imports, &file.path)?;
            let before: BTreeSet<String> = self
                .lib
                .env
                .iter()
                .map(|decl| decl.name.to_string())
                .collect();
            // A pack rule inherits the manifest's scope field by field unless
            // it writes the field itself. The values are metadata only; the
            // reasoner never filters on them here.
            let options = LoadOptions {
                pack_scope: Some(pack_scope.clone()),
                case_local: false,
            };
            self.lib
                .load_with_options(&path, &file.src, &options)
                .map_err(|error| error.render(&path))?;
            for decl in self.lib.env.iter() {
                let name = decl.name.to_string();
                if !before.contains(&name) {
                    decls.insert(name);
                }
            }
        }
        Ok(decls)
    }

    /// Re-check a package loaded earlier in this session against the registry.
    ///
    /// The session's ledger cannot be unloaded, so a changed version, hash or
    /// namespace is reported instead of silently keeping stale declarations.
    fn check_loaded_pack(&self, name: &str, importer: &Path) -> Result<(), String> {
        let info = self
            .infos
            .iter()
            .find(|info| info.name == name)
            .ok_or_else(|| {
                diag(
                    importer,
                    &format!("包 `{name}` 已标记为加载，但会话中没有包记录"),
                )
            })?;
        let Some(package) = self.registry.find(name) else {
            return Err(diag(
                importer,
                &format!(
                    "注册表 `{}` 中没有已加载包 `{name}`",
                    self.registry.root.display()
                ),
            ));
        };
        let namespace = package
            .manifest
            .pack
            .namespace
            .as_deref()
            .unwrap_or_default();
        if info.version != package.manifest.pack.version
            || info.hash != package.hash
            || info.namespace != namespace
        {
            return Err(diag(
                &package.dir.join(MANIFEST_FILE),
                &format!(
                    "包 `{name}` 已在会话中加载（版本 {}，哈希 {}，namespace `{}`），\
                     与当前注册表（版本 {}，哈希 {}，namespace `{}`）不一致；请重新启动会话",
                    info.version,
                    info.hash,
                    info.namespace,
                    package.manifest.pack.version,
                    package.hash,
                    namespace
                ),
            ));
        }
        Ok(())
    }
}

/// One already-read theory file of a package.
struct TheoryFile {
    /// The manifest path normalized to `/`-separated components, for errors.
    relative: String,
    path: PathBuf,
    src: String,
}

/// The `import` items of a parsed file, in first-appearance order, deduplicated.
pub(crate) fn imports_of(items: &[Item]) -> Vec<String> {
    let mut imports = Vec::new();
    for item in items {
        if let Item::Import(name) = item {
            if !imports.contains(name) {
                imports.push(name.clone());
            }
        }
    }
    imports
}

/// Validate one `[[files]]` path and return its normalized `/`-separated form.
///
/// The path must be relative, may not contain `..` (or a root/prefix
/// component), and must end at a normal component. `.` components are allowed
/// because they stay inside the pack and are collapsed in the returned form,
/// which is also what duplicate detection compares.
fn validate_theory_path(raw: &str) -> Result<String, String> {
    if raw.is_empty() {
        return Err("path 不能为空".to_owned());
    }
    let path = Path::new(raw);
    if path.is_absolute() {
        return Err("path 必须是相对路径".to_owned());
    }
    let mut parts: Vec<&str> = Vec::new();
    for component in path.components() {
        match component {
            Component::Normal(part) => {
                let part = part
                    .to_str()
                    .ok_or_else(|| "path 不是有效的 UTF-8".to_owned())?;
                // On Windows `theory.std:hidden` names an alternate data stream
                // of `theory.std`: directory scans and the lock hash never see
                // it, but `fs::read` would open it. Reject the colon on every
                // platform instead of relying on the platform path parser.
                if part.contains(':') {
                    return Err("path 不能包含 `:`（Windows 备用数据流）".to_owned());
                }
                parts.push(part);
            }
            Component::CurDir => {}
            Component::ParentDir => return Err("path 不能包含 `..`".to_owned()),
            Component::RootDir | Component::Prefix(_) => {
                return Err("path 必须是相对路径".to_owned());
            }
        }
    }
    if parts.is_empty() {
        return Err("path 没有文件名".to_owned());
    }
    Ok(parts.join("/"))
}

/// Render a `lawpack` error as a P0c-style diagnostic.
pub(crate) fn render_pack_error(error: &PackError) -> String {
    diag(error.path(), error.message())
}

/// Render one diagnostic as `path: error: message`, escaping both parts.
fn diag(path: &Path, message: &str) -> String {
    let path = path.to_string_lossy();
    format!("{}: error: {}", escape_path(&path), escape_path(message))
}
