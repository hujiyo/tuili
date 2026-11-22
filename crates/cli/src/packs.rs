//! Registry-backed package imports for `:load` and the batch entry point.
//!
//! This module is deliberately internal to the CLI: the language layer only
//! knows that an imported namespace is already loaded, while the registry
//! decides where a package comes from, which files belong to it, and whether
//! the directory still matches `std.lock`.
//!
//! A `:load` first parses the file to find its `import` items. A file without
//! any import never touches the registry. A file with imports scans
//! `lawpacks` in the current directory and verifies the lock once for the whole
//! load; packages are then loaded depth-first, dependencies before the package
//! that imports them.
//!
//! The whole load runs on a cloned [`Library`] and a cloned package list. An
//! error at any step therefore leaves the session exactly as it was: no
//! declarations from a package and no package information survive a failed
//! load.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fs;
use std::path::{Component, Path, PathBuf};

use std_deduce_lang::ast::Item;
use std_deduce_lang::module::escape_path;
use std_deduce_lang::{Library, LoadError};
use std_deduce_lawpack::{
    scan, verify_lock, LoadedPack, Lockfile, Manifest, PackError, LOCK_FILE, MANIFEST_FILE,
};

/// A pack successfully loaded into the current session.
///
/// `:inspect` uses the namespace to find the pack and prints
/// `[name@version]`; the hash is kept so a later import can tell whether the
/// registry still describes the same content the session loaded.
#[derive(Debug, Clone)]
pub(crate) struct LoadedPackInfo {
    pub(crate) name: String,
    pub(crate) version: String,
    pub(crate) hash: String,
    pub(crate) namespace: String,
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

    fn open_at(root: PathBuf) -> Result<Registry, Vec<String>> {
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
        // reports every mismatch it finds instead of stopping at the first.
        if let Err(lock_errors) = verify_lock(&root) {
            return Err(lock_errors.iter().map(render_pack_error).collect());
        }

        let lock_path = root.join(LOCK_FILE);
        let lockfile =
            Lockfile::read(&lock_path).map_err(|error| vec![render_pack_error(&error)])?;
        let mut hashes: BTreeMap<String, String> = lockfile
            .pack
            .into_iter()
            .map(|entry| (entry.name, entry.hash))
            .collect();

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
        Ok(Registry { root, packs })
    }

    fn find(&self, name: &str) -> Option<&RegistryPack> {
        self.packs.get(name)
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
        self.stack.push(name.to_owned());
        let loaded = self.load_theory_files(name, &namespace, &theory_files);
        self.stack.pop();
        loaded?;

        self.infos.push(LoadedPackInfo {
            name: name.to_owned(),
            version: manifest.pack.version.clone(),
            hash,
            namespace,
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
    fn load_theory_files(
        &mut self,
        name: &str,
        namespace: &str,
        files: &[TheoryFile],
    ) -> Result<(), String> {
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
            self.lib
                .load(&path, &file.src)
                .map_err(|error| error.render(&path))?;
        }
        Ok(())
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
fn render_pack_error(error: &PackError) -> String {
    diag(error.path(), error.message())
}

/// Render one diagnostic as `path: error: message`, escaping both parts.
fn diag(path: &Path, message: &str) -> String {
    let path = path.to_string_lossy();
    format!("{}: error: {}", escape_path(&path), escape_path(message))
}
