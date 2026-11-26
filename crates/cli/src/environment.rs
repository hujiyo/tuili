//! The default legal environment.
//!
//! A registry may declare an environment profile under `lawpacks/profiles`.
//! In the default automatic mode the first theory load prepares that
//! environment once: the profile is scanned, its packs are checked against the
//! registry lock, version constraints and trust level, and the packages are
//! loaded into the session before the file itself. `--profile <name>` selects a
//! profile explicitly, `--no-default-packs` disables the environment (explicit
//! `import` still works), and `--allow-community-packs` lowers the trust gate
//! for a profile. The flag only lowers that gate: an `official` claim is still
//! checked against the registry's official whitelist by the package loader.
//!
//! Preparation is lazy: `:packs`, `:lock`, `:inspect` and a REPL that never
//! loads a file do not touch it. The whole preparation runs on the caller's
//! cloned [`Library`] and package list, so a profile, lock, version, trust or
//! package error leaves the session untouched. Its preload report is returned
//! to the caller and printed only after the whole load commits, so a file that
//! fails afterwards never claims the environment loaded.
//!
//! The selected profile is a session object: [`Environment::profile_name`]
//! exposes its canonical name for the certificate's environment identity, and
//! no profile (`--no-default-packs`, no default profile, no registry) is
//! recorded as an explicit `null`, never as a missing field.
//!
//! `--as-of <YYYY-MM-DD>` and `--jurisdiction <code>` are session options too:
//! they are validated when the arguments are parsed, stored here, and stamped
//! into the certificate's environment identity by `:cert`. The `:asof` /
//! `:jurisdiction` commands replace the same session values. They never affect
//! which packs load or how the reasoner derives; `:verify-cert` compares them
//! exactly, so a certificate is checked against the same values. A session
//! without a jurisdiction choice refuses `:why` / `:cert` when the loaded
//! rules name two or more jurisdictions; that gate is in the CLI, not here.
//!
//! `--closed-env` is the closed-environment mode: a top-level `:load` may only
//! load a *case* file, and the case may only use the declarations and rules its
//! imported packs provide. `--allow-case-rules` lifts that declaration check and
//! lets the case declare its own sorts, predicates, definitions, rules,
//! contraries and uniques; those declarations are recorded as case extensions
//! and a certificate that applies a case rule records an open obligation. The
//! option is only valid together with `--closed-env`; without the closed mode a
//! case file may declare what it needs, so the flag would have no meaning.

use std::collections::BTreeSet;
use std::fmt::Write as _;
use std::io::Write;
use std::path::{Path, PathBuf};

use std_deduce_kernel::env::escape_control;
use std_deduce_lang::module::escape_path;
use std_deduce_lang::Library;
use std_deduce_lawpack::profile::{
    scan_profiles, select_default, select_named, version_matches, Profile,
};
use std_deduce_lawpack::Trust;

use crate::packs::{render_pack_error, LoadedPackInfo, PackageLoader, Registry};

/// Invocation options that affect the default environment, the closed
/// environment and the certificate's environment identity.
#[derive(Debug, Clone, Default)]
pub(crate) struct Options {
    pub(crate) profile: Option<String>,
    pub(crate) no_default_packs: bool,
    pub(crate) allow_community_packs: bool,
    /// Closed-environment mode: case files may not declare legal concepts.
    pub(crate) closed_env: bool,
    /// Allow case-local declarations in the closed environment.
    pub(crate) allow_case_rules: bool,
    pub(crate) as_of: Option<String>,
    pub(crate) jurisdiction: Option<String>,
    /// Interpretations enabled for every query in this session, in command
    /// line order. They are resolved against the loaded environment; a
    /// default (empty) session keeps every interpretation inert.
    pub(crate) interpretations: Vec<String>,
    /// Display-layer redaction: replace individual names in printed output with
    /// stable placeholders. It is a session flag carried on the same struct
    /// because the option is parsed in the same prefix; it never affects which
    /// packs load, the environment identity or a certificate's content.
    pub(crate) redact: bool,
}

/// An enabled environment: the profile that selected it, where the registry
/// lives, every pack it loaded (direct packs and the dependency closure), and
/// whether the trust gate was lowered.
#[derive(Debug, Clone)]
struct Active {
    profile: Profile,
    registry_root: PathBuf,
    pack_names: BTreeSet<String>,
    allow_community_packs: bool,
}

/// How far the environment preparation has got.
#[derive(Debug, Clone, Default)]
enum State {
    #[default]
    Uninitialized,
    Closed,
    Disabled,
    Enabled(Active),
}

/// Session-level environment preparation.
#[derive(Debug, Clone)]
pub(crate) struct Environment {
    options: Options,
    state: State,
}

impl Environment {
    pub(crate) fn new(options: Options) -> Self {
        let state = if options.no_default_packs {
            State::Closed
        } else {
            State::Uninitialized
        };
        Environment { options, state }
    }

    /// Prepare the default environment before the first theory load.
    ///
    /// Auto mode does nothing unless the current directory has a `lawpacks/`
    /// directory with a `default = true` profile; a missing registry, a missing
    /// `profiles/` directory or no default profile is not an error. Once a
    /// default profile exists every error is fatal for this load: a bad
    /// profile, a bad lock, a missing pack, a version mismatch and insufficient
    /// trust all fail. Explicit `--profile` requires the registry and the
    /// profile. The already-selected state is reused on later loads.
    ///
    /// The returned preload report is not printed here: the caller prints it
    /// only after the whole load commits, so a file that fails after a
    /// successful environment preparation never claims the environment loaded.
    pub(crate) fn ensure_loaded(
        &mut self,
        lib: &mut Library,
        packs: &mut Vec<LoadedPackInfo>,
    ) -> Result<Option<String>, String> {
        if !matches!(self.state, State::Uninitialized) {
            return Ok(None);
        }
        let cwd = current_dir()?;
        let root = cwd.join("lawpacks");
        if !root.is_dir() {
            if let Some(query) = &self.options.profile {
                return Err(format!(
                    "注册表 `{}` 不存在或不是目录：--profile `{}` 需要当前目录下的 lawpacks",
                    escape_path(&root.display().to_string()),
                    escape_path(query)
                ));
            }
            self.state = State::Disabled;
            return Ok(None);
        }

        let profiles = scan_profiles(&root).map_err(render_profile_errors)?;
        let profile = match &self.options.profile {
            Some(query) => select_named(&profiles, query)
                .map_err(|error| escape_path(&error))?
                .clone(),
            None => match select_default(&profiles).map_err(|error| escape_path(&error))? {
                Some(profile) => profile.clone(),
                None => {
                    self.state = State::Disabled;
                    return Ok(None);
                }
            },
        };

        let registry = Registry::open_at(root).map_err(|errors| errors.join("\n"))?;
        let (active, start) = load_profile(
            &registry,
            &profile,
            self.options.allow_community_packs,
            lib,
            packs,
        )?;
        let report = preload_report(&active, &packs[start..])?;
        self.state = State::Enabled(active);
        Ok(Some(report))
    }

    /// Append the `--no-default-packs` hint to a failed file load, when useful.
    ///
    /// The hint only diagnoses a closed environment; it never changes an exit
    /// code. `imports` are the file's own import list: a pack the file already
    /// imports is not a missing environment pack, so an unknown name under it
    /// is the file's own problem and gets no hint. The owning pack is looked up
    /// in the current registry (every manifest's name and namespace, longest
    /// prefix), so a dependency of the profile is named too. Reading the
    /// registry here is explicitly best-effort: if it cannot be scanned, no
    /// hint is added and the original error is returned unchanged.
    pub(crate) fn annotate_error(&self, error: String, imports: &[String]) -> String {
        if !matches!(self.state, State::Closed) {
            return error;
        }
        let Some(name) = unknown_name(&error) else {
            return error;
        };
        let Some(pack) = self.pack_for_name(name) else {
            return error;
        };
        if imports.contains(&pack) {
            return error;
        }
        format!(
            "{error}\n提示：`{}` 可能来自法律包 `{}`；--no-default-packs 已关闭默认环境，\
             请写 `import {}` 或去掉 --no-default-packs。",
            escape_path(name),
            escape_path(&pack),
            escape_path(&pack)
        )
    }

    /// The canonical name of the active profile, or `None` when no profile is
    /// active (closed, disabled or not yet prepared).
    ///
    /// An alias selects the profile it names, so the returned name is always
    /// [`Profile::name`], the identity the certificate records.
    pub(crate) fn profile_name(&self) -> Option<&str> {
        match &self.state {
            State::Enabled(active) => Some(active.profile.name.as_str()),
            State::Closed | State::Disabled | State::Uninitialized => None,
        }
    }

    /// The `--as-of` / `:asof` value the session records, if any.
    ///
    /// It is an identity field only: it does not gate preparation and is not
    /// read by the reasoner.
    pub(crate) fn as_of(&self) -> Option<&str> {
        self.options.as_of.as_deref()
    }

    /// Replace the session's legal as-of date after `:asof` validated it.
    pub(crate) fn set_as_of(&mut self, value: String) {
        self.options.as_of = Some(value);
    }

    /// The `--jurisdiction` / `:jurisdiction` value the session records, if
    /// any.
    ///
    /// It is an identity field and the multi-jurisdiction gate's answer: it
    /// does not gate preparation and is not read by the reasoner.
    pub(crate) fn jurisdiction(&self) -> Option<&str> {
        self.options.jurisdiction.as_deref()
    }

    /// Replace the session's jurisdiction code after `:jurisdiction`
    /// validated it.
    pub(crate) fn set_jurisdiction(&mut self, value: String) {
        self.options.jurisdiction = Some(value);
    }

    /// The `（环境外：...）` suffix for an explicit import.
    ///
    /// A pack the environment loaded (directly or as a dependency) is inside
    /// the environment and keeps the plain report line. A pack loaded by an
    /// explicit import without being in the closure is marked with its trust
    /// level; an import satisfied by a module loaded directly from a file is
    /// not a registry pack and carries no marker.
    pub(crate) fn import_marker(&self, name: &str, packs: &[LoadedPackInfo]) -> Option<String> {
        let State::Enabled(active) = &self.state else {
            return None;
        };
        if active.pack_names.contains(name) {
            return None;
        }
        let pack = packs.iter().find(|pack| pack.name == name)?;
        Some(format!("（环境外：{}）", pack.trust))
    }

    /// Whether the closed-environment mode is on.
    ///
    /// The mode is a pure invocation switch: it does not depend on the
    /// registry or the profile, and it applies to every top-level `:load` of
    /// the session, not only to the first one.
    pub(crate) fn closed_env(&self) -> bool {
        self.options.closed_env
    }

    /// Whether the closed environment allows case-local declarations.
    ///
    /// The parser rejects `--allow-case-rules` without `--closed-env`, so this
    /// is only ever true together with [`Environment::closed_env`].
    pub(crate) fn allow_case_rules(&self) -> bool {
        self.options.allow_case_rules
    }

    /// Append the closed-environment hint to a failed file load, when useful.
    ///
    /// The closed environment never invents a legal concept for a case file: a
    /// name the loaded packs do not define is reported with a hint to load the
    /// pack that covers it, or to allow case-local rules. The hint only
    /// diagnoses; it never changes the exit code, and a failure without an
    /// `未知名称` marker gets no hint.
    pub(crate) fn annotate_closed_error(&self, error: String) -> String {
        if !self.options.closed_env {
            return error;
        }
        let Some(name) = unknown_name(&error) else {
            return error;
        };
        let name = escape_control(name);
        if self.options.allow_case_rules {
            format!(
                "{error}\n提示：已加载的法律包中没有 `{name}`；封闭环境不会为案件补造法律概念，\
                 请加载覆盖它的法律包或检查名称拼写。"
            )
        } else {
            format!(
                "{error}\n提示：封闭环境不会为案件补造法律概念；已加载的法律包中没有 `{name}`。\
                 请加载覆盖它的法律包，或加 --allow-case-rules 使用案件本地扩展（证书会标记）。"
            )
        }
    }

    /// The registry pack whose name owns `name`, if it can be imported.
    ///
    /// This is a diagnostic helper for the closed mode: it scans the current
    /// directory's registry and matches the longest importable pack-name
    /// prefix, so a dependency pack of the default profile is found too. Only a
    /// pack whose `namespace` equals its name can be imported, and only such a
    /// pack is suggested: a missing namespace, a different namespace and a
    /// longer unimportable namespace are skipped. It gives up silently when the
    /// registry is unavailable; it is not a load path.
    fn pack_for_name(&self, name: &str) -> Option<String> {
        let cwd = std::env::current_dir().ok()?;
        let found = std_deduce_lawpack::scan(&cwd.join("lawpacks")).ok()?;
        let mut best: Option<String> = None;
        for pack in &found.packs {
            let info = &pack.manifest.pack;
            if info.namespace.as_deref() != Some(info.name.as_str()) {
                continue;
            }
            if !name.starts_with(&format!("{}.", info.name)) {
                continue;
            }
            if best
                .as_ref()
                .is_none_or(|current| info.name.len() > current.len())
            {
                best = Some(info.name.clone());
            }
        }
        best
    }
}

/// `std-deduce env`: report and load the environment without a theory file.
///
/// The registry must exist and its lock is always verified. Auto mode reports
/// an unused default profile as success; `--no-default-packs` skips profile
/// parsing; an explicit profile must exist. A profile that is selected is
/// really loaded, so a bad theory file in one of its packs is an environment
/// error too.
pub(crate) fn run_env(options: &Options, out: &mut impl Write) -> Result<(), String> {
    let cwd = current_dir()?;
    let root = cwd.join("lawpacks");
    if !root.is_dir() {
        return Err(format!(
            "当前目录没有 lawpacks：期望 {}",
            escape_path(&root.display().to_string())
        ));
    }
    let registry = Registry::open_at(root.clone()).map_err(|errors| errors.join("\n"))?;

    if options.no_default_packs {
        writeln!(out, "环境 profile：未启用（--no-default-packs）").ok();
        writeln!(out, "默认包：未加载").ok();
        print_registry(&root, &registry, out);
        return Ok(());
    }

    let profiles = scan_profiles(&root).map_err(render_profile_errors)?;
    let profile = match &options.profile {
        Some(query) => select_named(&profiles, query)
            .map_err(|error| escape_path(&error))?
            .clone(),
        None => match select_default(&profiles).map_err(|error| escape_path(&error))? {
            Some(profile) => profile.clone(),
            None => {
                writeln!(
                    out,
                    "环境 profile：未启用（没有 default = true 的 profile）"
                )
                .ok();
                writeln!(out, "默认包：未加载").ok();
                print_registry(&root, &registry, out);
                return Ok(());
            }
        },
    };

    let mut lib = Library::new();
    let mut infos = Vec::new();
    let (active, start) = load_profile(
        &registry,
        &profile,
        options.allow_community_packs,
        &mut lib,
        &mut infos,
    )?;
    // The profile's packs are the whole load transaction here: check the
    // `revision` groups once, after all of them are in (a pack may split one
    // provision's versions across theory files).
    lib.check_revision_groups()
        .map_err(|error| error.to_string())?;
    print_env_profile(&registry, &active, &infos[start..], out)
}

/// Validate a profile against the registry and load its packs into `lib`.
///
/// Direct packs must exist, satisfy their version constraints and reach the
/// profile's trust level; dependencies are loaded recursively and the whole
/// closure must reach it as well. Trust is only lowered by
/// `--allow-community-packs`. Returns the active environment and the index in
/// `packs` where the newly loaded packs start.
fn load_profile(
    registry: &Registry,
    profile: &Profile,
    allow_community_packs: bool,
    lib: &mut Library,
    packs: &mut Vec<LoadedPackInfo>,
) -> Result<(Active, usize), String> {
    for entry in &profile.packs {
        let Some(version) = registry.version(&entry.name) else {
            return Err(format!(
                "profile `{}` 引用的包 `{}` 不在注册表 `{}` 中",
                profile.name,
                entry.name,
                escape_path(&registry.root().display().to_string())
            ));
        };
        if !version_matches(&entry.version, version) {
            return Err(format!(
                "profile `{}`：包 `{}` 的清单版本 `{}` 不满足约束 `{}`",
                profile.name, entry.name, version, entry.version
            ));
        }
        if !allow_community_packs {
            let trust = registry
                .trust(&entry.name)
                .ok_or_else(|| format!("内部错误：注册表中包 `{}` 没有清单信任级别", entry.name))?;
            ensure_trust(profile, &entry.name, trust)?;
        }
    }

    let start = packs.len();
    let names: Vec<String> = profile
        .packs
        .iter()
        .map(|entry| entry.name.clone())
        .collect();
    {
        let mut loader = PackageLoader::new(registry, lib, packs);
        loader.load_imports(&names, registry.root())?;
    }

    // Dependencies are only known after loading. They are part of the
    // environment closure, so the trust gate applies to them too.
    if !allow_community_packs {
        for info in &packs[start..] {
            ensure_trust(profile, &info.name, info.trust)?;
        }
    }

    let mut pack_names: BTreeSet<String> = profile
        .packs
        .iter()
        .map(|entry| entry.name.clone())
        .collect();
    pack_names.extend(packs[start..].iter().map(|info| info.name.clone()));
    Ok((
        Active {
            profile: profile.clone(),
            registry_root: registry.root().to_path_buf(),
            pack_names,
            allow_community_packs,
        },
        start,
    ))
}

/// Reject a pack whose trust level is below what the profile requires.
fn ensure_trust(profile: &Profile, pack: &str, actual: Trust) -> Result<(), String> {
    if actual >= profile.trust {
        return Ok(());
    }
    Err(format!(
        "profile `{}` 要求信任级别至少 `{}`，但包 `{}` 的信任级别是 `{}`；\
         如需允许非官方包，请加 --allow-community-packs",
        profile.name, profile.trust, pack, actual
    ))
}

/// Build the preload lines printed before the theory's own load report.
fn preload_report(active: &Active, infos: &[LoadedPackInfo]) -> Result<String, String> {
    let allowed_non_official =
        active.allow_community_packs && infos.iter().any(|info| info.trust < Trust::Official);
    let mut report = String::new();
    writeln!(
        report,
        "默认环境 {}：已加载 {} 个包{}",
        active.profile.name,
        infos.len(),
        if allowed_non_official {
            "（已允许非官方包）"
        } else {
            ""
        }
    )
    .expect("写入 String 不会失败");

    let direct: BTreeSet<&str> = active
        .profile
        .packs
        .iter()
        .map(|entry| entry.name.as_str())
        .collect();
    for entry in &active.profile.packs {
        let info = infos
            .iter()
            .find(|info| info.name == entry.name)
            .ok_or_else(|| format!("内部错误：默认环境包 `{}` 没有加载记录", entry.name))?;
        writeln!(report, "  {}@{}（{}）", info.name, info.version, info.trust)
            .expect("写入 String 不会失败");
    }
    for info in infos {
        if direct.contains(info.name.as_str()) {
            continue;
        }
        writeln!(
            report,
            "  {}@{}（{}，依赖）",
            info.name, info.version, info.trust
        )
        .expect("写入 String 不会失败");
    }
    Ok(report)
}

/// Print the success report of `std env`.
fn print_env_profile(
    registry: &Registry,
    active: &Active,
    infos: &[LoadedPackInfo],
    out: &mut impl Write,
) -> Result<(), String> {
    let description = active
        .profile
        .description
        .as_deref()
        .filter(|text| !text.trim().is_empty())
        .map(|text| format!("（{}）", escape_path(text)))
        .unwrap_or_default();
    writeln!(out, "环境 profile：{}{}", active.profile.name, description).ok();
    writeln!(out, "  信任要求：{}", active.profile.trust).ok();

    let direct: BTreeSet<&str> = active
        .profile
        .packs
        .iter()
        .map(|entry| entry.name.as_str())
        .collect();
    for entry in &active.profile.packs {
        let info = infos
            .iter()
            .find(|info| info.name == entry.name)
            .ok_or_else(|| format!("内部错误：环境包 `{}` 没有加载记录", entry.name))?;
        let hash = registry
            .hash(&entry.name)
            .ok_or_else(|| format!("内部错误：注册表没有包 `{}` 的锁哈希", entry.name))?;
        writeln!(
            out,
            "  {} {} → {}（{}，锁 {}）",
            entry.name, entry.version, info.version, info.trust, hash
        )
        .ok();
    }
    for info in infos {
        if direct.contains(info.name.as_str()) {
            continue;
        }
        writeln!(
            out,
            "  {} → {}（{}，依赖）",
            info.name, info.version, info.trust
        )
        .ok();
    }

    print_registry(&active.registry_root, registry, out);
    writeln!(out, "环境加载：通过（{} 个包）", infos.len()).ok();
    Ok(())
}

/// Print the registry path and the lock verification result.
fn print_registry(root: &Path, registry: &Registry, out: &mut impl Write) {
    writeln!(out, "注册表：{}", escape_path(&root.display().to_string())).ok();
    writeln!(out, "锁定校验：通过（{} 个包）", registry.pack_count()).ok();
}

/// Render every profile scan error as one diagnostic per line.
fn render_profile_errors(errors: Vec<std_deduce_lawpack::PackError>) -> String {
    errors
        .iter()
        .map(render_pack_error)
        .collect::<Vec<_>>()
        .join("\n")
}

fn current_dir() -> Result<PathBuf, String> {
    std::env::current_dir()
        .map_err(|error| format!("无法取得当前目录：{}", escape_path(&error.to_string())))
}

/// The name an elaboration error reports as unknown, if any.
pub(crate) fn unknown_name(error: &str) -> Option<&str> {
    let marker = "未知名称 `";
    let start = error.find(marker)? + marker.len();
    let rest = &error[start..];
    let end = rest.find('`')?;
    Some(&rest[..end])
}
