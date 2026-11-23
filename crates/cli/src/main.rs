//! Command-line interface.
//!
//! The binary has a batch entry point and a line-oriented session:
//!
//! ```text
//! std-deduce                       start the REPL
//! std-deduce [options] <file> [commands...]
//!                                  load a theory file, then run the commands
//! std-deduce [options] check <file> [...]
//!                                  the same batch entry as a plain file
//! std-deduce [options] env         report and load the default environment
//! std-deduce [options] repl        start the REPL
//! std-deduce --help | -h           print usage
//! std-deduce --version | -V        print `std-deduce <version>`
//! std-deduce [options] <command> [...]
//!                                  run every argument as a colon command
//! ```
//!
//! Options must come before the file, subcommand or colon command:
//! `--profile <name>` selects a profile from `lawpacks/profiles`,
//! `--no-default-packs` disables the default environment,
//! `--allow-community-packs` lowers the trust gate of the selected profile, and
//! `--as-of <YYYY-MM-DD>` / `--jurisdiction <code>` record the certificate's
//! legal as-of date and jurisdiction code. The last two are identity fields
//! only: they are validated at parse time, stamped into a `:cert` certificate
//! and compared exactly by `:verify-cert`; they never affect preparation or
//! reasoning.
//!
//! When the current directory contains `lawpacks/profiles` with a
//! `default = true` profile, the first theory load prepares that environment
//! lazily: the profile is validated, its packs are checked against the lock,
//! version constraints and trust level, and they are loaded before the file.
//! A failed preparation fails the load. `--no-default-packs` turns this off
//! without affecting explicit imports; `--profile` selects a profile by name or
//! alias. The preload lines are printed only after the whole load commits, so a
//! failed file never claims that the environment loaded. The profile and the
//! packs it loaded are session objects, but a certificate v3 records the
//! environment identity it was produced in: the profile, the as-of date, the
//! jurisdiction code and the loaded packs/corpora. `:cert` stamps it before
//! writing, and `:verify-cert` compares it with the current environment before
//! running the proof layers.
//!
//! A batch load uses the same path as `:load`, so it prints the same report. A
//! file that does not pass its checks prints `path:line:col: error: ...` on
//! stderr when the loader knows a source position, or `path: error: ...`
//! otherwise (refinement and kernel errors carry no position yet), and exits
//! `1`; the remaining commands are not run. A malformed invocation is still a
//! usage error (`2`): an argument that looks like an option (`-…`) where a
//! command or a file is expected is an unknown option, not a comment and not a
//! file. Only the standalone `--help`/`-h`/`--version`/`-V` are options; a file
//! whose name starts with `-` is passed as `./-名字`. Commands are
//! line-oriented:
//!
//! ```text
//! :load <file>            load a theory file (imports resolve loaded namespaces first)
//! :inspect                dump the ledger
//! :why <term>             derive, print the certificate's tree, and check it
//! :gap <term>             explain what is missing for a goal
//! :cert <term>            derive and print the goal's certificate JSON
//! :verify-cert <file> [goal]
//!                         check a certificate, optionally bound to a goal
//! :packs [dir]            list the legal-pack manifests under a directory
//! :lock [dir]             hash the packs and write the std.lock registry lock
//! :audit [dir]            check rule-source quotations against article corpora
//! :given <term>           add an assumption by hand
//! :quit
//! ```
//!
//! A `:load` file may begin with `import <pack>` items. Imports resolve
//! against namespaces already loaded in the session first; only the remaining
//! ones read the registry: `lawpacks` below the current working directory is
//! scanned and its `std.lock` verified once, then each package's
//! `kind = "theory"` files are loaded depth-first, dependencies first. A file
//! without imports, or whose imports are all already loaded from files, never
//! requires `lawpacks` or a lock. The whole load runs on cloned session state,
//! so a registry, lock, package-path, dependency-cycle or package-load error
//! leaves no half-loaded declarations or package information behind. A
//! top-level file may not declare inside a namespace an already loaded pack
//! owns. `:inspect` shows `[name@version]` only for declarations a loaded pack
//! itself contributed, and still `[ns]` for a namespaced module loaded
//! directly from a file.
//!
//! `:packs` reads manifests but imports nothing and does not require a loaded
//! theory. With no argument it scans `lawpacks` in the current working
//! directory; with an argument that whole string is the directory, so a path
//! containing spaces works without further quoting. Only direct child
//! directories containing a regular `lawpack.toml` are packs; symbolic links
//! and pack directories that resolve outside the root are errors. Each valid
//! pack is printed on one line with its effective range and trust level, then
//! an optional indented description and file count. A manifest may link an
//! article corpus as `<law-id>/<version>`; `:packs` reads
//! `<registry-parent>/law/corpus/<law-id>/<version>.json` and prints its
//! coverage counts and named ontology gaps. A missing or invalid linked corpus
//! is printed as a diagnostic and fails the command. An invalid manifest is
//! printed as `path：error` and makes the command fail (exit `2`); valid packs
//! are still printed. Descriptions, paths and errors are escaped first, so a
//! newline or terminal escape sequence cannot forge another line. A root with
//! no packs prints a "not found" line and succeeds.
//!
//! After the listing, `:packs` looks for `std.lock` in the same directory. When
//! it is there, every pack is hashed and checked against the lock: a match
//! prints `锁定校验：通过（N 个包）`, while a missing, changed, extra or
//! differently versioned pack prints every error and makes the command exit
//! `2`. Without a lock the command prints
//! `锁定校验：未找到 std.lock（未锁定）` and keeps the listing's outcome. If
//! the listing itself found manifest errors, lock verification is skipped and
//! reported as `锁定校验：未运行（清单错误）`, so one bad manifest is reported
//! once and the listing's exit code stands.
//!
//! `:lock` hashes every pack in the directory (default `lawpacks`) and writes
//! `<dir>/std.lock`. An unreadable directory or file, a symbolic link inside a
//! pack, or an invalid manifest prints every error and exits `2`; no lock,
//! partial or otherwise, is written in that case. The hash covers every
//! regular file in the pack directory, with `/`-separated relative paths and
//! `\r\n` normalized to `\n`, so the same files hash the same on Windows and
//! Linux. `:lock` does not import rules and does not require a loaded theory.
//!
//! `:audit` checks every quoted `source` on every declaration in the loaded
//! theory against the article corpus under `law/corpus`, or against the
//! directory given as its argument. A quoted source is printed as `✓` when its
//! quotation matches the stored article after removing all Unicode whitespace,
//! as `?` when no corpus matches (unverified), and as `✗` for every other
//! failure: a missing article, a version mismatch, an ambiguous instrument
//! name, changed wording, a wrong article-text hash, an invalid source or a
//! jurisdiction mismatch. A source without a quotation is printed with `·` and
//! does not take part in the audit or affect the exit code, because case facts
//! carry provenance but no article text to check. Only a run with at least one
//! quoted source and every quoted source `✓` exits `0`; zero quoted sources
//! prints "没有可核对的引文" and exits `1`, and an unverified source is never a
//! pass. A missing or empty corpus directory leaves every quoted source
//! unverified (exit `1`), while a corpus with a broken layout or JSON, or a
//! duplicate `(law, version)`, exits `2`. All text from a source, a corpus or a
//! path is escaped before printing, so a newline in a quotation cannot forge
//! another output line. A corpus's `text_sha256` is provenance metadata only
//! and is neither recomputed nor verified. After the summary, each loaded
//! corpus prints its declared `coverage`: counts for formalized, partial,
//! indexed and needs-ontology articles, the formalized and partial article
//! numbers, the named ontology gaps with their counts, the open concepts and
//! the note. The declaration is printed only and is not compared with the
//! loaded theory's rules.
//!
//! `:why` prints the derivation tree rendered from the generated certificate,
//! then runs [`std_deduce_cert::check`] and [`std_deduce_cert::kernel_proof`]
//! on that same certificate. Its three outcomes are:
//!
//! * proved — the tree is printed, both layers accept the certificate, and
//!   the certificate leaves nothing open;
//! * a gap — the certificate is valid but its root is a gap, so the conclusion
//!   is not proved;
//! * a conflict — both derivations are printed and the process exits non-zero.
//!
//! A certificate that fails either layer is an error (exit `2`), never a
//! successful query. A conclusion caught in an unresolved conflict is kept out
//! of the fact base, but it is never dropped silently.
//!
//! `:cert` requires a loaded theory and writes only the certificate JSON to
//! stdout; a gap becomes a `MissingPremise` obligation and an unresolved
//! conflict becomes an `UnresolvedConflict` obligation in that JSON. Before
//! serialization the certificate is stamped with the environment identity:
//! the canonical profile name, the `--as-of` date and `--jurisdiction` code
//! (explicit `null` when the option was not given), every loaded pack's
//! version, lock hash and trust level, and the hash of every corpus file a
//! loaded pack links. An identity error writes no JSON; the argv entry points
//! report it on stderr, while the REPL keeps its convention of reporting
//! command errors on stdout.
//!
//! `:verify-cert` requires a loaded theory and first compares the
//! certificate's recorded environment identity with the current one. A
//! certificate that records nothing cannot be compared, and any difference
//! fails the check before either proof layer runs: the differences are printed
//! one per line, the four proof lines say they did not run, and the process
//! exits `2`. Only an environment match reaches the two layers, in order:
//!
//! 1. [`std_deduce_cert::check`] rebuilds every rule instance and checks the
//!    recorded `unless` conditions and the root's conflict status;
//! 2. [`std_deduce_cert::kernel_proof`] turns the monotone skeleton into
//!    kernel terms and has the kernel check every step.
//!
//! The two layers are printed separately, together with the side conditions
//! and whether a human must decide something. The process exits `0` only when
//! both layers pass, the root is proved and nothing is left open; `1` when
//! both layers pass but the root is a gap, an open obligation remains or a
//! recorded conflict is unresolved; and `2` when the file cannot be read or
//! parsed, or either layer fails. A logical pass with a kernel failure is
//! therefore a `2`, never a `0`.
//!
//! `:verify-cert <file> <goal>` additionally binds the certificate to the goal:
//! after both layers accept the certificate, the proposition proved by its root
//! must be definitionally equal to the elaborated goal. A gap root, a missing
//! root or a different proposition makes the binding fail (exit `2`) and prints
//! `目标绑定：失败（...）`; a match prints `目标绑定：通过（根命题与目标在内核下等价）`
//! and keeps the original `0`/`1` outcome. A file path containing whitespace
//! is written in double quotes before the goal (`:verify-cert "<path>" <goal>`);
//! without quotes, an argument that is exactly an existing file is taken as a
//! path, which preserves the unquoted form for a space-containing file. In all
//! other cases the first whitespace separates the path from the goal. Without a
//! goal, no binding line is printed and the output is unchanged.
//!
//! `:check` is not an alias: it reports that it was renamed to `:verify-cert`
//! and exits `2`.

mod environment;
mod identity;
mod packs;

use std::collections::BTreeSet;
use std::fs;
use std::io::{self, BufRead, Write};
use std::path::{Path, PathBuf};

use std_deduce_lang::ast::Item;

use std_deduce_cert::{
    render, Certificate, CheckReport, EnvironmentDifference, EnvironmentIdentity,
    EnvironmentRecord, Node as CertNode, ObligationKind,
};
use std_deduce_kernel::conv::convertible;
use std_deduce_kernel::env::{escape_control, Ctx, DeclKind, Env, SourceRef};
use std_deduce_kernel::pretty::print_expr;
use std_deduce_kernel::{check, Expr};
use std_deduce_lang::module::escape_path;
use std_deduce_lang::{elab, Library, LoadReport};
use std_deduce_lawpack::corpus::{self, Audit, Citation, Corpus, CoverageStatus};
use std_deduce_lawpack::{PackInfo, LOCK_FILE};
use std_deduce_reason::{
    certificate as reason_certificate, Conflict, Provenance, Reasoner, Resolution, Side,
};

/// How a query ended. Only `Proved` is a success; the other two make the
/// process exit non-zero, the way a failed `check` does.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Outcome {
    Proved,
    Gap,
    Unresolved,
}

impl Outcome {
    /// The process exit code this outcome stands for. Only `Proved` is `0`;
    /// both a gap and an unresolved conflict mean the query was not proved.
    fn exit_code(self) -> i32 {
        match self {
            Outcome::Proved => 0,
            Outcome::Gap | Outcome::Unresolved => 1,
        }
    }
}

/// What the command line asked for after the leading environment options.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Invocation {
    Batch { file: String, commands: Vec<String> },
    Commands(Vec<String>),
    Repl,
    Env,
    Help,
    Version,
}

/// Parse the leading environment options, then the entry point.
///
/// Options are only recognised in one contiguous prefix. After a file,
/// `check`, `repl`, `env` or a colon command has started, an argument that
/// looks like an option is a usage error and is never silently ignored.
/// `--help` and `--version` only work as the sole argument.
fn parse_invocation(args: &[String]) -> Result<(environment::Options, Invocation), String> {
    if args.len() == 1 {
        match args[0].as_str() {
            "--help" | "-h" => return Ok((environment::Options::default(), Invocation::Help)),
            "--version" | "-V" => {
                return Ok((environment::Options::default(), Invocation::Version));
            }
            _ => {}
        }
    }

    let mut options = environment::Options::default();
    let mut index = 0;
    while let Some(argument) = args.get(index) {
        match argument.as_str() {
            "--profile" => {
                if options.profile.is_some() {
                    return Err("用法错误：--profile 只能使用一次".to_owned());
                }
                options.profile = Some(invocation_value(
                    args,
                    index,
                    "--profile",
                    "--profile <名字>",
                )?);
                index += 2;
            }
            "--as-of" => {
                if options.as_of.is_some() {
                    return Err("用法错误：--as-of 只能使用一次".to_owned());
                }
                let value = invocation_value(args, index, "--as-of", "--as-of <YYYY-MM-DD>")?;
                std_deduce_lawpack::validate_date("--as-of", &value)
                    .map_err(|error| format!("用法错误：{}", escape_control(&error)))?;
                options.as_of = Some(value);
                index += 2;
            }
            "--jurisdiction" => {
                if options.jurisdiction.is_some() {
                    return Err("用法错误：--jurisdiction 只能使用一次".to_owned());
                }
                let value =
                    invocation_value(args, index, "--jurisdiction", "--jurisdiction <代码>")?;
                std_deduce_lawpack::validate_jurisdiction_code("--jurisdiction", &value)
                    .map_err(|error| format!("用法错误：{}", escape_control(&error)))?;
                options.jurisdiction = Some(value);
                index += 2;
            }
            "--no-default-packs" => {
                options.no_default_packs = true;
                index += 1;
            }
            "--allow-community-packs" => {
                options.allow_community_packs = true;
                index += 1;
            }
            _ => break,
        }
    }
    if options.profile.is_some() && options.no_default_packs {
        return Err("用法错误：--profile 与 --no-default-packs 不能同时使用".to_owned());
    }

    let rest = &args[index..];
    let Some(first) = rest.first() else {
        return Ok((options, Invocation::Repl));
    };
    match first.as_str() {
        "check" => {
            let Some(file) = rest.get(1) else {
                return Err("用法：std-deduce check <文件.std> [命令...]".to_owned());
            };
            if file.starts_with('-') {
                return Err(unknown_option_message(
                    file,
                    "std-deduce check 的第一个参数必须是文件",
                ));
            }
            Ok((
                options,
                Invocation::Batch {
                    file: file.clone(),
                    commands: rest[2..].to_vec(),
                },
            ))
        }
        "repl" => {
            if rest.len() == 1 {
                Ok((options, Invocation::Repl))
            } else {
                Err(extra_argument_error(
                    &rest[1],
                    "用法：std-deduce repl（不接受额外参数）",
                ))
            }
        }
        "env" => {
            if rest.len() == 1 {
                Ok((options, Invocation::Env))
            } else {
                Err(format!(
                    "用法：std-deduce env（不接受额外参数）；选项要写在 env 之前，例如 std-deduce --no-default-packs env{}",
                    if rest[1].starts_with('-') {
                        format!("；`{}` 不是 env 的参数", escape_path(&rest[1]))
                    } else {
                        String::new()
                    }
                ))
            }
        }
        "--help" | "-h" | "--version" | "-V" => Err(format!(
            "用法错误：{}只能作为唯一参数使用",
            escape_path(first)
        )),
        first if first.starts_with(':') => Ok((options, Invocation::Commands(rest.to_vec()))),
        first if first.starts_with('-') => Err(unknown_option_message(
            first,
            "std-deduce 的第一个参数必须是文件或命令",
        )),
        _ => Ok((
            options,
            Invocation::Batch {
                file: first.clone(),
                commands: rest[1..].to_vec(),
            },
        )),
    }
}

/// The value that follows a leading option.
///
/// A missing value and a value that looks like another option are both usage
/// errors: an option is never silently consumed as a value, and a typo never
/// turns into a session setting.
fn invocation_value(
    args: &[String],
    index: usize,
    option: &str,
    usage: &str,
) -> Result<String, String> {
    let Some(value) = args.get(index + 1) else {
        return Err(format!("用法错误：{option} 缺少值（用法：{usage}）"));
    };
    if value.starts_with('-') {
        return Err(format!(
            "用法错误：{option} 缺少值，`{}` 看起来是选项",
            escape_path(value)
        ));
    }
    Ok(value.clone())
}

/// The usage error for an unexpected extra argument of `repl`.
fn extra_argument_error(argument: &str, usage: &str) -> String {
    if argument.starts_with('-') {
        unknown_option_message(argument, usage)
    } else {
        usage.to_owned()
    }
}

struct Session {
    lib: Library,
    /// Whether a theory has been loaded. `:verify-cert` needs an environment,
    /// so it refuses to run before any `:load`.
    loaded: bool,
    /// Packs loaded through the registry, in load order. A package loaded from
    /// a file path directly has no entry; its declarations still show `[ns]`.
    packs: Vec<packs::LoadedPackInfo>,
    /// The lazily prepared default legal environment.
    environment: environment::Environment,
}

impl Session {
    fn new(options: environment::Options) -> Self {
        Session {
            lib: Library::new(),
            loaded: false,
            packs: Vec::new(),
            environment: environment::Environment::new(options),
        }
    }

    /// The environment identity an exported certificate records.
    ///
    /// The identity comes from the active profile, the session's `--as-of` /
    /// `--jurisdiction` values, the packs this session has loaded (including
    /// explicit imports) and the corpus files those packs link below
    /// `<current directory>/law/corpus`. It is always a recorded identity: an
    /// error here stops `:cert` before any JSON is written.
    fn identity(&self) -> Result<EnvironmentIdentity, String> {
        let corpus_root = std::env::current_dir()
            .map_err(|error| format!("无法取得当前目录：{}", escape_control(&error.to_string())))?
            .join("law")
            .join("corpus");
        identity::build(
            self.environment.profile_name(),
            self.environment.as_of(),
            self.environment.jurisdiction(),
            &self.packs,
            &corpus_root,
        )
    }

    /// Load a theory file into the session and print the load report.
    ///
    /// Both `:load` and the batch entry point go through this one function, so
    /// they cannot report or fail differently. The returned error is already
    /// rendered as `path:line:col: error: ...` (or `path: error: ...` when the
    /// loader has no source position); callers add their own command prefix, if
    /// any.
    ///
    /// The first load first prepares the default legal environment when the
    /// current directory declares one. The whole load runs on cloned session
    /// state: a failed environment preparation, import, package or file load
    /// leaves no declarations or package records behind, and the preload report
    /// is printed only after the file load commits. Imports resolve against
    /// the session's loaded namespaces first: one that a file already introduced
    /// needs no registry, while one that came from a pack is still re-checked
    /// for version/hash drift. Only the remaining imports scan the registry
    /// once, verify the lock once, and load every package (dependencies first).
    fn load_theory(&mut self, path: &str, out: &mut impl Write) -> Result<Outcome, String> {
        let src = std::fs::read_to_string(path)
            .map_err(|e| format!("{}: error: 读取失败：{e}", escape_path(path)))?;
        // The parser is also run by `Library::load`; doing it here first is
        // what lets a file without imports take the old path untouched and
        // returns parser diagnostics in exactly the same rendering as before.
        let items = std_deduce_lang::parser::parse(&src).map_err(|error| {
            std_deduce_lang::LoadError::at(error.msg, error.line, error.col).render(path)
        })?;
        let imports = packs::imports_of(&items);
        let namespace = namespace_of(&items);

        // The whole load, including preparing the default environment, runs on
        // clones; no partial state can survive a failure.
        let mut lib = self.lib.clone();
        let mut loaded_packs = self.packs.clone();
        let mut environment = self.environment.clone();
        let preload = environment.ensure_loaded(&mut lib, &mut loaded_packs)?;

        // A top-level file may not declare inside a namespace a loaded pack
        // owns: the flat ledger would merge them and `:inspect` could not tell
        // the file's declarations from the pack's.
        reject_pack_namespace(path, namespace, &loaded_packs)?;

        // Imports first look at what this session already loaded. A namespace
        // that arrived through a pack is kept on the registry path so a changed
        // version or hash is still reported; one loaded directly from a file
        // needs no registry at all.
        let pack_names: BTreeSet<&str> =
            loaded_packs.iter().map(|pack| pack.name.as_str()).collect();
        let loaded_namespaces: BTreeSet<&str> = lib
            .theories
            .iter()
            .filter_map(|theory| theory.namespace.as_deref())
            .collect();
        let registry_imports: Vec<String> = imports
            .iter()
            .filter(|name| {
                !loaded_namespaces.contains(name.as_str()) || pack_names.contains(name.as_str())
            })
            .cloned()
            .collect();

        if !registry_imports.is_empty() {
            let registry = packs::Registry::open().map_err(|errors| errors.join("\n"))?;
            let mut loader = packs::PackageLoader::new(&registry, &mut lib, &mut loaded_packs);
            loader.load_imports(&registry_imports, Path::new(path))?;
            // A pack imported by this very file may own the file's namespace,
            // so check the packages loaded above as well.
            reject_pack_namespace(path, namespace, &loaded_packs)?;
        }

        // The case/module file itself is loaded last, after its dependencies.
        // If it fails, the cloned library and package list are dropped and the
        // pending preload report is never printed.
        let report = match lib.load(path, &src) {
            Ok(report) => report,
            Err(error) => {
                let error = error.render(path);
                return Err(environment.annotate_error(error, &imports));
            }
        };
        self.lib = lib;
        self.packs = loaded_packs;
        self.environment = environment;
        self.loaded = true;
        // The preload lines are printed only now that the whole load committed:
        // a failed file never claims that the environment loaded.
        if let Some(report) = preload {
            write!(out, "{report}").ok();
        }
        self.print_load_report(path, &report, out);
        Ok(Outcome::Proved)
    }

    /// Print the declarations a successful load reported, in ledger order.
    ///
    /// `report.imported` belongs to the top-level file only; the package
    /// loader never prints its own files' reports, so internal dependencies are
    /// not repeated here.
    fn print_load_report(&self, path: &str, report: &LoadReport, out: &mut impl Write) {
        writeln!(out, "已加载 `{path}`。").ok();
        for name in &report.imported {
            let marker = self
                .environment
                .import_marker(name, &self.packs)
                .unwrap_or_default();
            writeln!(out, "  导入 {name}{marker}").ok();
        }
        for d in &report.declared {
            writeln!(out, "  + {d}").ok();
        }
        for c in &report.checked {
            writeln!(out, "  ✓ {c}").ok();
        }
        for s in &report.shown {
            writeln!(out, "  · {s}").ok();
        }
    }

    fn handle(&mut self, line: &str, out: &mut impl Write) -> Result<Outcome, String> {
        let line = line.trim();
        if line.is_empty() {
            return Ok(Outcome::Proved);
        }
        if line.starts_with('-') {
            // A bare line is normally a colon command. An option-looking line
            // is not a command and is never a comment: silently accepting it
            // would turn `std-deduce file.std --help` into a success.
            return Err(unknown_option_message(
                line,
                "它不是命令；查询请用 :why / :gap",
            ));
        }
        if let Some(rest) = line.strip_prefix(':') {
            let (cmd, arg) = rest.split_once(char::is_whitespace).unwrap_or((rest, ""));
            let arg = arg.trim();
            match cmd {
                "load" => self.load_theory(arg, out),
                "inspect" => {
                    // The ledger is flat, so recover each declaration's source
                    // namespace from the theory that recorded it. Case files
                    // have no namespace and therefore print exactly as before.
                    let namespaces: std::collections::HashMap<String, String> = self
                        .lib
                        .theories
                        .iter()
                        .filter_map(|theory| {
                            theory.namespace.as_ref().map(|ns| (theory, ns.clone()))
                        })
                        .flat_map(|(theory, ns)| {
                            theory
                                .decls
                                .iter()
                                .map(move |decl| (decl.clone(), ns.clone()))
                        })
                        .collect();
                    // A package supplies the richer `[name@version]` suffix,
                    // but only for a name it really declared; a namespace
                    // loaded directly from a file keeps `[ns]`.
                    let pack_by_decl: std::collections::HashMap<&str, &packs::LoadedPackInfo> =
                        self.packs
                            .iter()
                            .flat_map(|pack| {
                                pack.decls.iter().map(move |decl| (decl.as_str(), pack))
                            })
                            .collect();
                    for decl in self.lib.env.iter() {
                        let kind = match &decl.kind {
                            DeclKind::Sort => "sort ",
                            DeclKind::Obj => "obj  ",
                            DeclKind::Pred => "pred ",
                            DeclKind::Axiom => "axiom",
                            DeclKind::Def { .. } => "def  ",
                            DeclKind::Rule(_) => "rule ",
                            DeclKind::Interpretation(_) => "interp",
                            DeclKind::Contrary { .. } => "contr ",
                            DeclKind::Unique { .. } => "uniq  ",
                        };
                        let namespace = match pack_by_decl.get(decl.name.as_ref()) {
                            Some(pack) => format!(" [{}@{}]", pack.name, pack.version),
                            None => namespaces
                                .get(decl.name.as_ref())
                                .map(|ns| format!(" [{ns}]"))
                                .unwrap_or_default(),
                        };
                        writeln!(
                            out,
                            "  {kind} {} : {}{namespace}",
                            decl.name,
                            print_expr(&decl.ty)
                        )
                        .ok();
                        for s in &decl.sources {
                            writeln!(out, "       ← {}", s.one_line()).ok();
                            for line in s.full().lines() {
                                writeln!(out, "         {line}").ok();
                            }
                        }
                    }
                    Ok(Outcome::Proved)
                }
                "given" => {
                    let t = parse_term(arg)?;
                    let e = elab::elab_top(&self.lib.env, &t).map_err(|e| e.msg)?;
                    check::check(&self.lib.env, &Ctx::new(), &e, &Expr::Sort(0))
                        .map_err(|e| e.to_string())?;
                    writeln!(out, "已登记假设：{}", print_expr(&e)).ok();
                    // Stash it on the library as an assumption of the current
                    // session, recorded as a declaration for auditability.
                    let mut lib = self.lib.clone();
                    let name = format!("已知{}", lib.env.len());
                    let decl = std_deduce_kernel::Decl {
                        name: std_deduce_kernel::name(&name),
                        kind: DeclKind::Axiom,
                        ty: e,
                        sources: vec![SourceRef {
                            text: "用户输入".into(),
                            locator: "交互会话".into(),
                            ..Default::default()
                        }],
                        index: 0,
                    };
                    lib.env
                        .insert(decl, &Ctx::new())
                        .map_err(|e| e.to_string())?;
                    self.lib = lib;
                    Ok(Outcome::Proved)
                }
                "why" | "gap" => self.query(cmd, arg, out),
                "cert" => self.export_certificate(arg, out),
                "verify-cert" => self.verify_certificate(arg, out),
                "check" => Err(
                    ":check 已改名为 :verify-cert；检查源文件请直接运行 std-deduce <文件>"
                        .to_owned(),
                ),
                "packs" => self.list_packs(arg, out),
                "lock" => self.lock_packs(arg, out),
                "audit" => self.audit_sources(arg, out),
                "quit" | "exit" => Ok(Outcome::Proved),
                other => Err(format!("未知命令 `:{other}`")),
            }
        } else {
            // Bare line: treated as a command.
            self.handle(&format!(":{line}"), out)
        }
    }

    fn query(&mut self, cmd: &str, arg: &str, out: &mut impl Write) -> Result<Outcome, String> {
        let goal = self.goal(arg)?;
        let mut r = Reasoner::new(&self.lib.env);
        // Every axiom whose declared type is a proposition is usable as an
        // assumption. This is how a corpus of facts enters. See
        // `Reasoner::assume_ledger_axioms`.
        r.assume_ledger_axioms()?;
        r.saturate()?;

        // A conclusion can be in a recorded conflict without being asserted:
        // that is a third outcome, distinct from both success and a gap.
        if let Some(c) = r.conflict_for(&goal) {
            match &c.resolution {
                Resolution::Unresolved => {
                    report_unresolved(out, &r, &goal, &c);
                    return Ok(Outcome::Unresolved);
                }
                Resolution::Defeated { winner } => {
                    let side = r.conflict_side(&c, &goal);
                    if side != Some(*winner) {
                        report_defeated(out, &r, &goal, &c, *winner);
                        return Ok(Outcome::Gap);
                    }
                    // The winner is asserted; fall through and show it as
                    // proved, with a note about the defeated competitor.
                    let reachable = r.knows(&goal);
                    debug_assert!(reachable);
                }
            }
        }

        let reachable = r.knows(&goal);

        if cmd == "gap" {
            let ex = r.explain(&goal);
            if reachable {
                writeln!(out, "目标可以推出。").ok();
                return Ok(Outcome::Proved);
            }
            writeln!(out, "无法推出 {}。以下是缺口：", print_expr(&goal)).ok();
            if let Some(n) = ex.note {
                writeln!(out, "  {n}").ok();
            }
            if ex.candidates.is_empty() {
                writeln!(
                    out,
                    "  没有任何规则以它为结论：要么补一条规则，要么把它作为已知事实登记。"
                )
                .ok();
            }
            for c in ex.candidates {
                writeln!(out, "  候选 ⟨{}⟩", c.rule).ok();
                for s in &c.sources {
                    writeln!(out, "    ← {}", s.one_line()).ok();
                }
                if !c.missing.is_empty() {
                    writeln!(
                        out,
                        "    缺：{}",
                        c.missing
                            .iter()
                            .map(print_expr)
                            .collect::<Vec<_>>()
                            .join("；")
                    )
                    .ok();
                }
                for b in &c.blocked_by {
                    writeln!(
                        out,
                        "    被阻断：「{}」已成立，故本规则不触发",
                        print_expr(b)
                    )
                    .ok();
                }
            }
            return Ok(Outcome::Gap);
        }

        let mut d = r.derivation();
        if reachable {
            d.root = r.root_for(&goal);
        } else {
            let ex = r.explain(&goal);
            let id = d.nodes.len();
            d.nodes.push(std_deduce_reason::Node::Gap {
                prop: goal.clone(),
                candidates: ex.candidates,
                note: ex.note,
            });
            d.root = Some(id);
        }

        let certificate = reason_certificate(&d)?;
        // The tree is printed from the certificate, then that same certificate
        // is checked by both layers: the tree the user sees and the object
        // being checked cannot diverge.
        writeln!(out, "{}", render(&certificate)?).ok();

        let checked = std_deduce_cert::check(&self.lib.env, &certificate);
        let kernel = std_deduce_cert::kernel_proof(&self.lib.env, &certificate);
        let (report, kernel_report) = match (checked, kernel) {
            (Ok(report), Ok(kernel)) => (report, kernel),
            (checked, kernel) => {
                let mut failures = Vec::new();
                if let Err(error) = checked {
                    writeln!(out, "逻辑校验失败：{error}").ok();
                    failures.push(format!("逻辑层：{error}"));
                }
                if let Err(error) = kernel {
                    writeln!(out, "内核证明失败：{error}").ok();
                    failures.push(format!("内核层：{error}"));
                }
                return Err(format!("证书校验失败（{}）", failures.join("；")));
            }
        };

        let root = certificate
            .root
            .ok_or_else(|| "推理器生成的证书没有根节点：无法确认结论".to_owned())?;
        if matches!(certificate.nodes.get(root), Some(CertNode::Gap { .. })) {
            writeln!(out, "证书有效，但根为缺口，结论未被证明。").ok();
            report_conflicts(out, &certificate);
            return Ok(Outcome::Gap);
        }
        if !report.root_proved || !kernel_report.root_proved {
            writeln!(out, "证书有效，但根未被证明，结论未被证明。").ok();
            report_conflicts(out, &certificate);
            return Ok(Outcome::Gap);
        }

        let unresolved = certificate
            .conflicts
            .iter()
            .filter(|conflict| {
                matches!(conflict.resolution, std_deduce_cert::Resolution::Unresolved)
            })
            .count();
        if !certificate.open_obligations.is_empty() || unresolved > 0 {
            writeln!(
                out,
                "证书有效且根已证明，但仍有未决义务（open_obligations {} 项，未决冲突 {} 项），不能报告为无保留的证明。",
                certificate.open_obligations.len(),
                unresolved
            )
            .ok();
            report_conflicts(out, &certificate);
            return Ok(Outcome::Gap);
        }

        // Determine the defeated-conflict note before printing the success
        // line: a comparison failure is an error, never a success followed by
        // an error.
        let won_conflict = if reachable {
            won_conflict_note(&self.lib.env, &goal, &certificate)?
        } else {
            None
        };

        writeln!(out, "推导已通过独立校验。").ok();
        report_conflicts(out, &certificate);
        if let Some(other) = won_conflict {
            writeln!(
                out,
                "注：与「{}」存在冲突，已按记录的裁决为本结论胜出（裁决依据与优先级来源未核验）。",
                print_expr(&other)
            )
            .ok();
        }
        Ok(Outcome::Proved)
    }

    /// Parse `arg` as a proposition in the current environment.
    fn goal(&self, arg: &str) -> Result<Expr, String> {
        let t = parse_term(arg)?;
        let goal = elab::elab_top(&self.lib.env, &t).map_err(|e| e.msg)?;
        check::check(&self.lib.env, &Ctx::new(), &goal, &Expr::Sort(0))
            .map_err(|e| format!("目标不是命题：{e}"))?;
        Ok(goal)
    }

    /// Derive `arg` and print its certificate as pretty JSON.
    ///
    /// A proved goal has that proof as the root. An unreachable goal gets a
    /// gap node as the root, with the same candidates `:gap` would report, so
    /// the exported certificate is still checkable and says `root_proved
    /// = false` rather than pretending to be a proof.
    ///
    /// The certificate is stamped with the current environment identity before
    /// serialization. A theory must be loaded: the identity describes the
    /// environment the proof was derived in, and an unrecorded certificate can
    /// never be exported. Every failure happens before anything is written, so
    /// stdout never carries half a JSON document.
    fn export_certificate(&self, arg: &str, out: &mut impl Write) -> Result<Outcome, String> {
        if !self.loaded {
            return Err(
                "尚未加载理论：:cert 需要已加载的环境才能记录环境身份，请先 :load <文件>".into(),
            );
        }
        if arg.is_empty() {
            return Err("用法：:cert <目标命题>".into());
        }
        let goal = self.goal(arg)?;
        let mut r = Reasoner::new(&self.lib.env);
        r.assume_ledger_axioms()?;
        r.saturate()?;

        let reachable = r.knows(&goal);
        let mut d = r.derivation();
        if reachable {
            d.root = r.root_for(&goal);
        } else {
            let ex = r.explain(&goal);
            let id = d.nodes.len();
            d.nodes.push(std_deduce_reason::Node::Gap {
                prop: goal.clone(),
                candidates: ex.candidates,
                note: ex.note,
            });
            d.root = Some(id);
        }

        let certificate = reason_certificate(&d)?.with_environment(self.identity()?);
        let json = certificate
            .to_json_pretty()
            .map_err(|e| format!("证书序列化失败：{e}"))?;
        writeln!(out, "{json}").ok();
        Ok(if reachable {
            Outcome::Proved
        } else {
            Outcome::Gap
        })
    }

    /// Check a certificate against the loaded environment, without rerunning
    /// the reasoner.
    ///
    /// Both layers run and are reported separately: `cert::check` rebuilds
    /// rule instances and side conditions, then `kernel_proof` rebuilds the
    /// monotone proof terms and asks the kernel. A logical pass with a kernel
    /// failure is an error (`2`), not a valid certificate.
    ///
    /// The argument is `<file>` or `<file> <goal>`. A path containing
    /// whitespace is double-quoted when a goal follows. Without quotes, an
    /// argument that is exactly an existing file is taken as a path; otherwise
    /// the first whitespace separates the path from the goal. When a goal is
    /// given, the root's proposition must be definitionally equal to it; a gap
    /// root, a missing root and a mismatch all fail the binding (exit `2`).
    fn verify_certificate(&self, arg: &str, out: &mut impl Write) -> Result<Outcome, String> {
        if !self.loaded {
            write_verify_cert_not_run(out, "尚未加载理论");
            return Err(
                "尚未加载理论：:verify-cert 需要环境才能校验证书，请先 :load <文件>".into(),
            );
        }
        if arg.is_empty() {
            return Err("用法：:verify-cert <证书文件> [目标命题]".into());
        }
        let (path, goal) = split_verify_cert_argument(arg)?;
        let text = match std::fs::read_to_string(path) {
            Ok(text) => text,
            Err(e) => {
                write_verify_cert_not_run(out, "读取证书失败");
                return Err(format!("读取证书 `{}` 失败：{e}", escape_path(path)));
            }
        };
        let certificate = match Certificate::from_json(&text) {
            Ok(certificate) => certificate,
            Err(e) => {
                write_verify_cert_not_run(out, "证书 JSON 无效");
                return Err(format!(
                    "证书 `{}` 不是有效的证书 JSON：{e}",
                    escape_path(path)
                ));
            }
        };

        // Layer 0: a certificate only means something in the environment that
        // produced it. Compare the recorded identity before running either
        // proof layer, so a pack or corpus change cannot be silently ignored.
        self.check_certificate_environment(&certificate, out)?;

        // Layer 1: rebuild every rule instance from its own evidence and check
        // the recorded `unless` conditions and the root's conflict status.
        let report = match std_deduce_cert::check(&self.lib.env, &certificate) {
            Ok(report) => report,
            Err(e) => {
                writeln!(out, "逻辑校验：失败（{e}）").ok();
                writeln!(out, "内核证明：未运行（逻辑校验失败）").ok();
                writeln!(out, "侧条件：未评估（逻辑校验失败）").ok();
                writeln!(out, "需人判断：未评估（逻辑校验失败）").ok();
                return Err(format!("证书校验失败（逻辑层）：{e}"));
            }
        };
        writeln!(
            out,
            "逻辑校验：通过（检查 {} 个节点；{}）",
            report.nodes_checked,
            root_summary(&certificate, &report)
        )
        .ok();

        // Layer 2: the monotone skeleton must survive the kernel, not only the
        // structural check above.
        let kernel = match std_deduce_cert::kernel_proof(&self.lib.env, &certificate) {
            Ok(kernel) => kernel,
            Err(e) => {
                writeln!(out, "内核证明：失败（{e}）").ok();
                writeln!(out, "侧条件：未评估（内核证明失败）").ok();
                writeln!(out, "需人判断：未评估（内核证明失败）").ok();
                return Err(format!("证书校验失败（内核层）：{e}"));
            }
        };
        writeln!(
            out,
            "内核证明：通过（{} 个规则步骤；{}）",
            kernel.steps.len(),
            if kernel.root_proved {
                "根证明项通过内核"
            } else {
                "根为缺口，无证明项"
            }
        )
        .ok();

        let unresolved = certificate
            .conflicts
            .iter()
            .filter(|conflict| {
                matches!(conflict.resolution, std_deduce_cert::Resolution::Unresolved)
            })
            .count();
        let requires_human = report.requires_human || unresolved > 0;

        writeln!(
            out,
            "侧条件：unless 未发现已成立的阻断条件；未决冲突 {} 项；{}优先级来源未核验",
            unresolved,
            if report.conflict_resolved {
                "根冲突已按记录裁决；"
            } else {
                ""
            }
        )
        .ok();
        writeln!(
            out,
            "需人判断：{}",
            human_summary(&certificate, requires_human, unresolved)
        )
        .ok();

        // A root is successful only when both layers agree on it and nothing
        // is left to a human or an unresolved conflict.
        let proved = report.root_proved && kernel.root_proved && !requires_human && unresolved == 0;
        let outcome = if proved {
            Outcome::Proved
        } else {
            Outcome::Gap
        };

        // The certificate may be legal while proving a different proposition.
        // Only a caller-supplied goal can rule that out, and a failed binding
        // is an error even when the certificate itself passed both layers.
        if let Some(goal) = goal {
            self.check_goal_binding(goal, &certificate, out)?;
        }
        Ok(outcome)
    }

    /// Compare the certificate's recorded environment with the current one.
    ///
    /// The check passes only when both identities are recorded, the current
    /// identity can be built, and there is no difference. Every failure prints
    /// the environment outcome first, then the four proof lines as not run,
    /// and returns an error so the process exits `2`; no proof layer runs.
    fn check_certificate_environment(
        &self,
        certificate: &Certificate,
        out: &mut impl Write,
    ) -> Result<(), String> {
        let current = match self.identity() {
            Ok(current) => current,
            Err(error) => {
                writeln!(out, "环境校验：未运行（无法构造当前环境身份：{error}）").ok();
                write_verify_cert_checks_not_run(out, "环境校验未运行");
                return Err(format!("环境校验未运行：无法构造当前环境身份：{error}"));
            }
        };
        let Some(current) = current.as_recorded() else {
            // `identity::build` always records; if that ever changes, fail
            // closed rather than treating "nothing recorded" as an empty match.
            writeln!(out, "环境校验：未运行（当前环境身份未记录）").ok();
            write_verify_cert_checks_not_run(out, "环境校验未运行");
            return Err("环境校验未运行：当前环境身份未记录".into());
        };
        let differences = match certificate.environment.differences(current) {
            Ok(differences) => differences,
            Err(error) => {
                writeln!(out, "环境校验：未运行（{error}）").ok();
                write_verify_cert_checks_not_run(out, "环境校验未运行");
                return Err(format!("环境校验未运行：{error}"));
            }
        };
        if !differences.is_empty() {
            writeln!(out, "环境校验：失败（{} 处差异）", differences.len()).ok();
            for difference in &differences {
                writeln!(out, "  - {}", environment_difference(difference)).ok();
            }
            write_verify_cert_checks_not_run(out, "环境校验失败");
            return Err(format!(
                "环境校验失败：证书记录的环境身份与当前环境不一致（{} 处差异）；\
                 逻辑与内核校验未运行",
                differences.len()
            ));
        }
        writeln!(out, "环境校验：通过（{}）", environment_summary(current)).ok();
        Ok(())
    }

    /// Check that the root node's proposition is the supplied goal.
    ///
    /// The comparison is kernel definitional equality, not the printed form.
    /// A root that proves nothing (a gap) and a certificate without a root
    /// cannot be bound to any goal. Every failure prints
    /// `目标绑定：失败（...）` and returns an error, so the process exits `2`.
    fn check_goal_binding(
        &self,
        goal_text: &str,
        certificate: &Certificate,
        out: &mut impl Write,
    ) -> Result<(), String> {
        let goal = match self.goal(goal_text) {
            Ok(goal) => goal,
            Err(error) => {
                return fail_goal_binding(out, format!("目标无法解析：{error}"));
            }
        };

        let root_proposition = match certificate.root {
            None => return fail_goal_binding(out, "证书没有根节点"),
            Some(root) => match certificate.nodes.get(root) {
                None => {
                    return fail_goal_binding(
                        out,
                        format!(
                            "根节点 {root} 越界：证书只有 {} 个节点",
                            certificate.nodes.len()
                        ),
                    );
                }
                Some(CertNode::Assumption { assumption }) => {
                    match certificate.assumptions.get(*assumption) {
                        Some(entry) => Expr::from(&entry.proposition),
                        None => {
                            return fail_goal_binding(
                                out,
                                format!(
                                    "根引用了不存在的假设 {assumption}：证书只有 {} 条假设",
                                    certificate.assumptions.len()
                                ),
                            );
                        }
                    }
                }
                Some(CertNode::RuleApplication { conclusion, .. }) => Expr::from(conclusion),
                Some(CertNode::Gap { .. }) => {
                    return fail_goal_binding(out, "根为缺口，不证明任何命题");
                }
            },
        };

        match convertible(&self.lib.env, &Ctx::new(), &root_proposition, &goal) {
            Ok(true) => {
                writeln!(out, "目标绑定：通过（根命题与目标在内核下等价）").ok();
                Ok(())
            }
            Ok(false) => fail_goal_binding(
                out,
                format!(
                    "根命题「{}」与目标「{}」不等价",
                    print_expr(&root_proposition),
                    print_expr(&goal)
                ),
            ),
            Err(error) => fail_goal_binding(out, format!("无法比较根命题与目标：{error}")),
        }
    }

    /// List the legal-pack manifests under a directory.
    ///
    /// This reads and validates manifest format and, when a manifest declares
    /// `corpus`, reads that linked corpus to print its coverage. It does not
    /// load rules, does not check that the manifest's theory files exist, and
    /// does not require `:load`. Text that comes from a manifest, a path or a
    /// linked corpus is escaped before printing, so a newline or escape
    /// sequence cannot forge another output line.
    ///
    /// When `root/std.lock` exists, the registry is verified after the
    /// listing. A verification error is printed per pack and fails the
    /// command; a missing lock is only reported. Verification is skipped when
    /// the listing already failed, so a bad manifest is reported once.
    fn list_packs(&self, arg: &str, out: &mut impl Write) -> Result<Outcome, String> {
        let root = packs_root(arg)?;
        let found =
            std_deduce_lawpack::scan(&root).map_err(|error| escape_control(&error.to_string()))?;

        let mut corpus_errors = 0;
        for pack in &found.packs {
            let info = &pack.manifest.pack;
            writeln!(
                out,
                "{} {}  {}/{}  {}  {}  {}",
                info.name,
                info.version,
                info.jurisdiction,
                info.territory,
                effective_range(info),
                info.trust,
                escape_display_path(&pack.dir)
            )
            .ok();
            if let Some(description) = &info.description {
                writeln!(out, "  {}", escape_control(description)).ok();
            }
            if !pack.manifest.files.is_empty() {
                writeln!(out, "  文件 {} 个", pack.manifest.files.len()).ok();
            }
            if let Some(link) = &info.corpus {
                match read_pack_corpus(&root, link) {
                    Ok(corpus) => write_pack_coverage(out, &corpus),
                    Err(message) => {
                        writeln!(out, "{}", escape_control(&message)).ok();
                        corpus_errors += 1;
                    }
                }
            }
        }
        // No packs and no errors means an empty root, not a broken one.
        if found.packs.is_empty() && found.errors.is_empty() {
            writeln!(out, "没有找到法律包。").ok();
        }
        for error in &found.errors {
            writeln!(out, "{}", escape_control(&error.to_string())).ok();
        }
        // A broken manifest already fails the listing. Scanning the registry
        // again for the lock would print the same manifest error twice and
        // count it as a lock error, so verification waits for a clean listing.
        if !found.errors.is_empty() {
            writeln!(out, "锁定校验：未运行（清单错误）").ok();
            return Err(listing_error(
                found.errors.len(),
                "法律包清单错误",
                corpus_errors,
            ));
        }

        let lock_path = root.join(LOCK_FILE);
        let lock_errors = match std::fs::symlink_metadata(&lock_path) {
            Ok(_) => match std_deduce_lawpack::verify_lock(&root) {
                Ok(report) => {
                    writeln!(out, "锁定校验：通过（{} 个包）", report.verified).ok();
                    None
                }
                Err(errors) => {
                    for error in &errors {
                        writeln!(out, "{}", escape_control(&error.to_string())).ok();
                    }
                    Some(errors.len())
                }
            },
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                writeln!(out, "锁定校验：未找到 std.lock（未锁定）").ok();
                None
            }
            Err(error) => {
                writeln!(
                    out,
                    "{}",
                    escape_control(&format!("{}：无法读取锁文件：{error}", lock_path.display()))
                )
                .ok();
                Some(1)
            }
        };

        if let Some(count) = lock_errors {
            return Err(listing_error(count, "锁定校验错误", corpus_errors));
        }
        if corpus_errors > 0 {
            return Err(format!("{corpus_errors} 个语料错误"));
        }
        Ok(Outcome::Proved)
    }

    /// Hash every pack under a directory and write its `std.lock`.
    ///
    /// Nothing is written unless the whole registry could be scanned and
    /// hashed. Every error is printed and makes the command fail, so a bad
    /// pack can never leave a partial lock behind.
    fn lock_packs(&self, arg: &str, out: &mut impl Write) -> Result<Outcome, String> {
        let root = packs_root(arg)?;
        let lockfile = match std_deduce_lawpack::build_lock(&root) {
            Ok(lockfile) => lockfile,
            Err(errors) => {
                for error in &errors {
                    writeln!(out, "{}", escape_control(&error.to_string())).ok();
                }
                return Err(format!("{} 个错误，std.lock 未写入", errors.len()));
            }
        };
        let path = root.join(LOCK_FILE);
        lockfile
            .write(&path)
            .map_err(|error| escape_control(&error.to_string()))?;
        writeln!(
            out,
            "已写入 {}（{} 个包）",
            escape_display_path(&path),
            lockfile.pack.len()
        )
        .ok();
        Ok(Outcome::Proved)
    }

    /// Check every declared source's quotation against the article corpus.
    ///
    /// The corpus directory defaults to `law/corpus` below the current
    /// directory; an argument is the whole directory, so a path containing
    /// spaces needs no further quoting. A theory must be loaded first.
    ///
    /// Only sources with a non-empty `quote` take part in the audit. A source
    /// without a quotation is printed with `·` and does not affect the exit
    /// code, because case facts carry provenance but no article text to check.
    /// At least one quoted source is required; zero quoted sources prints
    /// "没有可核对的引文" and exits `1`, never a pass. A quoted source that is
    /// not a hit fails the run, including a missing corpus (`NoCorpus`, reported
    /// as unverified). A missing or empty corpus directory therefore leaves
    /// every quoted source unverified. A corpus with a broken layout or JSON,
    /// or a duplicate `(law, version)`, is a corpus error (exit `2`). A recorded
    /// `hash` is the SHA-256 of the article text exactly as stored, including
    /// newlines; the summary distinguishes hashes that were fixed and verified,
    /// absent hashes and hashes that could not be verified or are malformed.
    /// `text_sha256` in a corpus is provenance metadata only and is neither
    /// recomputed nor verified. After the summary, each loaded corpus prints its
    /// declared coverage: counts for formalized, partial, indexed and
    /// needs-ontology articles, the formalized and partial article numbers, the
    /// named ontology gaps, the open concepts and the note. The declaration is
    /// printed only; it is not compared with the rules in the loaded theory.
    fn audit_sources(&self, arg: &str, out: &mut impl Write) -> Result<Outcome, String> {
        if !self.loaded {
            writeln!(out, "语料核对：未运行（尚未加载理论）").ok();
            return Err("尚未加载理论：:audit 需要环境才能核对引文，请先 :load <文件>".into());
        }
        let root = corpus_root(arg)?;
        let corpora = match corpus::scan(&root) {
            Ok(scan) => {
                if !scan.errors.is_empty() {
                    for error in &scan.errors {
                        writeln!(out, "{}", escape_control(&error.to_string())).ok();
                    }
                    return Err(format!("{} 个语料错误，未进行核对", scan.errors.len()));
                }
                if scan.corpora.is_empty() {
                    writeln!(out, "语料目录中没有语料：{}", escape_display_path(&root)).ok();
                }
                scan.corpora
                    .into_iter()
                    .map(|loaded| loaded.corpus)
                    .collect()
            }
            Err(error) => {
                writeln!(out, "{}", escape_control(&error.to_string())).ok();
                Vec::new()
            }
        };

        if corpora.iter().any(|corpus| corpus.text_sha256.is_some()) {
            writeln!(
                out,
                "注：语料的 text_sha256 仅为出处元数据，未重算、未校验。"
            )
            .ok();
        }

        let mut quoted = 0;
        let mut unquoted = 0;
        let mut hit = 0;
        let mut mismatch = 0;
        let mut unverified = 0;
        let mut fixed_hash = 0;
        let mut unfixed_hash = 0;
        let mut unchecked_hash = 0;
        for decl in self.lib.env.iter() {
            for source in &decl.sources {
                let label = format!(
                    "「{}{}」",
                    escape_control(&source.text),
                    escape_control(&source.locator)
                );
                let citation = Citation {
                    text: &source.text,
                    locator: &source.locator,
                    version: &source.version,
                    quote: &source.quote,
                    hash: &source.hash,
                    jurisdiction: &source.jurisdiction,
                };
                let checked = corpus::audit(&corpora, &citation);
                if checked.audit == Audit::NoQuote {
                    unquoted += 1;
                    writeln!(out, "· {label}：没有引文原文，不参与核对").ok();
                    continue;
                }
                quoted += 1;
                if checked.hash_checked {
                    fixed_hash += 1;
                } else if source.hash.is_empty() {
                    unfixed_hash += 1;
                } else {
                    unchecked_hash += 1;
                }
                let line = if checked.audit.is_hit() {
                    hit += 1;
                    let id = checked
                        .corpus
                        .as_ref()
                        .ok_or_else(|| "内部错误：引文命中但没有对应的语料".to_owned())?;
                    format!("✓ {label}← {}", escape_control(&id.to_string()))
                } else if checked.audit.is_unverified() {
                    unverified += 1;
                    format!("? {label}：{}（未核对）", escape_control(&checked.detail))
                } else {
                    mismatch += 1;
                    match &checked.corpus {
                        Some(id) => format!(
                            "✗ {label}← {}：{}",
                            escape_control(&id.to_string()),
                            escape_control(&checked.detail)
                        ),
                        None => format!("✗ {label}：{}", escape_control(&checked.detail)),
                    }
                };
                writeln!(out, "{line}").ok();
            }
        }

        writeln!(
            out,
            "核对 {quoted} 条带引文来源：命中 {hit}，不一致 {mismatch}，未核对 {unverified}；另有 {unquoted} 条来源无引文（不参与核对）。"
        )
        .ok();
        if quoted == 0 {
            write_coverage(out, &corpora);
            writeln!(out, "没有可核对的引文：至少要有一条 quote 非空的来源。").ok();
            return Ok(Outcome::Gap);
        }
        writeln!(
            out,
            "条文哈希：{fixed_hash} 条已固定并核验，{unfixed_hash} 条未固定，{unchecked_hash} 条未核验或格式非法。"
        )
        .ok();
        write_coverage(out, &corpora);
        if hit == quoted {
            Ok(Outcome::Proved)
        } else {
            Ok(Outcome::Gap)
        }
    }
}

/// The top-level `namespace` of a parsed file, when it has one.
///
/// The parser guarantees that a namespace item is the first non-import item.
/// A case/example file has none.
fn namespace_of(items: &[Item]) -> Option<&str> {
    match items.iter().find(|item| !matches!(item, Item::Import(_))) {
        Some(Item::Namespace(namespace)) => Some(namespace.as_str()),
        _ => None,
    }
}

/// Refuse a top-level file whose namespace belongs to a loaded pack.
///
/// Package theory files are loaded through [`packs::PackageLoader`] directly,
/// so this check only guards files the user loads. It keeps a user file from
/// injecting declarations into an official namespace, where the flat ledger
/// would merge them with the pack's.
fn reject_pack_namespace(
    path: &str,
    namespace: Option<&str>,
    packs: &[packs::LoadedPackInfo],
) -> Result<(), String> {
    let Some(namespace) = namespace else {
        return Ok(());
    };
    if packs.iter().any(|pack| pack.namespace == namespace) {
        return Err(std_deduce_lang::LoadError::new(format!(
            "不能向已加载包 `{namespace}` 添加声明；请使用独立 namespace"
        ))
        .render(path));
    }
    Ok(())
}

/// Format a coverage list so the separator cannot be confused with an item.
///
/// Each item is wrapped in `「」`; an empty list prints `（无）` so the line does
/// not end at a bare colon.
fn quoted_list<S: AsRef<str>>(items: &[S]) -> String {
    if items.is_empty() {
        return "（无）".to_owned();
    }
    items
        .iter()
        .map(|item| format!("「{}」", escape_control(item.as_ref())))
        .collect::<Vec<_>>()
        .join("、")
}

/// Combine a listing error count with independently found corpus errors.
///
/// A manifest or lock error used to be returned alone even when a linked corpus
/// had already failed to load; the stderr then under-reported the failures that
/// stdout had shown. Both counts are reported instead.
fn listing_error(primary: usize, label: &str, corpus_errors: usize) -> String {
    if corpus_errors == 0 {
        format!("{primary} 个{label}")
    } else {
        format!("{primary} 个{label}、{corpus_errors} 个语料错误")
    }
}

/// Format ontology-gap counts as `「code」 count` joined by `、`.
///
/// The code is quoted so a code containing `、` or whitespace cannot be read as
/// several separate gaps.
fn format_gap_counts(gaps: &[(&str, usize)]) -> String {
    if gaps.is_empty() {
        return "（无）".to_owned();
    }
    gaps.iter()
        .map(|(gap, count)| format!("「{}」 {count}", escape_control(gap)))
        .collect::<Vec<_>>()
        .join("、")
}

/// Print the coverage attached to a pack's linked corpus.
///
/// The counts are a declaration from the corpus, not a comparison with the
/// pack's rules. A corpus without coverage prints `覆盖：未声明`.
fn write_pack_coverage(out: &mut impl Write, corpus: &Corpus) {
    let id = escape_control(&format!("{}@{}", corpus.law, corpus.version));
    match &corpus.coverage {
        Some(coverage) => {
            writeln!(
                out,
                "  覆盖 {id}：形式化 {} / 部分 {} / 仅索引 {} / 待本体 {}；开放概念 {}",
                coverage.count(CoverageStatus::Formalized),
                coverage.count(CoverageStatus::Partial),
                coverage.count(CoverageStatus::Indexed),
                coverage.count(CoverageStatus::NeedsOntology),
                coverage.open_concepts.len()
            )
            .ok();
            writeln!(
                out,
                "  本体缺口：{}",
                format_gap_counts(&coverage.gap_counts())
            )
            .ok();
        }
        None => {
            writeln!(out, "  覆盖 {id}：未声明").ok();
        }
    }
}

/// Read a manifest's `corpus = "<law-id>/<version>"` link.
///
/// The corpus lives next to the registry, not inside it: `law/corpus` is a
/// sibling of `lawpacks`. The registry root is made absolute first, so `:packs .`
/// and `:packs lawpacks` resolve the same corpus. The linked file must be a
/// regular file, not a symbolic link, and its own `law`/`version` must match
/// both segments of the link; otherwise a wrong corpus would be displayed under
/// this pack as if it were the pack's coverage.
fn read_pack_corpus(root: &Path, link: &str) -> Result<Corpus, String> {
    let Some((law, version)) = link.split_once('/') else {
        return Err(format!(
            "语料链接 `{link}` 格式无效：必须是 `<law-id>/<version>`"
        ));
    };
    if law.is_empty() || version.is_empty() || version.contains('/') {
        return Err(format!(
            "语料链接 `{link}` 格式无效：必须是 `<law-id>/<version>`"
        ));
    }
    let root = std::path::absolute(root)
        .map_err(|error| format!("无法解析注册表路径 `{}`：{error}", root.display()))?;
    let Some(parent) = root.parent() else {
        return Err(format!(
            "无法从注册表路径 `{}` 推导语料目录",
            root.display()
        ));
    };
    let path = parent
        .join("law")
        .join("corpus")
        .join(law)
        .join(format!("{version}.json"));
    let metadata = fs::symlink_metadata(&path)
        .map_err(|error| format!("无法读取语料文件 `{}`：{error}", path.display()))?;
    if !metadata.file_type().is_file() {
        return Err(format!(
            "语料文件 `{}` 必须是普通文件，不能是符号链接或其他类型",
            path.display()
        ));
    }
    let corpus = Corpus::read(&path).map_err(|error| error.to_string())?;
    if corpus.law != law || corpus.version != version {
        return Err(format!(
            "语料 `{}` 的标识是 `{}@{}`，与清单链接 `{link}` 不符",
            path.display(),
            corpus.law,
            corpus.version
        ));
    }
    Ok(corpus)
}

/// Print each loaded corpus's declared coverage.
///
/// This is a declaration from the corpus file: the audit displays it but does
/// not compare it with the rules in the loaded theory. Fields are escaped so a
/// newline or a format character cannot forge another output line.
fn write_coverage(out: &mut impl Write, corpora: &[Corpus]) {
    for corpus in corpora {
        let id = escape_control(&format!("{}@{}", corpus.law, corpus.version));
        match &corpus.coverage {
            Some(coverage) => {
                writeln!(
                    out,
                    "覆盖 {id}：形式化 {} 条 / 部分 {} 条 / 仅索引 {} 条 / 待本体 {} 条 / 开放概念 {} 个",
                    coverage.count(CoverageStatus::Formalized),
                    coverage.count(CoverageStatus::Partial),
                    coverage.count(CoverageStatus::Indexed),
                    coverage.count(CoverageStatus::NeedsOntology),
                    coverage.open_concepts.len()
                )
                .ok();
                writeln!(
                    out,
                    "  形式化：{}",
                    quoted_list(&coverage.numbers(CoverageStatus::Formalized))
                )
                .ok();
                writeln!(
                    out,
                    "  部分：{}",
                    quoted_list(&coverage.numbers(CoverageStatus::Partial))
                )
                .ok();
                writeln!(
                    out,
                    "  待本体：{}",
                    format_gap_counts(&coverage.gap_counts())
                )
                .ok();
                writeln!(out, "  开放概念：{}", quoted_list(&coverage.open_concepts)).ok();
                if let Some(notes) = &coverage.notes {
                    writeln!(out, "  备注：{}", escape_control(notes)).ok();
                }
            }
            None => {
                writeln!(out, "覆盖 {id}：未声明").ok();
            }
        }
    }
}

/// Resolve the legal-pack directory a `:packs` or `:lock` command operates on.
///
/// With no argument the directory is `lawpacks` below the current working
/// directory; with an argument the whole string is the directory, so a path
/// containing spaces needs no further quoting.
fn packs_root(arg: &str) -> Result<PathBuf, String> {
    directory_arg(arg, "lawpacks")
}

/// Resolve the corpus directory `:audit` operates on.
///
/// With no argument the directory is `law/corpus` below the current working
/// directory; with an argument the whole string is the directory.
fn corpus_root(arg: &str) -> Result<PathBuf, String> {
    directory_arg(arg, "law/corpus")
}

fn directory_arg(arg: &str, default: &str) -> Result<PathBuf, String> {
    if arg.is_empty() {
        Ok(std::env::current_dir()
            .map_err(|error| format!("无法取得当前目录：{}", escape_control(&error.to_string())))?
            .join(default))
    } else {
        Ok(PathBuf::from(arg))
    }
}

/// Split `:verify-cert`'s argument into a file path and an optional goal.
///
/// A leading double quote delimits a path that may contain whitespace; the
/// rest of the argument is the goal. Without quotes, an argument that names an
/// existing file is taken whole, which preserves the unquoted form for paths
/// containing spaces. Otherwise the first whitespace separates the path from
/// the goal.
fn split_verify_cert_argument(arg: &str) -> Result<(&str, Option<&str>), String> {
    let arg = arg.trim();
    if arg.is_empty() {
        return Err("用法：:verify-cert <证书文件> [目标命题]".into());
    }
    if let Some(rest) = arg.strip_prefix('"') {
        let Some(end) = rest.find('"') else {
            return Err("证书路径的引号未闭合".into());
        };
        let path = &rest[..end];
        let goal = rest[end + 1..].trim();
        return Ok((path, if goal.is_empty() { None } else { Some(goal) }));
    }
    if Path::new(arg).is_file() {
        return Ok((arg, None));
    }
    match arg.split_once(char::is_whitespace) {
        Some((path, rest)) => {
            let goal = rest.trim();
            Ok((path, if goal.is_empty() { None } else { Some(goal) }))
        }
        None => Ok((arg, None)),
    }
}

/// Print the failed binding line and return the error that exits `2`.
fn fail_goal_binding(out: &mut impl Write, detail: impl std::fmt::Display) -> Result<(), String> {
    writeln!(out, "目标绑定：失败（{detail}）").ok();
    Err(format!("目标绑定失败：{detail}"))
}

/// Render a path for a command's multi-line report.
///
/// Listing output escapes a literal backslash (via `escape_control`), unlike
/// the one-line load and certificate diagnostics, which use
/// [`escape_path`] so a Windows path keeps its separators single.
fn escape_display_path(path: &Path) -> String {
    escape_control(&path.display().to_string())
}

/// The usage error for an option where a command or a file was expected.
///
/// The option itself is escaped, so it cannot forge a diagnostic line either.
/// The hint names the escape hatch for a file whose name really starts with
/// `-`.
fn unknown_option_message(option: &str, expected: &str) -> String {
    format!(
        "未知选项 `{}`：{expected}；文件名以 - 开头时请写 ./-名字，帮助用 std-deduce --help",
        escape_path(option)
    )
}

/// Render a pack's effective date range. A missing endpoint is shown as
/// "not stated" instead of hiding the endpoint that is present.
fn effective_range(info: &PackInfo) -> String {
    match (&info.effective_from, &info.effective_to) {
        (None, None) => "未注明".to_owned(),
        (Some(from), Some(to)) => format!("{from}..{to}"),
        (Some(from), None) => format!("{from}..未注明"),
        (None, Some(to)) => format!("未注明..{to}"),
    }
}

/// Print the five labelled lines when `:verify-cert` cannot reach any check.
fn write_verify_cert_not_run(out: &mut impl Write, reason: &str) {
    writeln!(out, "环境校验：未运行（{reason}）").ok();
    write_verify_cert_checks_not_run(out, reason);
}

/// Print the four proof-layer lines as not run.
fn write_verify_cert_checks_not_run(out: &mut impl Write, reason: &str) {
    writeln!(out, "逻辑校验：未运行（{reason}）").ok();
    writeln!(out, "内核证明：未运行（{reason}）").ok();
    writeln!(out, "侧条件：未评估（{reason}）").ok();
    writeln!(out, "需人判断：未评估（{reason}）").ok();
}

/// The summary appended to a passing environment line.
fn environment_summary(record: &EnvironmentRecord) -> String {
    format!(
        "profile {}；包 {} 个；语料 {} 个；as_of {}；管辖 {}",
        environment_text(record.profile.as_deref()),
        record.packs.len(),
        record.corpora.len(),
        environment_text(record.as_of.as_deref()),
        environment_text(record.jurisdiction.as_deref()),
    )
}

/// One optional environment field, escaped and with `null` spelled out.
fn environment_text(value: Option<&str>) -> String {
    match value {
        Some(text) => escape_control(text),
        None => "未指定".to_owned(),
    }
}

/// Render one environment difference as a single escaped line.
///
/// Every value that comes from the certificate is untrusted input: it is
/// escaped so a newline or terminal escape sequence cannot forge another
/// output line.
fn environment_difference(difference: &EnvironmentDifference) -> String {
    match difference {
        EnvironmentDifference::Profile { recorded, current } => format!(
            "profile 不一致：证书为 {}，当前为 {}",
            environment_value(recorded.as_deref()),
            environment_value(current.as_deref())
        ),
        EnvironmentDifference::AsOf { recorded, current } => format!(
            "as_of 不一致：证书为 {}，当前为 {}",
            environment_value(recorded.as_deref()),
            environment_value(current.as_deref())
        ),
        EnvironmentDifference::Jurisdiction { recorded, current } => format!(
            "管辖不一致：证书为 {}，当前为 {}",
            environment_value(recorded.as_deref()),
            environment_value(current.as_deref())
        ),
        EnvironmentDifference::MissingPack(pack) => format!(
            "当前环境缺少证书记录的包 `{}@{}`（信任级别 {}，哈希 {}）",
            escape_control(&pack.name),
            escape_control(&pack.version),
            pack.trust,
            escape_control(&pack.hash)
        ),
        EnvironmentDifference::ExtraPack(pack) => format!(
            "当前环境多出证书未记录的包 `{}@{}`（信任级别 {}，哈希 {}）",
            escape_control(&pack.name),
            escape_control(&pack.version),
            pack.trust,
            escape_control(&pack.hash)
        ),
        EnvironmentDifference::PackVersion {
            name,
            recorded,
            current,
        } => format!(
            "包 `{}` 版本不一致：证书为 {}，当前为 {}",
            escape_control(name),
            escape_control(recorded),
            escape_control(current)
        ),
        EnvironmentDifference::PackHash {
            name,
            version,
            recorded,
            current,
        } => format!(
            "包 `{}@{}` 哈希不一致：证书为 {}，当前为 {}",
            escape_control(name),
            escape_control(version),
            escape_control(recorded),
            escape_control(current)
        ),
        EnvironmentDifference::PackTrust {
            name,
            version,
            recorded,
            current,
        } => format!(
            "包 `{}@{}` 信任级别不一致：证书为 {}，当前为 {}",
            escape_control(name),
            escape_control(version),
            recorded,
            current
        ),
        EnvironmentDifference::MissingCorpus(corpus) => format!(
            "当前环境缺少证书记录的语料 `{}@{}`（文件哈希 {}）",
            escape_control(&corpus.law),
            escape_control(&corpus.version),
            escape_control(&corpus.file_sha256)
        ),
        EnvironmentDifference::ExtraCorpus(corpus) => format!(
            "当前环境多出证书未记录的语料 `{}@{}`（文件哈希 {}）",
            escape_control(&corpus.law),
            escape_control(&corpus.version),
            escape_control(&corpus.file_sha256)
        ),
        EnvironmentDifference::CorpusHash {
            law,
            version,
            recorded,
            current,
        } => format!(
            "语料 `{}@{}` 文件哈希不一致：证书为 {}，当前为 {}",
            escape_control(law),
            escape_control(version),
            escape_control(recorded),
            escape_control(current)
        ),
    }
}

/// One recorded/current environment field value, escaped; `null` is spelled out.
fn environment_value(value: Option<&str>) -> String {
    match value {
        Some(text) => format!("`{}`", escape_control(text)),
        None => "null".to_owned(),
    }
}

/// Describe what the logical layer established about the root.
fn root_summary(certificate: &Certificate, report: &CheckReport) -> String {
    match certificate.root {
        None => "没有根节点".to_owned(),
        Some(root) if matches!(certificate.nodes[root], CertNode::Gap { .. }) => {
            "根未被证明，根为缺口".to_owned()
        }
        Some(_) if report.root_proved && report.root_is_assumption => {
            format!(
                "根已证明，根为假设，证书共 {} 条假设",
                report.assumption_count
            )
        }
        Some(_) if report.root_proved => {
            format!(
                "根已证明，根为规则推导，证书共 {} 条假设",
                report.assumption_count
            )
        }
        Some(_) => "根未被证明".to_owned(),
    }
}

/// Explain why a human is or is not needed, using the recorded obligations.
fn human_summary(certificate: &Certificate, requires_human: bool, unresolved: usize) -> String {
    if !requires_human {
        return "否（无未决义务）".to_owned();
    }
    let mut counts: std::collections::BTreeMap<&'static str, usize> =
        std::collections::BTreeMap::new();
    for obligation in &certificate.open_obligations {
        *counts
            .entry(obligation_kind_label(obligation.kind))
            .or_default() += 1;
    }
    let mut details: Vec<String> = counts
        .iter()
        .map(|(label, count)| format!("{label} {count} 项"))
        .collect();
    if details.is_empty() || (unresolved > 0 && !counts.contains_key("冲突未决")) {
        details.push(format!("未决冲突 {unresolved} 项"));
    }
    format!(
        "是（open_obligations {} 项：{}）",
        certificate.open_obligations.len(),
        details.join("、")
    )
}

/// The user-facing label of an obligation kind.
fn obligation_kind_label(kind: ObligationKind) -> &'static str {
    match kind {
        ObligationKind::MissingPremise => "缺少前提",
        ObligationKind::MissingSource => "缺少来源",
        ObligationKind::OpenConcept => "开放概念",
        ObligationKind::UnresolvedConflict => "冲突未决",
        ObligationKind::NeedsHumanDetermination => "需人判断",
        ObligationKind::Other => "其他",
    }
}

fn report_unresolved(out: &mut impl Write, r: &Reasoner, goal: &Expr, c: &Conflict) {
    writeln!(out, "冲突未决：{}", print_expr(goal)).ok();
    writeln!(
        out,
        "  该结论没有进入事实库——系统不替你选，但也绝不悄悄丢掉它。"
    )
    .ok();
    writeln!(
        out,
        "  左：{}  ← {}",
        print_expr(&c.left),
        describe(&c.left_by)
    )
    .ok();
    writeln!(
        out,
        "  右：{}  ← {}",
        print_expr(&c.right),
        describe(&c.right_by)
    )
    .ok();
    for (label, prop) in [("左", &c.left), ("右", &c.right)] {
        writeln!(out, "── 冲突{label}方：{} ──", print_expr(prop)).ok();
        show_derivation(out, r, prop);
    }
}

fn report_defeated(out: &mut impl Write, r: &Reasoner, goal: &Expr, c: &Conflict, winner: Side) {
    let (win, win_by) = match winner {
        Side::Left => (&c.left, &c.left_by),
        Side::Right => (&c.right, &c.right_by),
    };
    writeln!(
        out,
        "冲突已裁决：{} 与 {} 不能并存",
        print_expr(&c.left),
        print_expr(&c.right)
    )
    .ok();
    writeln!(
        out,
        "  本结论「{}」被否决；胜出的是「{}」（{}）。",
        print_expr(goal),
        print_expr(win),
        describe(win_by)
    )
    .ok();
    writeln!(out, "── 胜出方推导：{} ──", print_expr(win)).ok();
    show_derivation(out, r, win);
    writeln!(out, "── 被否决方推导：{} ──", print_expr(goal)).ok();
    show_derivation(out, r, goal);
}

fn show_derivation(out: &mut impl Write, r: &Reasoner, prop: &Expr) {
    let Some(d) = r.derivation_for(prop) else {
        writeln!(out, "  （推导无法重建：它的前提本身已不在事实库）").ok();
        return;
    };
    let certificate = match reason_certificate(&d) {
        Ok(certificate) => certificate,
        Err(error) => {
            writeln!(out, "  （该推导未能生成证书：{error}）").ok();
            return;
        }
    };
    match render(&certificate) {
        Ok(rendered) => writeln!(out, "{rendered}").ok(),
        Err(error) => {
            writeln!(out, "  （该推导的证书无法渲染：{error}）").ok();
            return;
        }
    };
    match std_deduce_cert::check(r.env(), &certificate) {
        Ok(report) if report.root_proved => {
            writeln!(out, "  （该推导通过证书逻辑校验）").ok();
        }
        Ok(_) => {
            writeln!(out, "  （该推导未通过证书逻辑校验：根未被证明）").ok();
        }
        Err(error) => {
            writeln!(out, "  （该推导未通过证书逻辑校验：{error}）").ok();
        }
    }
}

/// Print every conflict the certificate records.
fn report_conflicts(out: &mut impl Write, certificate: &Certificate) {
    for conflict in &certificate.conflicts {
        let how = match conflict.resolution {
            std_deduce_cert::Resolution::Unresolved => "未决",
            std_deduce_cert::Resolution::Defeated { .. } => "已裁决",
        };
        writeln!(
            out,
            "冲突（{how}）：{} 与 {}",
            print_expr(&Expr::from(&conflict.left)),
            print_expr(&Expr::from(&conflict.right))
        )
        .ok();
    }
}

/// The defeated competitor of a conflict the queried proposition won.
///
/// The proposition is matched with kernel definitional equality, not by
/// comparing printed strings.
fn won_conflict_note(
    env: &Env,
    goal: &Expr,
    certificate: &Certificate,
) -> Result<Option<Expr>, String> {
    for conflict in &certificate.conflicts {
        let left = Expr::from(&conflict.left);
        let right = Expr::from(&conflict.right);
        let side = if convertible(env, &Ctx::new(), goal, &left)
            .map_err(|error| format!("无法比较目标与冲突左命题：{error}"))?
        {
            Some(std_deduce_cert::Side::Left)
        } else if convertible(env, &Ctx::new(), goal, &right)
            .map_err(|error| format!("无法比较目标与冲突右命题：{error}"))?
        {
            Some(std_deduce_cert::Side::Right)
        } else {
            None
        };
        let (Some(side), std_deduce_cert::Resolution::Defeated { winner }) =
            (side, &conflict.resolution)
        else {
            continue;
        };
        if side != *winner {
            continue;
        }
        let other = match winner {
            std_deduce_cert::Side::Left => &conflict.right,
            std_deduce_cert::Side::Right => &conflict.left,
        };
        return Ok(Some(Expr::from(other)));
    }
    Ok(None)
}

fn describe(p: &Provenance) -> String {
    match p {
        Provenance::Assumption => "已知事实".into(),
        Provenance::Rules(rs) if rs.is_empty() => "已无可重建的规则实例".into(),
        Provenance::Rules(rs) => format!(
            "规则 {}",
            rs.iter()
                .map(|r| format!("⟨{r}⟩"))
                .collect::<Vec<_>>()
                .join("、")
        ),
    }
}

fn parse_term(s: &str) -> Result<std_deduce_lang::ast::Term, String> {
    // Wrap a bare term as `#check <term>`, which is the one place the
    // grammar admits a bare expression at the top level.
    let src = format!("#check {s}");
    let toks = std_deduce_lang::lexer::lex(&src).map_err(|e| e.to_string())?;
    let mut p = std_deduce_lang::parser::Parser::new(toks);
    // Skip the `#` and `check` tokens by parsing the program and taking the
    // command, keeping the parser's own recovery in one place.
    let items = p.program().map_err(|e| e.to_string())?;
    match items.into_iter().next() {
        Some(std_deduce_lang::ast::Item::Check(t)) => Ok(t),
        _ => Err("无法解析为项".into()),
    }
}

fn print_help(out: &mut impl Write) {
    writeln!(
        out,
        "std-deduce {} — 法律规则演绎系统",
        env!("CARGO_PKG_VERSION")
    )
    .ok();
    writeln!(out).ok();
    writeln!(out, "用法：").ok();
    writeln!(out, "  std-deduce                         进入 REPL").ok();
    writeln!(
        out,
        "  std-deduce <文件.std> [命令...]    加载文件；成功后依次执行后续冒号命令"
    )
    .ok();
    writeln!(
        out,
        "  std-deduce check <文件.std> [...]  等价于直接给文件（check 是批处理入口）"
    )
    .ok();
    writeln!(
        out,
        "  std-deduce env                     检查并加载默认法律环境"
    )
    .ok();
    writeln!(out, "  std-deduce repl                    进入 REPL").ok();
    writeln!(
        out,
        "  std-deduce <冒号命令> [...]        把每个参数当命令执行，例如 :load <文件>"
    )
    .ok();
    writeln!(out, "  std-deduce --help | -h             显示本用法").ok();
    writeln!(
        out,
        "  std-deduce --version | -V          显示版本（std-deduce <version>）"
    )
    .ok();
    writeln!(out).ok();
    writeln!(out, "环境选项（写在文件、子命令或命令之前）：").ok();
    writeln!(
        out,
        "  --profile <名字>             选择 lawpacks/profiles 里的环境 profile"
    )
    .ok();
    writeln!(
        out,
        "  --as-of <YYYY-MM-DD>         记录证书的法律基准日（只影响 :cert / :verify-cert，不参与推理）"
    )
    .ok();
    writeln!(
        out,
        "  --jurisdiction <代码>        记录证书的管辖代码（只影响 :cert / :verify-cert，不参与推理）"
    )
    .ok();
    writeln!(
        out,
        "  --no-default-packs           不加载默认环境（与 --profile 互斥；显式 import 仍可用）"
    )
    .ok();
    writeln!(
        out,
        "  --allow-community-packs      允许 profile 包含非官方信任级别的包"
    )
    .ok();
    writeln!(out).ok();
    writeln!(
        out,
        "证书命令为 :verify-cert <证书文件> [目标命题]（先校验环境身份）；\
         原来的 :check 已改名。"
    )
    .ok();
    writeln!(
        out,
        "--as-of / --jurisdiction 只写进证书环境身份，:verify-cert 比对同值；不参与推理。"
    )
    .ok();
}

fn print_version(out: &mut impl Write) {
    writeln!(out, "std-deduce {}", env!("CARGO_PKG_VERSION")).ok();
}

/// Run every argument as a colon command and return the process exit code.
///
/// The worst outcome wins. A command error — including the removed `:check`
/// and an option-looking argument such as `--help` after a file — stops the
/// run and is a usage error (`2`). Options are never silently ignored.
fn run_commands(session: &mut Session, commands: &[String], out: &mut impl Write) -> i32 {
    let mut worst = 0;
    for command in commands {
        match session.handle(command, out) {
            Ok(outcome) => worst = worst.max(outcome.exit_code()),
            Err(error) => {
                eprintln!("错误：{error}");
                return 2;
            }
        }
    }
    worst
}

/// Load one theory file and then run the remaining commands.
///
/// A failed load prints the already-rendered `path:line:col: error: ...` (or
/// `path: error: ...`) on stderr and exits `1`: the file did not pass its
/// checks, while the invocation itself was well-formed. The load error already
/// names the file, so the batch entry adds no path prefix of its own. Remaining
/// commands are not run.
fn run_batch(session: &mut Session, file: &str, commands: &[String], out: &mut impl Write) -> i32 {
    if let Err(error) = session.load_theory(file, out) {
        eprintln!("{error}");
        return 1;
    }
    run_commands(session, commands, out)
}

/// Run the interactive session on stdin, returning the worst command outcome.
fn run_repl(session: &mut Session, out: &mut impl Write) -> i32 {
    writeln!(
        out,
        "std-deduce {} — 输入 :help 查看命令。",
        env!("CARGO_PKG_VERSION")
    )
    .ok();
    let stdin = io::stdin();
    let mut worst = 0;
    for line in stdin.lock().lines() {
        let Ok(line) = line else { break };
        if line.trim() == ":quit" || line.trim() == ":exit" {
            break;
        }
        if line.trim() == ":help" {
            writeln!(
                out,
                ":load <文件>  :inspect  :given <命题>  :why <命题>  :gap <命题>  \
                 :cert <命题>  :verify-cert <证书文件> [目标命题]  :packs [目录]  \
                 :lock [目录]  :audit [目录]（只核对带 quote 的来源）  :quit"
            )
            .ok();
            continue;
        }
        match session.handle(&line, out) {
            Ok(outcome) => worst = worst.max(outcome.exit_code()),
            Err(error) => {
                writeln!(out, "错误：{error}").ok();
                worst = 2;
            }
        }
    }
    // Interactive mode settles the exit code on the worst command, the same way
    // argv mode does.
    worst
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut out = io::stdout();

    let (options, invocation) = match parse_invocation(&args) {
        Ok(parsed) => parsed,
        Err(error) => {
            eprintln!("错误：{error}");
            std::process::exit(2);
        }
    };

    let code = match invocation {
        Invocation::Help => {
            print_help(&mut out);
            0
        }
        Invocation::Version => {
            print_version(&mut out);
            0
        }
        Invocation::Env => match environment::run_env(&options, &mut out) {
            Ok(()) => 0,
            Err(error) => {
                eprintln!("错误：{error}");
                2
            }
        },
        Invocation::Repl => {
            let mut session = Session::new(options);
            run_repl(&mut session, &mut out)
        }
        Invocation::Commands(commands) => {
            let mut session = Session::new(options);
            run_commands(&mut session, &commands, &mut out)
        }
        Invocation::Batch { file, commands } => {
            let mut session = Session::new(options);
            run_batch(&mut session, &file, &commands, &mut out)
        }
    };
    if code != 0 {
        std::process::exit(code);
    }
}
