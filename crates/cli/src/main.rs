//! Command-line interface.
//!
//! The binary has a batch entry point and a line-oriented session:
//!
//! ```text
//! std-deduce                       start the REPL
//! std-deduce [options] <file> [commands...]
//!                                  load a theory file, then run the commands
//! std-deduce [options] <case.json> [commands...]
//!                                  load a strict JSON case description
//!                                  (the same path as `:load-case`)
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
//! `--allow-community-packs` lowers the trust gate of the selected profile (it
//! never accepts an `official` claim the registry's whitelist does not cover),
//! `--closed-env` enables the closed environment, `--allow-case-rules` lifts
//! its case-declaration check (only together with `--closed-env`),
//! `--interpret <id>` enables one declared interpretation for the session (it
//! may be repeated; two interpretations with kernel-equivalent `to`
//! conclusions are refused), and
//! `--as-of <YYYY-MM-DD>` / `--jurisdiction <code>` set the session's date
//! value (a fallback only when a judged instance has no event time) and
//! jurisdiction code; `:asof` / `:jurisdiction` print or replace
//! the same session values and report whether they came from the command line
//! or a session command. They are stamped into a `:cert` certificate and
//! compared exactly by `:verify-cert`. `:jurisdiction` is the case's legal
//! system in the applicability judgement; `:asof` is only a fallback when the
//! judged rule instance references no fact with an occurrence time. If the
//! loaded rules name two or more jurisdictions and the session has no
//! jurisdiction, `:why` / `:explain` / `:review` / `:cert` refuse with exit
//! `2` instead of silently picking one; `:gap`, `:issues`, `:applicability`
//! and `:inspect` are not gated.
//!
//! Rule scope (`effective` / `repealed` / `jurisdiction` / `territory`) and a
//! fact's occurrence (`occurred_at` / `occurred_in`) are judged before a rule
//! instantiates: the reference point is the event time/place of the premise
//! facts the instance consumes, not the query date. Every event time must be
//! inside the range and every event place inside the territory; all-out is
//! inapplicable and partial coverage is undecidable, never rounded. A rule
//! that does not apply is never applied; a rule with partial coverage is also
//! never applied (the evidence says it does not wholly govern the instance),
//! while a rule judged *unchecked* (no evidence at all) keeps firing and every
//! conclusion line it produces carries `适用性未判定（…）`. The verdict and
//! the event times/places it relied on are printed on the conclusion line; a
//! gap's candidates are listed by `:gap` and `:applicability`. Certificate v8
//! records the verdict, its basis and its reason on every rule application and
//! gap candidate, and `:verify-cert` recomputes it from the environment
//! declaration and the certificate's own inputs.
//!
//! In the closed environment a top-level `:load` accepts only a case file (no
//! `namespace`): modules are legal packs and must be imported. The case may
//! state facts (`obj`, `axiom`) and query, but by default it may not declare
//! `sort`/`pred`/`def`/`rule`/`contrary`/`unique`/`open`, and its facts may not
//! smuggle a concept through their type: an object must be declared at a sort
//! from a loaded pack (not `Prop`, `Type` or a function type), and an axiom's
//! type must be a proposition. The error names what was rejected and points at
//! `--allow-case-rules`. With that flag the declarations load and are recorded
//! as case extensions: `:inspect` marks them ` [案件扩展]` (including an object
//! or axiom whose type invented a concept), and a certificate that applies a
//! case rule records one `local-extension` open obligation, so `:why` and
//! `:verify-cert` report that a human must judge the result instead of claiming
//! an unqualified proof. A name the loaded packs do not define gets a
//! closed-environment hint instead of being invented for the case. Without
//! `--closed-env` a case file behaves exactly as before and no extension is
//! recorded.
//!
//! A JSON case description (`:load-case`, or the batch entry when the file ends
//! in `.json`) is a strict, versioned document (`schema_version = 1`). It is
//! untrusted input: it may only bring facts, identities, sources, occurrence
//! records, individual constants and goals, and a rule/predicate/interpretation/
//! risk/priority field is refused outright. All fields are checked before the
//! session is touched; proposition text goes through the existing parser and
//! elaborator. Diagnostics name the JSON path (`facts[2].identity`), one bad
//! entry rejects the whole file, and a `reference` value that disagrees with an
//! explicitly set session date or jurisdiction is an error rather than an
//! overwrite. Imports, the default environment and the closed environment use
//! the same path as `:load`. A batch JSON load exits `2` on any read, syntax or
//! validation failure (the same command-error code `:load-case` uses; the
//! existing `.std` batch load failure stays `1`) and `0` on success; goals are
//! only checked and listed, so an unproved goal never makes the load exit `1`.
//!
//! When the current directory contains `lawpacks/profiles` with a
//! `default = true` profile, the first theory load prepares that environment
//! lazily: the profile is validated, its packs are checked against the lock,
//! version constraints and trust level, and they are loaded before the file.
//! A failed preparation fails the load. `--no-default-packs` turns this off
//! without affecting explicit imports; `--profile` selects a profile by name or
//! alias. The preload lines are printed only after the whole load commits, so a
//! failed file never claims that the environment loaded. The profile and the
//! packs it loaded are session objects, but a certificate v8 records the
//! environment identity it was produced in: the profile, the as-of date, the
//! jurisdiction code and the loaded packs/corpora. `:cert` stamps it before
//! writing, and `:verify-cert` compares it with the current environment before
//! running the proof layers.
//!
//! Interpretations are off by default. `:interpret list` shows every declared
//! interpretation with its state; `enable`/`disable` change the session set,
//! which is the same set `--interpret` builds. When enabled, an interpretation
//! applies once to a registered fact or rule conclusion: `from` must already
//! hold, and its `to` becomes a fact in that query. It is a separate
//! `interpretation_application` certificate step, never a rule; it does not
//! trigger rules and cannot consume another interpretation's conclusion, so
//! there is no interpretation chain. A `:gap` or `:why` that is only missing an
//! unenabled interpretation prints `存在未启用解释 ...` instead of leaving the
//! declaration invisible.
//!
//! Universal elimination is demand-driven. A `Fact` declaration whose type is a
//! telescope of named `∀` binders ending in a predicate-headed proposition can
//! be instantiated with closed values: a queried goal that no rule or fact
//! proves demands one instance, and a rule premise that is already closed under
//! the bindings collected so far demands one during saturation. Every instance
//! is a derived `axiom_instance` step in certificate v8, never an assumption;
//! `:why` prints the universal fact, its identity and the binding, and
//! `:verify-cert` recomputes the conclusion from the declaration. `:gap` lists
//! the universal facts that unify with a goal, with the values an instance
//! would need and the reason it was refused. The bounds are explicit: at most
//! 64 universal facts are tried per goal, 1024 instances are derived per query
//! and 4096 distinct goals are probed; exceeding one is an error, never a
//! silently truncated derivation. Existential quantifiers, polymorphism and
//! higher-order instantiation of function-typed facts are not implemented.
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
//! :inspect                dump the ledger, including recorded scope and occurrence
//! :asof [date]            show or set the session's legal as-of date
//! :jurisdiction [code]    show or set the session's jurisdiction code
//! :interpret [list]       list declared interpretations and their state
//! :interpret enable <id>  enable one interpretation for later queries
//! :interpret disable <id> disable it again (the default is off)
//! :why <term>             derive, print the certificate's tree, and check it
//! :explain <term>         derive, print a Chinese because-so explanation, and
//!                         check the same certificate
//! :labels <term>          derive and print the certificate's full trust labels
//!                         with their evidence
//! :gap <term>             explain what is missing, as a recursive gap tree
//! :issues                 list every conclusion the current facts can contest
//! :applicability [term]   list temporal/spatial verdicts: every rule, or the
//!                         rules the goal's derivation or gap tree uses
//! :cert <term>            derive and print the goal's certificate JSON
//! :verify-cert <file> [goal]
//!                         check a certificate, optionally bound to a goal
//! :packs [dir]            list the legal-pack manifests under a directory
//! :lock [dir]             hash the packs and write the std.lock registry lock
//! :audit [dir]            check rule-source quotations against article corpora
//! :given <term>           register a fact asserted by the user
//! :fact [list]            list the facts in the ledger with their identities
//! :fact show <term>       show the facts equivalent to a proposition
//! :fact add <term>        register a fact asserted by the user
//! :fact assumed <term>    register a fact assumed for the analysis
//! :fact disputed <term>   register a fact disputed by the other side
//! :fact verified <term> / :fact stipulated <term>
//!                         refused: those identities only come from case files
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
//! itself contributed, ` [案件扩展]` for a closed-environment case's own legal
//! concepts, and still `[ns]` for a namespaced module loaded directly from a
//! file.
//!
//! `:packs` reads manifests but imports nothing and does not require a loaded
//! theory. With no argument it scans `lawpacks` in the current working
//! directory; with an argument that whole string is the directory, so a path
//! containing spaces works without further quoting. Only direct child
//! directories containing a regular `lawpack.toml` are packs; symbolic links
//! and pack directories that resolve outside the root are errors. Each valid
//! pack is printed on one line with its effective range and trust level — the
//! level's label says whether this project audited the release: an `official`
//! claim reads `official（本项目审核）` only when the whitelist confirms it and
//! `official（未通过白名单核对）` otherwise, while the lower levels are marked as
//! unaudited — then the maintainers, the review record of a reviewed release,
//! the description behind a fixed `  说明：` prefix, the file count and, for an
//! `official` claim, the official-whitelist verdict. A manifest may link an
//! article corpus as `<law-id>/<version>`; `:packs` reads
//! `<registry-parent>/law/corpus/<law-id>/<version>.json` and prints its
//! coverage counts and named ontology gaps. A missing or invalid linked corpus
//! is printed as a diagnostic and fails the command. An invalid manifest is
//! printed as `path：error` and makes the command fail (exit `2`); valid packs
//! are still printed. Descriptions, paths and errors are escaped first, so a
//! newline or terminal escape sequence cannot forge another line. A root with
//! no packs prints a "not found" line and succeeds.
//!
//! In the same directory, `:packs` looks for `std.lock` and `official.toml`.
//! When the lock is there, every pack is hashed and checked against it before
//! the listing is printed: a match prints `锁定校验：通过（N 个包）`, while a
//! missing, changed, extra or differently versioned pack prints every lock
//! error and makes the command exit `2`; no per-pack whitelist verdict is
//! printed then, and an `official` claim still reads
//! `official（未通过白名单核对）`. An `official` claim is honoured only when
//! `official.toml` lists the pack's name, version and locked hash; that prints
//! `白名单：通过（official.toml）`. A missing whitelist, an unlisted release and a
//! hash mismatch print a per-pack `path: error: ...` line, and an `official.toml`
//! that cannot be read or validated prints one `path: error: ...` line of its
//! own; every one of them makes the command exit `2`. A pack below `official`
//! does not have to be listed by the whitelist, but a broken `official.toml` is
//! still a registry error that fails the whole listing. Without a lock the
//! command prints `锁定校验：未找到 std.lock（未锁定）` and keeps the listing's
//! outcome, except for an `official` claim, which then has no hash to check and
//! fails with a per-pack error. If the listing itself found manifest errors,
//! lock verification is skipped and reported as `锁定校验：未运行（清单错误）`, so
//! one bad manifest is reported once and the listing's exit code stands.
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
//! * a conflict — an unresolved conclusion, or one on the losing side of a
//!   defeated conflict, prints both derivations and exits non-zero; the
//!   winning side of a defeated conflict is a proved conclusion, and its
//!   recorded basis is printed as `依据：` notes.
//!
//! A certificate that fails either layer is an error (exit `2`), never a
//! successful query. A conclusion caught in an unresolved conflict is kept out
//! of the fact base, but it is never dropped silently: `:why` states the
//! recorded reason — no declared priority, priorities that do not decide
//! (listing every declared edge and its source), unresolvable witnesses, two
//! strict facts, two claims, or a claim facing a rule conclusion
//! (`non_strict_fact`, naming the claim's identity). A defeated conclusion gets
//! the recorded basis as `依据：` lines: a strict fact (whose identity the
//! winning side shows), or the declaration (or rule clause) and its source.
//! When the
//! environment's own priority declarations contain a cycle, `:why` and `:gap`
//! print one warning line before their result: an edge inside a cycle cannot
//! decide anything, and the warning does not change the exit code.
//!
//! After the derivation, every rule application's conclusion line carries its
//! applicability verdict and the event times/places behind it (after
//! `⟨rule⟩`): an unchecked verdict says `适用性未判定（…）`, a clean one
//! `适用（事件时间 …）`. An inapplicable or undecidable rule cannot appear
//! because it never fired (`:gap` and `:applicability` show it, with the
//! latter also listing gap candidates). The same annotation is printed on each
//! conflict side's tree.
//!
//! `:explain` uses exactly the same derivation and prints
//! [`std_deduce_cert::render_narrative`] instead of the formal tree; the same
//! certificate is then checked by both layers, and the `0`/`1`/`2` outcomes
//! match `:why`, including the same inline applicability annotations on its
//! conclusion sentences. A fact always carries
//! its recorded identity (`据用户陈述`,
//! `根据法院查明`, `作为分析假设`, `双方无争议`), a step keeps its source and
//! parameter bindings, a conflict is reported as decided or as `此处未决` with
//! its recorded reason, and a gap lists its candidates, missing premises and
//! `unless` blockers. Each missing-premise and blocked sentence also states the
//! candidate rule's declared burden/standard in plain words (for example
//! `这条证据由主张方提出，标准是优势证据`); an undeclared value is written out
//! as `未声明举证责任` / `未声明证明标准`, never defaulted, and the standard is
//! only a label. The 【未决义务】 section repeats the same values for a
//! missing-premise obligation. A source the certificate does not record is
//! printed as `证书未记录来源`, never omitted or filled in. The narrative owns the whole
//! conflict report, so `:explain` does not append the terse `:why` conflict
//! lines, the `注：…` defeat note or its `依据：` lines afterwards. `:why` still
//! prints the formal tree, so the certificate remains expandable; `:cert` JSON
//! is unchanged.
//!
//! `:why`, `:explain` and `:labels` print the certificate's trust labels.
//! The labels are a derived view of the certificate's own fields (`root` and
//! its reachable proof graph, assumption identities, interpretation
//! applications, conflicts and open obligations), computed by
//! `std_deduce_cert::derive_trust`; no renderer guesses one from printed text
//! and no label is stored in the certificate. `:why` and `:explain` print the
//! one-line summary next to their result line (after a proved result, before a
//! unresolved or defeated conflict report), and `:labels` prints the same
//! summary plus every applicable label and its evidence. The five labels are
//! `已验证`, `依赖假设`, `事实待举证`, `争点未决` and `需律师判断`; a gap root
//! is never `已验证`, an unresolved conflict always makes `争点未决` appear,
//! and `需律师判断` comes from an open concept, a human-judgement obligation or
//! a case extension — never from an unresolved conflict alone, so the two
//! labels can appear together. Only records attached to the root's reachable
//! proof graph count; an unrelated conflict or case extension elsewhere in the
//! certificate does not change the root's label. `已验证` says only that the
//! certificate proves the root under strict facts and leaves no root-relevant
//! obligation — it is not a claim that the conclusion is legally correct.
//! `:cert` JSON is unchanged: the labels are not a certificate field and the
//! format stays v8.
//!
//! `:review` uses the same certificate and the same two proof layers as
//! `:why`, then renders a Markdown review report from the certificate, the
//! reasoner's gap trees, the rules' burden/standard declarations and the trust
//! labels. It adds no inference of its own, never changes `:why` / `:cert`
//! output, and is not legal advice. The report is written to stdout, or to a
//! file with `--out` (the path is printed and the file is written through a
//! temporary file, so a failed write leaves no partial report). Its exit code
//! is `:why`'s; the sections and their ordering are documented in `README.md`.
//! `:why`, `:explain` and `:labels` also report the **risk themes** of the
//! case. A theory marks a predicate with `risk <类别> <谓词>` (刑事, 人身安全,
//! 重大财产, 临近期限, 涉外或移民); a proposition on the root's proof graph
//! whose kernel predicate head carries such a marker makes the derivation
//! high-risk. `:why` and `:explain` then print exactly one
//! `高风险题材：涉及…；建议尽快咨询执业律师。` line followed by one
//! `  依据：…` line per proving node (the proposition, the theme, the declaring
//! `risk` line, and the rule/axiom/interpretation with its recorded sources);
//! `:labels` prints the same themes as a separate `题材风险（次标签…）` section.
//! A low-risk derivation prints nothing, so a clean case gets no noise. The
//! theme is a second label and is never merged into `需律师判断`: that trust
//! label says why the model may not decide, the theme says what the case is
//! about. The grading is structural, never a keyword match on printed
//! propositions, and `:inspect` shows `〔风险 <类别>〕` next to the marked
//! predicate and the `risk` marker's own ledger entry. The report is derived
//! from the certificate, is never written into it, and does not change any
//! exit code: `:cert` JSON, certificate v8 and `:verify-cert` are unchanged.
//!
//! A theory that declares no `risk` covering the derivation shows no grading —
//! and most theories declare none. So `:why` and `:explain` print one
//! `提示：案情中出现「…」相关用语，可能属于…题材，但本案没有声明 risk；这只是提示，不改变标签、不改退出码。`
//! sentence when the root graph's propositions mention a term from a small
//! documented word list and no declaration matched. That sentence is explicitly
//! not a judgment: it never says `高风险题材`, it names no rule and no source,
//! `:labels` never prints it, and it changes no label, no exit code and no
//! certificate field. The list lives in `std_deduce_cert::risk::HINT_TERMS` and
//! in the README; it is not a classifier, and an ambiguous term (拘留) keeps the
//! `可能属于` wording instead of becoming a verdict.
//!
//! Every result output of `:why`, `:explain`, `:labels` and `:cert` carries the
//! one-line disclaimer `声明：这是模型内推导，不是法律意见。` as its own line.
//! It is never placed inside the derivation tree and never inside the
//! certificate JSON; `:cert` prints it, plus the privacy notice
//! `证书包含案件原文，可能含个人信息，分享前请自行处理`, before the JSON, so the
//! certificate bytes from the first `{` on are unchanged.
//!
//! `--redact` (or the session command `:redact on|off`) is display-layer
//! redaction: every printed line except `:cert`'s certificate JSON replaces the
//! declared individual names (`obj`, or an `axiom` constant of a sort) with the
//! stable placeholders `甲1`, `甲2`, … assigned in declared-name order. Source
//! text, labels and notes are rewritten too, so a name cannot leak through a
//! citation, and every redacted command output ends with
//! `输出已脱敏；证书未脱敏。…`. Redaction changes display only: a verdict, an
//! exit code, the derivation and the certificate content are identical with it
//! on or off. Silently redacting the certificate is not offered: `:verify-cert`
//! re-checks the recorded words, so a redacted certificate could no longer be
//! verified.
//!
//! `:why` and `:explain` also report the `open` concept marker. A rule step
//! whose conclusion head is an open predicate, or a root that is one, makes the
//! derivation depend on a human judgement: the certificate records one
//! `open_concept` obligation (stable id `open-concept`, a description naming the
//! concept, and the direct dependency nodes), `:why` prints
//! `  此处需人判断：`<concept>`` after the derivation and `:explain` prints it
//! after the conclusion. Such a query exits `1` and never prints
//! `推导已通过独立校验。`. The judgement follows the root's proof graph only:
//! an open concept derived on an unrelated branch, or one merely supplied as a
//! fact, does not reach the root. The candidate interpretations and branch
//! re-runs this marker will eventually drive are not implemented yet.
//!
//! `:gap` prints a recursive gap tree: every candidate rule names the premises
//! it is missing and the blocking conditions that already hold, and every
//! missing premise is expanded into its own gap — the rules that could conclude
//! it, in turn — until the branch reaches a proposition no rule concludes, a
//! proposition in an unresolved conflict or a decided loser, an open rule
//! pattern, a non-proposition, or a proposition already being expanded on the
//! same path (a rule cycle). Repeated expansions are recognised by a structural
//! key of the normalised proposition, never by printed text, so an alpha
//! variant cannot start a second, endless branch; the head match is normalised
//! too, so a `def` alias finds the rule that concludes its definition. Every
//! candidate line carries its per-instance verdict and evidence:
//! `〔适用（事件时间 …）〕`, `〔不适用（原因）〕`, `〔适用性未判定（原因）〕` or
//! `〔适用性无法判定（原因）〕`. An excluded candidate is still listed, with
//! its missing premises but no deeper expansion (adding a premise cannot make
//! an excluded rule fire); an undecidable one also points at the missing
//! explicit reference time, which this version does not offer yet. Only an
//! unchecked candidate is expanded further.
//! Every missing-premise line states the rule's declared burden and standard
//! (`〔举证：主张方 / 优势证据〕`), and every `unless` blocker line states the
//! exception group (`〔例外举证：相对方 / 清楚可信〕`). An undeclared value is
//! printed as `未声明举证责任` / `未声明证明标准`, never replaced by a default;
//! the standard is a label and is never given a number. `:issues` renders the
//! same gap tree, so it carries exactly the same annotations.
//! The recursion is bounded by explicit limits — depth 6, 128 nodes, 8 attempts
//! per rule — and a limit that stops a branch is printed as `已截断：…` where it
//! applies. `:issues` requires a loaded theory and runs the same machinery over
//! the whole fact set instead of one goal: it instantiates every rule over the
//! declared constants, lists each conclusion that is not already proved (and
//! each side of an unresolved conflict) with its own gap tree, reports rules it
//! could not instantiate, reports rules the applicability judgement excluded,
//! and caps the list at 32 conclusions. A conflict the
//! theory already decided is not an open issue: its winner is in the fact base
//! and its loser is reported by `:gap`/`:why` as decided, never as unresolved.
//! Neither command touches the certificate format.
//!
//! `:applicability [term]` is a report, not a query: with no argument it judges
//! every rule as an empty instance (declarations plus `:asof` when set); with
//! a goal it lists the per-instance verdicts of the rules the goal's derivation
//! or gap tree uses. Each line is `⟨rule⟩：` followed by the verdict and the
//! event times/places it relied on (`适用（事件时间 …）`, `不适用（…）`,
//! `适用性未判定（…）` or `适用性无法判定（…）`). It always exits `0`, because
//! "this rule does not apply" is information.
//!
//! `:cert` requires a loaded theory and writes only the certificate JSON to
//! stdout; a gap becomes a `MissingPremise` obligation, an unresolved
//! conflict becomes an `UnresolvedConflict` obligation, and a root derivation
//! that turned an `open` concept into a proved proposition becomes one
//! `open_concept` obligation in that JSON. Version 7 also records one
//! temporal/spatial applicability record per rule application and per gap
//! candidate: the verdict, the reference event times/places, the rule's
//! declared scope, the session fallback actually used and the reason code with
//! its explanation. Each assumption records the environment fact's
//! `occurred_at` / `occurred_in` as an explicit value or `null`. Before
//! serialization the certificate is stamped with the environment identity:
//! the canonical profile name, the session's as-of date and jurisdiction code
//! (from `--as-of`/`--jurisdiction` or `:asof`/`:jurisdiction`; explicit `null`
//! when never set), every loaded pack's version, lock hash and trust level, and
//! the hash of every corpus file a loaded pack links. An identity error writes
//! no JSON; the argv entry points report it on stderr, while the REPL keeps its
//! convention of reporting command errors on stdout.
//!
//! `:verify-cert` requires a loaded theory and first compares the
//! certificate's recorded environment identity with the current one. A
//! certificate that records nothing cannot be compared, and any difference
//! fails the check before either proof layer runs: the differences are printed
//! one per line, the four proof lines say they did not run, and the process
//! exits `2`. A passing environment line is followed, when the certificate
//! records a pack below `official` trust, by one indented `注意：证书记录了非官方包：`
//! line naming every such pack and its level; the warning changes neither the
//! exit code nor the four proof lines. Only an environment match reaches the
//! two layers, in order:
//!
//! 1. [`std_deduce_cert::check`] rebuilds every rule instance, recomputes the
//!    applicability record of every rule application and gap candidate from
//!    the rule's environment declaration and the certificate's own inputs,
//!    checks the recorded `unless` conditions and the root's conflict status;
//!    a mismatch, a missing record or a record that was added to the wrong
//!    place fails here and names the node and field. The logical line reports
//!    how many applicability records were recomputed;
//! 2. [`std_deduce_cert::kernel_proof`] turns the monotone skeleton into
//!    kernel terms and has the kernel check every step.
//!
//! The two layers are printed separately, together with the side conditions
//! and whether a human must decide something. The side-condition line reports
//! how many recorded priority edges the logical layer compared with the
//! environment (`优先关系已核验（n 条边）`) or that the certificate records
//! none (`没有记录优先关系`), so a defeat is never presented without the
//! evidence that its declaration was checked. A priority cycle in the current
//! environment adds one warning line after it; the warning changes no exit
//! code. An `open_concept` obligation is recomputed from the environment's
//! markers and the proof graph rather than trusted: a certificate that dropped,
//! invented or edited it fails the logical layer (exit `2`). When it passes,
//! one `  此处需人判断：`<concept>`` line names the concept after the
//! `需人判断：` summary. A certificate that records a
//! `local-extension` obligation (its proof applied a rule the case file
//! declared) gets one `  本地扩展：...` line after the four report lines and
//! before any goal binding, and counts as an open obligation. The process exits
//! `0` only when both layers pass, the root is proved and nothing is left open;
//! `1` when both layers pass but the root is a gap, an open obligation remains
//! or a recorded conflict is unresolved; and `2` when the file cannot be read
//! or parsed, or either layer fails. A logical pass with a kernel failure is
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

mod case;
mod environment;
mod identity;
mod packs;
mod review;

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::io::{self, BufRead, Write};
use std::path::{Path, PathBuf};

use std_deduce_lang::ast::Item;

use std_deduce_cert::{
    derive_risk, derive_trust, render_narrative_with_context, render_with_annotations, Certificate,
    CheckReport, EnvironmentDifference, EnvironmentIdentity, EnvironmentRecord, KernelProofReport,
    Node as CertNode, ObligationKind, OpenObligation, PriorityClause, PriorityEdge, PriorityOrigin,
    ResolutionBasis, RiskReport, Source, TrustLabel, TrustLevel, TrustReport,
    LOCAL_EXTENSION_OBLIGATION_ID,
};
use std_deduce_kernel::conv::convertible;
use std_deduce_kernel::env::{escape_control, Ctx, Decl, DeclKind, Env, FactIdentity, SourceRef};
use std_deduce_kernel::meta::{validate_date, validate_jurisdiction_code, Scope, ScopeOrigin};
use std_deduce_kernel::pretty::print_expr;
use std_deduce_kernel::{check, Expr, Name, RuleDecl};
use std_deduce_lang::module::escape_path;
use std_deduce_lang::{elab, Library, LoadOptions, LoadReport};
use std_deduce_lawpack::corpus::{self, Audit, Citation, Corpus, CoverageStatus};
use std_deduce_lawpack::{
    read_whitelist, AuditStatus, PackError, PackInfo, Trust, Whitelist, LOCK_FILE, MANIFEST_FILE,
    OFFICIAL_FILE,
};
use std_deduce_reason::{
    certificate as reason_certificate, Applicability, Conflict, Derivation, GapLimit, GapLimits,
    GapStatus, GapTree, Node as ReasonNode, Provenance, Reasoner, Resolution, Side,
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

/// A buffer for one command's printed output, so display redaction can rewrite
/// the whole text in one pass instead of a chunk at a time.
///
/// `String` is not an [`std::io::Write`], so the buffer collects bytes and
/// converts once at the end. Every write goes through `writeln!` with UTF-8
/// strings, so the conversion cannot fail; if it ever did, that is an internal
/// error rather than silently lossy output.
#[derive(Default)]
struct OutputBuffer {
    bytes: Vec<u8>,
}

impl OutputBuffer {
    fn into_text(self, command: &str) -> Result<String, String> {
        String::from_utf8(self.bytes)
            .map_err(|error| format!("命令 `:{command}` 的输出不是有效 UTF-8（内部错误）：{error}"))
    }
}

impl Write for OutputBuffer {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.bytes.extend_from_slice(buf);
        Ok(buf.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

/// The short statement every user-facing result output carries once.
///
/// It is printed as its own line after the derivation tree, the trust line and
/// any warning, never inside the tree and never inside the certificate JSON:
/// the certificate is a proof artifact whose bytes must stay reproducible.
const DISCLAIMER_LINE: &str = "声明：这是模型内推导，不是法律意见。";

/// The notice appended to every redacted command output.
///
/// It states both halves of the boundary: the display was redacted, the
/// certificate was not. The individual names are replaced everywhere the text
/// mentions them, including source text, labels and notes.
const REDACT_NOTICE: &str =
    "输出已脱敏；证书未脱敏。个体名已替换为占位符（甲1、甲2…），来源与标签文本同样替换。";

/// The `:cert` explanation lines printed before the JSON.
///
/// The certificate keeps the original text (its propositions, sources and
/// assumption labels) because `:verify-cert` re-checks the words the derivation
/// used: a redacted certificate could no longer be verified. The reader is told
/// so before the JSON, and the JSON itself gains no field (certificate v8).
const CERT_NOTICE: [&str; 2] = [
    "说明：这是模型内推导，不是法律意见。",
    "说明：证书包含案件原文，可能含个人信息，分享前请自行处理；证书不脱敏（:verify-cert 需要原文复核）。",
];

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
/// `--help` and `--version` only work as the sole argument. A batch file whose
/// extension is `.json` is a case description; the load stage chooses the
/// parser by that extension, not here.
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
            "--closed-env" => {
                options.closed_env = true;
                index += 1;
            }
            "--interpret" => {
                let value = invocation_value(args, index, "--interpret", "--interpret <解释名>")?;
                if options.interpretations.contains(&value) {
                    return Err(format!(
                        "用法错误：--interpret `{}` 重复启用",
                        escape_path(&value)
                    ));
                }
                options.interpretations.push(value);
                index += 2;
            }
            "--allow-case-rules" => {
                options.allow_case_rules = true;
                index += 1;
            }
            "--redact" => {
                options.redact = true;
                index += 1;
            }
            _ => break,
        }
    }
    if options.profile.is_some() && options.no_default_packs {
        return Err("用法错误：--profile 与 --no-default-packs 不能同时使用".to_owned());
    }
    if options.allow_case_rules && !options.closed_env {
        return Err("用法错误：--allow-case-rules 需要同时给 --closed-env".to_owned());
    }

    let rest = &args[index..];
    let Some(first) = rest.first() else {
        return Ok((options, Invocation::Repl));
    };
    match first.as_str() {
        "check" => {
            let Some(file) = rest.get(1) else {
                return Err("用法：std-deduce check <文件.std|文件.json> [命令...]".to_owned());
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

/// Where the session's recorded as-of date or jurisdiction came from.
///
/// The value itself lives in the environment so `:cert` and `:verify-cert`
/// read exactly one source; this only records whether the process arguments or
/// a session command set it, which `:asof` / `:jurisdiction` report.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SessionValueSource {
    CommandLine,
    SessionCommand,
    /// The value came from a loaded JSON case description's `reference`
    /// object. It is an explicit case value, not a default.
    CaseFile,
}

impl SessionValueSource {
    fn label(self) -> &'static str {
        match self {
            SessionValueSource::CommandLine => "命令行",
            SessionValueSource::SessionCommand => "会话命令",
            SessionValueSource::CaseFile => "案件",
        }
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
    /// Declarations top-level case files contributed while the closed
    /// environment allowed case-local rules, by name, with the declaration's
    /// kind label (`rule`, `pred`, ...). Empty outside the closed mode, so
    /// `:inspect` and certificates are unchanged there.
    case_extensions: BTreeMap<String, &'static str>,
    /// The lazily prepared default legal environment.
    environment: environment::Environment,
    /// Where the session's as-of date came from; `None` when no value is set.
    as_of_source: Option<SessionValueSource>,
    /// Where the session's jurisdiction came from; `None` when no value is set.
    jurisdiction_source: Option<SessionValueSource>,
    /// The interpretations the session enabled, by declaration id. Empty is
    /// the default: every interpretation stays inert and output is unchanged.
    enabled_interpretations: BTreeSet<String>,
    /// Display-layer redaction: when set, every printed line except the
    /// certificate JSON of `:cert` replaces declared individual names with
    /// stable placeholders. It changes display only: no verdict, exit code,
    /// certificate field or redacted-off output depends on it.
    redact: bool,
}

impl Session {
    fn new(options: environment::Options) -> Self {
        let as_of_source = options
            .as_of
            .as_ref()
            .map(|_| SessionValueSource::CommandLine);
        let jurisdiction_source = options
            .jurisdiction
            .as_ref()
            .map(|_| SessionValueSource::CommandLine);
        let enabled_interpretations = options.interpretations.iter().cloned().collect();
        let redact = options.redact;
        Session {
            lib: Library::new(),
            loaded: false,
            packs: Vec::new(),
            case_extensions: BTreeMap::new(),
            environment: environment::Environment::new(options),
            as_of_source,
            jurisdiction_source,
            enabled_interpretations,
            redact,
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

    /// Build a reasoner with the session's enabled interpretations and its
    /// legal as-of date and jurisdiction.
    ///
    /// The two session values are reference values of the applicability
    /// judgement: a rule that records an effective range, jurisdiction or
    /// territory is compared with them before it may fire. They still never
    /// filter a rule by themselves; the judgement and its recorded reasons do.
    fn reasoner(&self) -> Result<Reasoner<'_>, String> {
        let mut reasoner = configured_reasoner(&self.lib.env, &self.enabled_interpretations)?;
        reasoner.set_session_scope(self.environment.as_of(), self.environment.jurisdiction());
        Ok(reasoner)
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
    ///
    /// In the closed environment the file must be a case file, its declarations
    /// are checked before the loader runs, and the legal concepts it adds are
    /// recorded as case extensions once the load commits. A failed load records
    /// nothing, exactly like the cloned library and package list it drops.
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

        // A closed environment accepts case files only, and by default the case
        // may not declare legal concepts of its own. The check runs after the
        // imports resolved, so `import` still works, and before `lib.load`, so a
        // rejected file never enters the ledger.
        if environment.closed_env() {
            check_closed_case_file(
                path,
                &items,
                namespace,
                environment.allow_case_rules(),
                &lib.env,
            )?;
        }
        // The declarations a case file adds are the difference around
        // `lib.load`; capture the existing names before it runs. Only the closed
        // mode records them, so the default session keeps an empty map.
        let existing_names: BTreeSet<String> = if environment.closed_env() {
            lib.env.iter().map(|decl| decl.name.to_string()).collect()
        } else {
            BTreeSet::new()
        };
        let mut case_extensions = self.case_extensions.clone();

        // The case/module file itself is loaded last, after its dependencies.
        // If it fails, the cloned library and package list are dropped and the
        // pending preload report is never printed. Only the closed environment
        // with `--allow-case-rules` marks this file's rules as case-local; a
        // package's theory files are loaded by the package loader with the
        // manifest's scope instead.
        let load_options = LoadOptions {
            pack_scope: None,
            case_local: environment.closed_env() && environment.allow_case_rules(),
        };
        let report = match lib.load_with_options(path, &src, &load_options) {
            Ok(report) => report,
            Err(error) => {
                let error = error.render(path);
                let error = environment.annotate_error(error, &imports);
                return Err(environment.annotate_closed_error(error));
            }
        };
        // Interpretations named by `--interpret` or an earlier `:interpret
        // enable` must still exist in the environment that was just loaded.
        // Validating before the commit means a rejected setting leaves the
        // session exactly as it was.
        if !self.enabled_interpretations.is_empty() {
            configured_reasoner(&lib.env, &self.enabled_interpretations).map_err(|error| {
                format!("已启用的解释无法在当前环境解析：{error}（--interpret / :interpret enable 设置）")
            })?;
        }
        if environment.closed_env() {
            record_case_extensions(&lib, &existing_names, &mut case_extensions);
        }
        self.lib = lib;
        self.packs = loaded_packs;
        self.case_extensions = case_extensions;
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

    /// Load a strict JSON case description into the session.
    ///
    /// The document is parsed and field-checked before the session is touched,
    /// so a malformed file cannot prepare the default environment or record
    /// anything. Imports, the default environment and the closed environment
    /// follow the same path as `:load`. The description may only add
    /// individuals, facts, identities, sources, occurrence records and goals;
    /// proposition text is elaborated and type-checked with the existing
    /// parser/elaborator, and one bad entry rejects the whole file.
    ///
    /// Everything runs on cloned session state: a failure anywhere leaves the
    /// session exactly as it was, exactly like a failed `:load`.
    fn load_case(&mut self, path: &str, out: &mut impl Write) -> Result<Outcome, String> {
        if path.trim().is_empty() {
            return Err("用法：:load-case <文件.json>".to_owned());
        }
        let case = case::read(path)?;
        // A case's reference values are session values. An explicit session
        // value is never overwritten by a disagreement: that is an error, not a
        // preference. An equal value is accepted unchanged.
        if let Some(value) = &case.as_of {
            if let Some(current) = self.environment.as_of() {
                if current != value {
                    return Err(case::render(
                        path,
                        "reference.as_of",
                        format!(
                            "案件 JSON 的 as_of `{}` 与当前会话值 `{}` 冲突；不覆盖已显式设置的会话值",
                            escape_control(value),
                            escape_control(current)
                        ),
                    ));
                }
            }
        }
        if let Some(value) = &case.jurisdiction {
            if let Some(current) = self.environment.jurisdiction() {
                if current != value {
                    return Err(case::render(
                        path,
                        "reference.jurisdiction",
                        format!(
                            "案件 JSON 的 jurisdiction `{}` 与当前会话值 `{}` 冲突；不覆盖已显式设置的会话值",
                            escape_control(value),
                            escape_control(current)
                        ),
                    ));
                }
            }
        }

        let mut lib = self.lib.clone();
        let mut loaded_packs = self.packs.clone();
        let mut environment = self.environment.clone();
        let preload = environment.ensure_loaded(&mut lib, &mut loaded_packs)?;

        // Imports resolve exactly like `:load`'s: a namespace this session
        // already loaded from a file is reused, a package is re-checked through
        // the registry, and only the remaining names scan the registry once.
        let pack_names: BTreeSet<&str> =
            loaded_packs.iter().map(|pack| pack.name.as_str()).collect();
        let loaded_namespaces: BTreeSet<&str> = lib
            .theories
            .iter()
            .filter_map(|theory| theory.namespace.as_deref())
            .collect();
        let registry_imports: Vec<String> = case
            .imports
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
        }

        // Ledger names a loaded legal pack declared. In the closed environment
        // a JSON object must be an individual of one of these sorts: a sort the
        // case itself declared with `--allow-case-rules` is a legal concept of
        // the case, and the JSON format never lets a case description introduce
        // a legal concept.
        let pack_decls: BTreeSet<String> = loaded_packs
            .iter()
            .flat_map(|pack| pack.decls.iter().cloned())
            .collect();

        // Every fact already in the environment, so a JSON fact cannot relabel
        // a proposition registered under another identity (the same rule
        // `:given` and `:fact add` enforce).
        let existing_facts: Vec<(Name, Expr, FactIdentity)> = lib
            .env
            .iter()
            .filter_map(|decl| match &decl.kind {
                DeclKind::Fact { identity } => {
                    Some((decl.name.clone(), decl.ty.clone(), *identity))
                }
                _ => None,
            })
            .collect();

        // One diagnostic context for the rest of the load: every case error
        // names the file and the JSON path, then receives the same environment
        // hints a failed `:load` would add.
        let diagnostics = CaseDiagnostics {
            environment: &environment,
            imports: &case.imports,
            file: path,
        };

        let mut declared: Vec<String> = Vec::new();
        for object in &case.objects {
            let type_path = format!("{}.type", object.path);
            let ty = self.case_type(&object.ty, &type_path, &lib.env, &diagnostics)?;
            if !is_pack_sort(&lib.env, &ty) {
                return Err(diagnostics.error(
                    &type_path,
                    format!(
                        "案件对象 `{}` 的类型必须是已加载环境里的一个 sort（例如 `cn.constitution.人`）；\
                         不能是 Prop、Type、函数类型或定义。JSON 不能借对象引入法律概念",
                        escape_control(&object.name)
                    ),
                ));
            }
            if environment.closed_env() {
                let Expr::Const(sort) = &ty else {
                    // `is_pack_sort` already refused every non-sort head; this
                    // arm is unreachable but keeps the closed check total.
                    return Err(diagnostics.error(
                        &type_path,
                        "封闭环境中的案件对象必须使用已加载法律包里的 sort",
                    ));
                };
                if !pack_decls.contains(sort.as_ref()) {
                    return Err(diagnostics.error(
                        &type_path,
                        format!(
                            "封闭环境中的案件对象必须使用已加载法律包里的 sort；`{}` 不是任何已加载包声明的 sort；\
                             即使 --allow-case-rules 也不放行 JSON 对象引入案件本地 sort",
                            escape_control(sort)
                        ),
                    ));
                }
            }
            let decl = Decl {
                name: std_deduce_kernel::name(&object.name),
                kind: DeclKind::Obj,
                ty,
                sources: object.source.clone().into_iter().collect(),
                scope: Scope::default(),
                occurred_at: None,
                occurred_in: None,
                index: 0,
            };
            lib.env.insert(decl, &Ctx::new()).map_err(|error| {
                diagnostics.error(
                    &format!("{}.name", object.path),
                    format!("对象 `{}` 无法登记：{error}", escape_control(&object.name)),
                )
            })?;
            declared.push(object.name.clone());
        }

        let mut next_fact = 1usize;
        let mut written: Vec<(String, Expr, FactIdentity)> = Vec::new();
        for fact in case.facts.iter().chain(case.assumptions.iter()) {
            let proposition_path = format!("{}.proposition", fact.path);
            let prop = self.case_proposition(
                &fact.proposition,
                &proposition_path,
                &lib.env,
                &diagnostics,
            )?;
            if let Some(conflict) = diagnostics.identity_conflict(
                &lib.env,
                &existing_facts,
                &written,
                &prop,
                fact.identity,
                &fact.path,
            )? {
                return Err(conflict);
            }
            let name = next_case_fact_name(&lib.env, &mut next_fact);
            let decl = Decl {
                name: std_deduce_kernel::name(&name),
                kind: DeclKind::Fact {
                    identity: fact.identity,
                },
                ty: prop.clone(),
                sources: vec![fact.source.clone()],
                // A JSON fact records exactly the occurrence it declares. An
                // absent field stays `None`; the session's as-of date is never
                // copied into a fact's event time.
                scope: Scope::default(),
                occurred_at: fact.occurred_at.clone(),
                occurred_in: fact.occurred_in.clone(),
                index: 0,
            };
            lib.env.insert(decl, &Ctx::new()).map_err(|error| {
                diagnostics.error(&fact.path, format!("事实 `{name}` 无法登记：{error}"))
            })?;
            written.push((fact.path.clone(), prop, fact.identity));
            declared.push(name);
        }

        // Goals are checked for syntax and type here, but loading does not
        // prove them: a query does. They are kept in the load report so the
        // producer can see the exact propositions the case named.
        let mut goals: Vec<String> = Vec::new();
        for goal in &case.goals {
            let proposition_path = format!("{}.proposition", goal.path);
            let prop = self.case_proposition(
                &goal.proposition,
                &proposition_path,
                &lib.env,
                &diagnostics,
            )?;
            goals.push(print_expr(&prop));
        }

        // Interpretations enabled by the command line or an earlier session
        // command must still resolve in the environment that was just loaded.
        if !self.enabled_interpretations.is_empty() {
            configured_reasoner(&lib.env, &self.enabled_interpretations).map_err(|error| {
                format!("已启用的解释无法在当前环境解析：{error}（--interpret / :interpret enable 设置）")
            })?;
        }

        let mut as_of_source = self.as_of_source;
        let mut jurisdiction_source = self.jurisdiction_source;
        if let Some(value) = &case.as_of {
            if environment.as_of().is_none() {
                environment.set_as_of(value.clone());
                as_of_source = Some(SessionValueSource::CaseFile);
            }
        }
        if let Some(value) = &case.jurisdiction {
            if environment.jurisdiction().is_none() {
                environment.set_jurisdiction(value.clone());
                jurisdiction_source = Some(SessionValueSource::CaseFile);
            }
        }

        self.lib = lib;
        self.packs = loaded_packs;
        self.environment = environment;
        self.as_of_source = as_of_source;
        self.jurisdiction_source = jurisdiction_source;
        self.loaded = true;
        if let Some(report) = preload {
            write!(out, "{report}").ok();
        }
        self.print_case_load_report(path, &case, &declared, &goals, out);
        Ok(Outcome::Proved)
    }

    /// Elaborate a type expression from a case description.
    fn case_type(
        &self,
        text: &str,
        json_path: &str,
        env: &Env,
        diagnostics: &CaseDiagnostics<'_>,
    ) -> Result<Expr, String> {
        let term = parse_term(text).map_err(|error| {
            diagnostics.error(json_path, format!("类型无法按现有语法解析：{error}"))
        })?;
        let ty =
            elab::elab_top(env, &term).map_err(|error| diagnostics.error(json_path, error.msg))?;
        check::check_is_type(env, &Ctx::new(), &ty)
            .map_err(|error| diagnostics.error(json_path, format!("类型检查失败：{error}")))?;
        Ok(ty)
    }

    /// Elaborate and type-check one proposition from a case description.
    ///
    /// The existing parser and elaborator do the work, so a case and a `.std`
    /// file accept exactly the same proposition syntax. Every failure names the
    /// JSON path of the proposition that failed.
    fn case_proposition(
        &self,
        text: &str,
        json_path: &str,
        env: &Env,
        diagnostics: &CaseDiagnostics<'_>,
    ) -> Result<Expr, String> {
        let term = parse_term(text).map_err(|error| {
            diagnostics.error(json_path, format!("命题无法按现有语法解析：{error}"))
        })?;
        let expr =
            elab::elab_top(env, &term).map_err(|error| diagnostics.error(json_path, error.msg))?;
        check::check(env, &Ctx::new(), &expr, &Expr::Sort(0))
            .map_err(|error| diagnostics.error(json_path, format!("命题类型检查失败：{error}")))?;
        Ok(expr)
    }

    /// Print the declaration ledger of a successful case load.
    ///
    /// The shape follows `:load`: `已加载 …`, one `导入` line per import and
    /// one `+` line per declaration. Facts are listed by their generated ledger
    /// names (`事实N`); `:inspect` shows their propositions, identities,
    /// sources and occurrence records. Goals print after the declarations with
    /// the same `·` marker `:load` uses for shown items.
    fn print_case_load_report(
        &self,
        path: &str,
        case: &case::CaseFile,
        declared: &[String],
        goals: &[String],
        out: &mut impl Write,
    ) {
        let label = case
            .case
            .as_ref()
            .map(|name| format!("（{}）", escape_control(name)))
            .unwrap_or_default();
        writeln!(out, "已加载案件 `{}`{}。", escape_path(path), label).ok();
        for name in &case.imports {
            let marker = self
                .environment
                .import_marker(name, &self.packs)
                .unwrap_or_default();
            writeln!(out, "  导入 {name}{marker}").ok();
        }
        for name in declared {
            writeln!(out, "  + {name}").ok();
        }
        let counts = case.identity_counts();
        if !counts.is_empty() {
            let summary = counts
                .iter()
                .map(|(identity, count)| format!("{} {count}", identity.label_zh()))
                .collect::<Vec<_>>()
                .join("、");
            writeln!(out, "  事实身份：{summary}").ok();
        }
        for goal in goals {
            writeln!(out, "  · 目标 {goal}").ok();
        }
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

    /// Run one command line and return its outcome.
    ///
    /// A bare line is treated as a colon command. With display redaction on,
    /// every line the command prints is buffered and rewritten once with the
    /// session's placeholder mapping, and a one-line notice is appended; the
    /// `:cert` command is exempt because its JSON *is* the certificate and must
    /// stay reproducible. An error message is redacted the same way, so no path
    /// can leak a name the user asked to hide. The decision is made once, when
    /// the command starts: `:redact off` therefore also finishes its own output
    /// under the old state.
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
                "它不是命令；查询请用 :why / :gap / :issues",
            ));
        }
        let command = if line.starts_with(':') {
            line.to_owned()
        } else {
            format!(":{line}")
        };
        let rest = command.strip_prefix(':').unwrap_or(&command);
        let (cmd, arg) = rest.split_once(char::is_whitespace).unwrap_or((rest, ""));
        let arg = arg.trim();
        if self.redact && cmd != "cert" {
            let mut buffer = OutputBuffer::default();
            let result = self.dispatch(cmd, arg, &mut buffer);
            let text = buffer.into_text(cmd)?;
            let mut text = self.redact_text(&text);
            if !text.is_empty() {
                text.push_str(REDACT_NOTICE);
                text.push('\n');
            }
            write!(out, "{text}").ok();
            return result.map_err(|error| self.redact_text(&error));
        }
        self.dispatch(cmd, arg, out)
    }

    /// Dispatch an already split colon command.
    fn dispatch(&mut self, cmd: &str, arg: &str, out: &mut impl Write) -> Result<Outcome, String> {
        match cmd {
            "load" => self.load_theory(arg, out),
            "load-case" => self.load_case(arg, out),
            "inspect" => {
                // The ledger is flat, so recover each declaration's source
                // namespace from the theory that recorded it. Case files
                // have no namespace and therefore print exactly as before.
                let namespaces: std::collections::HashMap<String, String> = self
                    .lib
                    .theories
                    .iter()
                    .filter_map(|theory| theory.namespace.as_ref().map(|ns| (theory, ns.clone())))
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
                let pack_by_decl: std::collections::HashMap<&str, &packs::LoadedPackInfo> = self
                    .packs
                    .iter()
                    .flat_map(|pack| pack.decls.iter().map(move |decl| (decl.as_str(), pack)))
                    .collect();
                // `open` and `risk` markers are metadata on predicates: the
                // predicate line shows the marker, and the marker's own
                // ledger entry remains visible as `open:<predicate>` /
                // `risk:<predicate>`. This is where a reader can see *which*
                // declaration made a predicate open or risky; neither marker
                // is ever inferred from the predicate's spelling.
                let open_predicates = self.lib.env.open_predicates();
                let risk_markers = self.lib.env.risk_markers();
                for decl in self.lib.env.iter() {
                    let kind = match &decl.kind {
                        DeclKind::Sort => "sort ",
                        DeclKind::Obj => "obj  ",
                        DeclKind::Pred => "pred ",
                        DeclKind::Axiom => "axiom",
                        DeclKind::Fact { .. } => "fact ",
                        DeclKind::Def { .. } => "def  ",
                        DeclKind::Rule(_) => "rule ",
                        DeclKind::Interpretation(_) => "interpret",
                        DeclKind::Contrary { .. } => "contr ",
                        DeclKind::Unique { .. } => "uniq  ",
                        DeclKind::Priority { .. } => "prior ",
                        DeclKind::OpenConcept { .. } => "open ",
                        DeclKind::Risk { .. } => "risk ",
                    };
                    // A fact shows who asserts it, so the ledger line
                    // carries the Chinese identity label. An `Axiom`
                    // asserts nothing and has no identity to show.
                    let identity = match &decl.kind {
                        DeclKind::Fact { identity } => {
                            format!("  〔{}〕", identity.label_zh())
                        }
                        _ => String::new(),
                    };
                    // An interpretation's declaration data is what the
                    // ledger can show; whether it is enabled is a session
                    // setting, printed by `:interpret list`, not a
                    // property of the loaded declaration.
                    let extra = match &decl.kind {
                        DeclKind::Interpretation(interpretation) => {
                            let sources = interpretation
                                .sources
                                .iter()
                                .map(|source| source.one_line())
                                .collect::<Vec<_>>()
                                .join("；");
                            format!(
                                " 〔方向 {}〕〔来源 {sources}〕",
                                interpretation.direction.keyword()
                            )
                        }
                        _ => String::new(),
                    };
                    // An `open` marker belongs on the predicate it marks,
                    // next to the type. The marker's own ledger entry below
                    // still shows the synthetic `open:<predicate>` name.
                    let open = match &decl.kind {
                        DeclKind::Pred
                            if open_predicates
                                .iter()
                                .any(|pred| pred.as_ref() == decl.name.as_ref()) =>
                        {
                            " 〔开放概念〕"
                        }
                        _ => "",
                    };
                    // A `risk` marker likewise belongs on the predicate it
                    // marks: the theme it declares is the reason the case
                    // gets a warning, and `:inspect` must show it.
                    let risk = match &decl.kind {
                        DeclKind::Pred => match risk_markers
                            .iter()
                            .find(|(pred, _)| pred.as_ref() == decl.name.as_ref())
                        {
                            Some((_, theme)) => {
                                format!(" 〔风险 {}〕", theme.label_zh())
                            }
                            None => String::new(),
                        },
                        _ => String::new(),
                    };
                    // Recorded scope and occurrence are shown next to the
                    // identity; an undeclared field prints nothing, never a
                    // "default" placeholder.
                    let scope = declared_scope_text(&decl.scope);
                    let occurrence = declared_occurrence_text(decl);
                    // A rule shows the burden/standard clauses it declared;
                    // undeclared fields print nothing at all.
                    let pleading = match &decl.kind {
                        DeclKind::Rule(rule) => rule_pleading_suffix(rule),
                        _ => String::new(),
                    };
                    // A priority has no user-written name: its ledger name
                    // is a synthetic key. Print the surface declaration the
                    // module wrote, the same way the load report does.
                    let name = match &decl.kind {
                        DeclKind::Priority { winner, loser, .. } => {
                            format!("priority {winner} over {loser}")
                        }
                        // The marker is metadata about a predicate, so its
                        // line names the target instead of the synthetic
                        // ledger key (`open:<predicate>` / `risk:<predicate>`).
                        DeclKind::OpenConcept { pred } => pred.to_string(),
                        DeclKind::Risk { theme, pred } => {
                            format!("{} {pred}", theme.label_zh())
                        }
                        _ => decl.name.to_string(),
                    };
                    let namespace = match pack_by_decl.get(decl.name.as_ref()) {
                        Some(pack) => format!(" [{}@{}]", pack.name, pack.version),
                        // A closed-environment case may declare its own
                        // legal concepts; they are marked as case
                        // extensions instead of a namespace, which a case
                        // file never has.
                        None if self.case_extensions.contains_key(decl.name.as_ref()) => {
                            " [案件扩展]".to_owned()
                        }
                        None => namespaces
                            .get(decl.name.as_ref())
                            .map(|ns| format!(" [{ns}]"))
                            .unwrap_or_default(),
                    };
                    writeln!(
                            out,
                            "  {kind} {name} : {}{identity}{extra}{open}{risk}{scope}{occurrence}{pleading}{namespace}",
                            print_expr(&decl.ty)
                        )
                        .ok();
                    // A definition is a named macro: `:inspect` must let a
                    // reader see what the name expands to (the body and its
                    // binder order), because the kernel unfolds it by delta
                    // during conversion and that expansion is otherwise
                    // invisible.
                    if let DeclKind::Def { body } = &decl.kind {
                        writeln!(out, "       := {}", print_expr(body)).ok();
                    }
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
                let e = self.proposition(arg)?;
                let line = format!("已登记用户陈述：{}", print_expr(&e));
                // Name the fact after the first free slot, not after the
                // ledger length: adding metadata declarations (such as an
                // `open` marker) must not renumber session facts, because
                // that would change `:why`/`:cert` output for the same
                // theory and make the marker look non-inert.
                let name = (1..)
                    .map(|n| format!("已知{n}"))
                    .find(|name| self.lib.env.get(name).is_none())
                    .expect("the natural numbers are unbounded");
                self.insert_fact(e, FactIdentity::UserAsserted, name)?;
                writeln!(out, "{line}").ok();
                Ok(Outcome::Proved)
            }
            "fact" => self.fact_command(arg, out),
            "interpret" => self.interpret_command(arg, out),
            "asof" => self.as_of_command(arg, out),
            "jurisdiction" => self.jurisdiction_command(arg, out),
            "why" => {
                // A multi-jurisdiction environment without a chosen
                // jurisdiction is ambiguous: refusing here is the gate,
                // not an applicability judgement.
                self.require_jurisdiction()?;
                self.query(cmd, arg, out)
            }
            "gap" => self.query(cmd, arg, out),
            "explain" => {
                // The narrative uses the same certificate and the same
                // two proof layers as `:why`, so the multi-jurisdiction
                // ambiguity gate applies to it as well.
                self.require_jurisdiction()?;
                self.query(cmd, arg, out)
            }
            "applicability" => self.applicability_command(arg, out),
            "issues" => self.issues_command(arg, out),
            "labels" => self.labels_command(arg, out),
            "review" => self.review_command(arg, out),
            "cert" => self.export_certificate(arg, out),
            "verify-cert" => self.verify_certificate(arg, out),
            "check" => Err(
                ":check 已改名为 :verify-cert；检查源文件请直接运行 std-deduce <文件>".to_owned(),
            ),
            "packs" => self.list_packs(arg, out),
            "lock" => self.lock_packs(arg, out),
            "audit" => self.audit_sources(arg, out),
            "quit" | "exit" => Ok(Outcome::Proved),
            "redact" => self.redact_command(arg, out),
            other => Err(format!("未知命令 `:{other}`")),
        }
    }

    /// `:redact [on|off]` — show or set display-layer redaction.
    ///
    /// Redaction is a display filter: it replaces the case's declared individual
    /// names with stable placeholders in printed output. It never changes a
    /// derivation, a verdict, an exit code or a certificate field, and `:cert`
    /// keeps exporting the original certificate.
    fn redact_command(&mut self, arg: &str, out: &mut impl Write) -> Result<Outcome, String> {
        match arg {
            "" => {
                let state = if self.redact {
                    "已开启"
                } else {
                    "已关闭"
                };
                writeln!(out, "显示层脱敏：{state}。").ok();
                Ok(Outcome::Proved)
            }
            "on" => {
                self.redact = true;
                writeln!(
                    out,
                    "显示层脱敏：已开启（个体名会被替换为占位符；证书不脱敏）。"
                )
                .ok();
                Ok(Outcome::Proved)
            }
            "off" => {
                self.redact = false;
                writeln!(out, "显示层脱敏：已关闭。").ok();
                Ok(Outcome::Proved)
            }
            other => Err(format!(
                "用法：:redact [on|off]（不接受 `{}`）",
                escape_control(other)
            )),
        }
    }

    /// The individual-name mapping display redaction uses, sorted by name.
    ///
    /// An individual is a constant whose declared type is a sort: an `obj`
    /// declaration, or an `axiom` that only names a constant of a sort.
    /// Predicates, sorts, definitions and propositions are not redacted, so the
    /// output stays readable and a proposition still names its predicate. The
    /// mapping is sorted by the declared name, so the same theory always yields
    /// the same placeholder for the same individual, in the same order.
    fn redaction_map(&self) -> Vec<(String, String)> {
        let mut names: Vec<String> = self
            .lib
            .env
            .iter()
            .filter(|decl| is_individual(&self.lib.env, decl))
            .map(|decl| decl.name.to_string())
            .collect();
        names.sort();
        names.dedup();
        names
            .into_iter()
            .enumerate()
            .map(|(index, name)| (name, format!("甲{}", index + 1)))
            .collect()
    }

    /// Replace every declared individual name in `text` with its placeholder.
    ///
    /// Longest name first, so one individual's name is not redacted inside
    /// another's; ties break by name, so the result does not depend on map
    /// iteration order. This rewrites the whole printed text, including source
    /// text, labels and notes: a notice that said the sources were not redacted
    /// would be a way to leak the names back.
    fn redact_text(&self, text: &str) -> String {
        let mut map = self.redaction_map();
        map.sort_by(|left, right| {
            right
                .0
                .len()
                .cmp(&left.0.len())
                .then_with(|| left.0.cmp(&right.0))
        });
        let mut redacted = text.to_owned();
        for (name, placeholder) in map {
            redacted = redacted.replace(&name, &placeholder);
        }
        redacted
    }

    /// Elaborate `arg` as a proposition in the current environment.
    ///
    /// Used by `:given` and `:fact`: a session fact is an assertion, so its
    /// term must really be a proposition. Closed-environment name errors get
    /// the same hint as a failed load.
    fn proposition(&self, arg: &str) -> Result<Expr, String> {
        let t = parse_term(arg)?;
        let e = elab::elab_top(&self.lib.env, &t)
            .map_err(|e| self.environment.annotate_closed_error(e.msg))?;
        check::check(&self.lib.env, &Ctx::new(), &e, &Expr::Sort(0))
            .map_err(|e| self.environment.annotate_closed_error(e.to_string()))?;
        Ok(e)
    }

    /// Insert a fact the session asserts, with the session's own provenance.
    ///
    /// The session is cloned first, so a failed insert (a name collision)
    /// leaves no partial declaration behind. Registration also refuses a
    /// second identity for the same proposition: the identity is evidence, so
    /// `:given` (or `:fact add`) cannot relabel a proposition the ledger
    /// already records under another identity. The comparison uses kernel
    /// conversion, so an alpha variant cannot bypass it.
    fn insert_fact(
        &mut self,
        prop: Expr,
        identity: FactIdentity,
        name: String,
    ) -> Result<(), String> {
        for existing in self.lib.env.iter() {
            let DeclKind::Fact {
                identity: registered,
            } = &existing.kind
            else {
                continue;
            };
            if registered == &identity {
                continue;
            }
            let same = convertible(&self.lib.env, &Ctx::new(), &existing.ty, &prop)
                .map_err(|error| format!("无法判定命题是否已登记为事实：{error}"))?;
            if same {
                return Err(format!(
                    "同一命题只能有一种事实身份：`{}` 已登记为{}，不能同时是{}",
                    print_expr(&prop),
                    registered.label_zh(),
                    identity.label_zh()
                ));
            }
        }
        let decl = std_deduce_kernel::Decl {
            name: std_deduce_kernel::name(&name),
            kind: DeclKind::Fact { identity },
            ty: prop,
            sources: vec![SourceRef {
                text: "用户输入".into(),
                locator: "交互会话".into(),
                ..Default::default()
            }],
            // A session fact records no occurrence. It is not defaulted from
            // the session's as-of date: the query date is not the fact's date.
            scope: Scope::default(),
            occurred_at: None,
            occurred_in: None,
            index: 0,
        };
        let mut lib = self.lib.clone();
        lib.env
            .insert(decl, &Ctx::new())
            .map_err(|e| e.to_string())?;
        self.lib = lib;
        Ok(())
    }

    /// The first free `事实N` name, so a session can register several facts.
    fn next_fact_name(&self) -> String {
        let mut n = 1;
        loop {
            let candidate = format!("事实{n}");
            if !self.lib.env.contains(&candidate) {
                return candidate;
            }
            n += 1;
        }
    }
    /// `:fact` — inspect and register the facts in the ledger.
    ///
    /// `verified` and `stipulated` need the case file's source, so the session
    /// refuses them: they say what a court found or what both sides agreed,
    /// not what the person typing at the prompt says.
    fn fact_command(&mut self, arg: &str, out: &mut impl Write) -> Result<Outcome, String> {
        let (subcommand, rest) = arg.split_once(char::is_whitespace).unwrap_or((arg, ""));
        let rest = rest.trim();
        match subcommand {
            "" | "list" => self.list_facts(out),
            "show" => {
                if rest.is_empty() {
                    return Err("用法：:fact show <命题>".into());
                }
                self.show_facts(rest, out)
            }
            "add" | "assumed" | "disputed" => {
                if rest.is_empty() {
                    return Err(format!("用法：:fact {subcommand} <命题>"));
                }
                let identity = match subcommand {
                    "add" => FactIdentity::UserAsserted,
                    "assumed" => FactIdentity::Assumed,
                    _ => FactIdentity::Disputed,
                };
                let e = self.proposition(rest)?;
                let line = registered_fact_line(identity, &e);
                let name = self.next_fact_name();
                self.insert_fact(e, identity, name)?;
                writeln!(out, "{line}").ok();
                Ok(Outcome::Proved)
            }
            "verified" | "stipulated" => Err(format!(
                "{subcommand} 只能写在案件文件的事实声明里，随 source 一起登记；\
                 交互会话不能声明法院查明或双方无争议"
            )),
            other => Err(format!(
                "未知 :fact 子命令 `{other}`；可选：list / show / add / assumed / disputed / verified / stipulated"
            )),
        }
    }

    /// Print every fact in the ledger, one line each.
    fn list_facts(&self, out: &mut impl Write) -> Result<Outcome, String> {
        let mut any = false;
        for decl in self.lib.env.iter() {
            let DeclKind::Fact { identity } = &decl.kind else {
                continue;
            };
            any = true;
            let source = match decl.sources.first() {
                Some(source) => source.one_line(),
                None => "（没有来源）".to_owned(),
            };
            let note = if identity.seeds_derivation() {
                ""
            } else {
                "（争议事实，不参与推导）"
            };
            writeln!(
                out,
                "  {}  {}  [{}]  ← {source}{note}",
                identity.label_zh(),
                print_expr(&decl.ty),
                decl.name
            )
            .ok();
        }
        if !any {
            writeln!(out, "账本里还没有事实。").ok();
        }
        Ok(Outcome::Proved)
    }

    /// Print the facts definitionally equal to `arg`.
    fn show_facts(&self, arg: &str, out: &mut impl Write) -> Result<Outcome, String> {
        let goal = self.proposition(arg)?;
        let env = &self.lib.env;
        let mut found = false;
        for decl in env.iter() {
            let DeclKind::Fact { identity } = &decl.kind else {
                continue;
            };
            if !convertible(env, &Ctx::new(), &decl.ty, &goal)
                .map_err(|error| format!("无法比较事实与命题：{error}"))?
            {
                continue;
            }
            found = true;
            writeln!(out, "身份：{}", identity.label_zh()).ok();
            writeln!(out, "名称：{}", decl.name).ok();
            writeln!(out, "命题：{}", print_expr(&decl.ty)).ok();
            for source in &decl.sources {
                writeln!(out, "  ← {}", source.one_line()).ok();
                for line in source.full().lines() {
                    writeln!(out, "    {line}").ok();
                }
            }
        }
        if !found {
            return Err("没有登记为事实的命题".into());
        }
        Ok(Outcome::Proved)
    }

    /// `:asof [YYYY-MM-DD]` — show or set the session's legal as-of date.
    ///
    /// The date is an identity field (`:cert` records it and `:verify-cert`
    /// compares it) and a fallback date of the applicability judgement: it is
    /// used only for an instance whose premise facts record no event time.
    /// It never overrides a recorded `occurred_at` and never changes which
    /// rules load.
    fn as_of_command(&mut self, arg: &str, out: &mut impl Write) -> Result<Outcome, String> {
        if arg.is_empty() {
            let line = match (self.environment.as_of(), self.as_of_source) {
                (Some(value), Some(source)) => {
                    format!("基准日：{value}（{}）", source.label())
                }
                (Some(value), None) => format!("基准日：{value}（未设置）"),
                (None, _) => "基准日：未设置".to_owned(),
            };
            writeln!(out, "{line}").ok();
            return Ok(Outcome::Proved);
        }
        validate_date(":asof", arg)?;
        self.environment.set_as_of(arg.to_owned());
        self.as_of_source = Some(SessionValueSource::SessionCommand);
        writeln!(out, "基准日：{arg}（会话命令）").ok();
        Ok(Outcome::Proved)
    }

    /// `:jurisdiction [CODE]` — show or set the session's jurisdiction.
    ///
    /// The code is an identity field and answers the multi-jurisdiction gate.
    /// It is also the case's jurisdiction in the applicability judgement: a
    /// rule whose recorded `jurisdiction` differs is inapplicable and does not
    /// fire. It never filters a rule without a recorded verdict.
    fn jurisdiction_command(&mut self, arg: &str, out: &mut impl Write) -> Result<Outcome, String> {
        if arg.is_empty() {
            let line = match (self.environment.jurisdiction(), self.jurisdiction_source) {
                (Some(value), Some(source)) => {
                    format!("管辖：{value}（{}）", source.label())
                }
                (Some(value), None) => format!("管辖：{value}（未设置）"),
                (None, _) => "管辖：未设置".to_owned(),
            };
            writeln!(out, "{line}").ok();
            return Ok(Outcome::Proved);
        }
        validate_jurisdiction_code(":jurisdiction", arg)?;
        self.environment.set_jurisdiction(arg.to_owned());
        self.jurisdiction_source = Some(SessionValueSource::SessionCommand);
        writeln!(out, "管辖：{arg}（会话命令）").ok();
        Ok(Outcome::Proved)
    }

    /// `:interpret list` / `enable <id>` / `disable <id>`.
    ///
    /// Enabling is explicit and per session: the list prints every declared
    /// interpretation with its current state, `enable` validates existence,
    /// duplicate enablement and kernel-equivalent `to` conclusions, and
    /// `disable` restores the default inert behaviour immediately. The output
    /// never applies an interpretation on its own.
    fn interpret_command(&mut self, arg: &str, out: &mut impl Write) -> Result<Outcome, String> {
        if !self.loaded {
            return Err(
                "尚未加载理论：:interpret 需要环境才能解析解释声明，请先 :load <文件>".into(),
            );
        }
        let parts: Vec<&str> = arg.split_whitespace().collect();
        match parts.as_slice() {
            ["list"] => {
                let records = Reasoner::new(&self.lib.env).interpretation_records();
                if records.is_empty() {
                    writeln!(out, "没有声明任何解释。").ok();
                    return Ok(Outcome::Proved);
                }
                writeln!(
                    out,
                    "解释（已启用 {} 条，共 {} 条）：",
                    self.enabled_interpretations.len(),
                    records.len()
                )
                .ok();
                for record in records {
                    let state = if self.enabled_interpretations.contains(record.id.as_ref()) {
                        "[已启用]"
                    } else {
                        "[未启用]"
                    };
                    writeln!(
                        out,
                        "  {state} {} : {} → {} 〔方向 {}〕",
                        escape_control(&record.id),
                        print_expr(&record.from),
                        print_expr(&record.to),
                        record.direction.keyword()
                    )
                    .ok();
                }
                Ok(Outcome::Proved)
            }
            ["enable", id] => {
                if id.is_empty() {
                    return Err("用法：:interpret enable <解释名>".into());
                }
                let mut reasoner = self.reasoner()?;
                reasoner.enable_interpretation(id)?;
                let name = std_deduce_kernel::name(id);
                let Some(decl) = self.lib.env.get(&name) else {
                    return Err(format!("解释 `{id}` 不存在：当前环境没有这个声明"));
                };
                let DeclKind::Interpretation(interpretation) = &decl.kind else {
                    return Err(format!("`{id}` 不是解释声明，不能启用"));
                };
                self.enabled_interpretations.insert((*id).to_owned());
                writeln!(
                    out,
                    "已启用解释 `{id}`（{} → {}）。",
                    print_expr(&interpretation.from),
                    print_expr(&interpretation.to)
                )
                .ok();
                Ok(Outcome::Proved)
            }
            ["disable", id] => {
                if id.is_empty() {
                    return Err("用法：:interpret disable <解释名>".into());
                }
                let name = std_deduce_kernel::name(id);
                match self.lib.env.get(&name).map(|decl| &decl.kind) {
                    Some(DeclKind::Interpretation(_)) => {}
                    Some(_) => {
                        return Err(format!("`{id}` 不是解释声明，不能停用"));
                    }
                    None => {
                        return Err(format!("解释 `{id}` 不存在：当前环境没有这个声明"));
                    }
                }
                if !self.enabled_interpretations.remove(*id) {
                    return Err(format!("解释 `{id}` 没有启用，不能停用"));
                }
                writeln!(out, "已停用解释 `{id}`。").ok();
                Ok(Outcome::Proved)
            }
            _ => Err(
                "用法：:interpret list | :interpret enable <解释名> | :interpret disable <解释名>"
                    .into(),
            ),
        }
    }

    /// Refuse `:why` / `:explain` / `:review` / `:cert` when the loaded rules
    /// name two or more jurisdictions and the session has not chosen one.
    ///
    /// This is a gate on ambiguity, not an applicability judgment: it runs
    /// before the reasoner, because without a case jurisdiction the judgement
    /// could only leave every differing rule unchecked. With one jurisdiction
    /// the query proceeds unchanged, and a chosen jurisdiction does not filter
    /// a rule directly — the recorded applicability verdict does.
    fn require_jurisdiction(&self) -> Result<(), String> {
        if self.environment.jurisdiction().is_some() {
            return Ok(());
        }
        let codes: BTreeSet<&str> = self
            .lib
            .env
            .iter()
            .filter(|decl| matches!(decl.kind, DeclKind::Rule(_)))
            .filter_map(|decl| decl.scope.jurisdiction.as_deref())
            .collect();
        if codes.len() < 2 {
            return Ok(());
        }
        Err(format!(
            "必须用 --jurisdiction 或 :jurisdiction 选择管辖：候选规则涉及 {}",
            codes.into_iter().collect::<Vec<_>>().join("、")
        ))
    }

    fn query(&mut self, cmd: &str, arg: &str, out: &mut impl Write) -> Result<Outcome, String> {
        let goal = self.goal(arg)?;
        let mut r = self.reasoner()?;
        // Every axiom whose declared type is a proposition is usable as an
        // assumption. This is how a corpus of facts enters. See
        // `Reasoner::assume_ledger_axioms`. A goal that only a universal fact
        // can prove is demanded after the first pass fails to derive it.
        saturate_with_goal(&mut r, Some(&goal))?;

        // A cycle disables every edge inside it. Say so before the query
        // prints anything: a result that fell back to "no usable priority"
        // must not be read as "nothing was declared".
        write_priority_cycle_warning(out, &r.priority_cycles());

        // A conclusion can be in a recorded conflict without being asserted:
        // that is a third outcome, distinct from both success and a gap.
        // `:explain` deliberately skips these early reports: it builds the
        // certificate and narrates the conflict together with the proof (or
        // the gap), so the reader gets one coherent explanation.
        let reachable = r.knows(&goal);
        // The certificate is built before the conflict report so `:why` and
        // `:explain` attach the same derived trust labels even when the goal
        // takes part in an unresolved or defeated conflict.
        let derivation = if cmd == "why" || cmd == "explain" {
            let mut d = r.derivation();
            if reachable {
                d.root = r.root_for(&goal);
            } else {
                let ex = r.explain(&goal)?;
                let id = d.nodes.len();
                d.nodes.push(std_deduce_reason::Node::Gap {
                    prop: goal.clone(),
                    candidates: ex.candidates,
                    axiom_candidates: ex.axiom_candidates,
                    note: ex.note,
                });
                d.root = Some(id);
            }
            Some(d)
        } else {
            None
        };
        let certificate = match &derivation {
            Some(d) => {
                let mut certificate = reason_certificate(&self.lib.env, d, &r.priority_order())?;
                self.mark_case_extensions(&mut certificate);
                Some(certificate)
            }
            None => None,
        };
        // The concepts the root's proof graph decided. This is the certificate
        // layer's own recomputation, the same one `cert::check` runs, so the
        // notice printed here and the recorded obligation cannot disagree.
        let open_concepts = match &certificate {
            Some(certificate) => self.open_concepts(certificate)?,
            None => Vec::new(),
        };
        let trust = match &certificate {
            Some(certificate) => Some(derive_trust(certificate)?),
            None => None,
        };
        // The risk themes the root derivation is about. Like the trust labels
        // this is a derived view of the certificate plus the environment's
        // declared `risk` markers; it is printed as its own line and never
        // merged into a trust label.
        let risk = match &certificate {
            Some(certificate) => Some(derive_risk(&self.lib.env, certificate)?),
            None => None,
        };

        if cmd != "explain" {
            if let Some(c) = r.conflict_for(&goal) {
                match &c.resolution {
                    Resolution::Unresolved { reason } => {
                        if cmd == "why" {
                            // Validate before printing a label: a certificate
                            // that fails either layer must never be labelled.
                            let Some(certificate) = &certificate else {
                                return Err(
                                    "内部状态错误：:why 的冲突分支应当在构建证书之后".to_owned()
                                );
                            };
                            self.certificate_layers(certificate, out)?;
                            let Some(trust) = &trust else {
                                return Err("内部状态错误：冲突分支应当已经派生信任标签".to_owned());
                            };
                            let Some(risk) = &risk else {
                                return Err("内部状态错误：冲突分支应当已经派生题材风险".to_owned());
                            };
                            write_trust_line(out, trust);
                            report_unresolved(out, &r, &goal, &c, reason);
                            write_risk_warning(out, risk);
                            write_disclaimer(out);
                            return Ok(Outcome::Unresolved);
                        }
                        report_unresolved(out, &r, &goal, &c, reason);
                        return Ok(Outcome::Unresolved);
                    }
                    Resolution::Defeated { winner, basis } => {
                        let side = r.conflict_side(&c, &goal);
                        if side != Some(*winner) {
                            if cmd == "why" {
                                let Some(certificate) = &certificate else {
                                    return Err("内部状态错误：:why 的冲突分支应当在构建证书之后"
                                        .to_owned());
                                };
                                self.certificate_layers(certificate, out)?;
                                let Some(trust) = &trust else {
                                    return Err(
                                        "内部状态错误：冲突分支应当已经派生信任标签".to_owned()
                                    );
                                };
                                write_trust_line(out, trust);
                            }
                            report_defeated(out, &r, &goal, &c, *winner, basis);
                            if cmd == "why" {
                                let Some(risk) = &risk else {
                                    return Err(
                                        "内部状态错误：冲突分支应当已经派生题材风险".to_owned()
                                    );
                                };
                                write_risk_warning(out, risk);
                                write_disclaimer(out);
                            }
                            return Ok(Outcome::Gap);
                        }
                        // The winner is asserted; fall through and show it as
                        // proved, with a note about the defeated competitor.
                        debug_assert!(reachable);
                    }
                }
            }
        }

        if cmd == "gap" {
            if reachable {
                writeln!(out, "目标可以推出。").ok();
                // A goal proved by universal elimination names the universal
                // fact and the values it was instantiated with, so the reader
                // sees that the conclusion is an instance, not a bare fact.
                if let Some(instance) = r.axiom_instance_for(&goal) {
                    writeln!(
                        out,
                        "  由全称公理 ⟨{}⟩ 实例化（{}）",
                        escape_control(&instance.axiom),
                        instance_bindings_text(&instance.bindings)
                    )
                    .ok();
                }
                return Ok(Outcome::Proved);
            }
            let limits = GapLimits::default();
            let tree = r.gap_tree_with(&goal, &limits)?;
            writeln!(
                out,
                "无法推出 {}。缺口树（最大深度 {}，最多 {} 个节点，每条规则最多尝试 {} 次）：",
                print_expr(&goal),
                limits.max_depth,
                limits.max_nodes,
                limits.max_rule_attempts
            )
            .ok();
            render_gap_tree(out, &tree, &r, 2, "缺口");
            write_interpretation_hints(out, &r, &goal)?;
            return Ok(Outcome::Gap);
        }

        let Some(d) = derivation else {
            return Err("内部状态错误：只有 :why / :explain / :gap 会到达查询路径".to_owned());
        };
        let Some(certificate) = certificate else {
            return Err("内部状态错误：:why / :explain 应当已经构建证书".to_owned());
        };
        let Some(trust) = trust else {
            return Err("内部状态错误：:why / :explain 应当已经派生信任标签".to_owned());
        };
        let Some(risk) = risk else {
            return Err("内部状态错误：:why / :explain 应当已经派生题材风险".to_owned());
        };
        // The tree or the narrative is printed from the certificate, then that
        // same certificate is checked by both layers: what the user sees and
        // the object being checked cannot diverge. `:why` keeps the formal
        // tree; `:explain` prints the Chinese because-so rendering of it.
        // Every applied rule's conclusion line carries its applicability
        // verdict inline; the certificate stores the same verdict, and this
        // annotation is rendered from the derivation's judgement.
        let annotations = derivation_annotations(&d);
        // The burden/standard declarations the narrative prints come from the
        // environment, not from the certificate: certificate v8 does not record
        // them. The map is built once by the reasoner from the same rule
        // declarations the gap tree reads, so `:explain` and `:gap` report the
        // same values.
        let pleadings = r.pleadings();
        let rendered = if cmd == "explain" {
            render_narrative_with_context(&certificate, &open_concepts, &annotations, &pleadings)?
        } else {
            render_with_annotations(&certificate, &annotations)?
        };
        writeln!(out, "{rendered}").ok();
        // A gap root's candidate lines cannot carry a verdict through the
        // certificate, so its candidates are listed here with their state.
        if let Some(root) = d.root {
            write_gap_applicability_notes(out, &d, root);
        }
        // `:why` reports an unresolved or defeated goal before it builds this
        // certificate, so its conflict sides carry their own labels. `:explain`
        // narrates the conflict in the certificate instead, and still has to
        // label the rules that argued on the goal's side.
        if cmd == "explain" {
            if let Some(conflict) = r.conflict_for(&goal) {
                let side_of_goal = r.conflict_side(&conflict, &goal);
                let mut verdicts = BTreeSet::new();
                for (side, prop) in [(Side::Left, &conflict.left), (Side::Right, &conflict.right)] {
                    let include = match &conflict.resolution {
                        Resolution::Unresolved { .. } => true,
                        Resolution::Defeated { .. } => side_of_goal == Some(side),
                    };
                    if !include {
                        continue;
                    }
                    if let Some(side_derivation) = r.derivation_for(prop) {
                        if let Some(side_root) = side_derivation.root {
                            collect_derivation_verdicts(&side_derivation, side_root, &mut verdicts);
                        }
                    }
                }
                write_applicability_verdicts(out, &verdicts);
            }
        }
        if cmd == "why" {
            write_open_concept_lines(out, &open_concepts);
        }
        // An unreachable `:why` reports the same kind of gap as `:gap`, so it
        // offers the same "only an unenabled interpretation is missing" hint.
        // The hint is about the queried goal only: a rule's missing premise is
        // never bridged by enabling an interpretation, because rules do not
        // consume interpretation conclusions.
        if cmd == "why" && !reachable {
            write_interpretation_hints(out, &r, &goal)?;
        }

        let (report, kernel_report) = self.certificate_layers(&certificate, out)?;

        let root = certificate
            .root
            .ok_or_else(|| "推理器生成的证书没有根节点：无法确认结论".to_owned())?;
        if matches!(certificate.nodes.get(root), Some(CertNode::Gap { .. })) {
            writeln!(out, "证书有效，但根为缺口，结论未被证明。").ok();
            write_trust_line(out, &trust);
            if cmd != "explain" {
                report_conflicts(out, &certificate);
            }
            write_risk_warning(out, &risk);
            write_disclaimer(out);
            return Ok(Outcome::Gap);
        }
        if !report.root_proved || !kernel_report.root_proved {
            writeln!(out, "证书有效，但根未被证明，结论未被证明。").ok();
            write_trust_line(out, &trust);
            if cmd != "explain" {
                report_conflicts(out, &certificate);
            }
            write_risk_warning(out, &risk);
            write_disclaimer(out);
            return Ok(Outcome::Gap);
        }

        let unresolved = certificate
            .conflicts
            .iter()
            .filter(|conflict| {
                matches!(
                    conflict.resolution,
                    std_deduce_cert::Resolution::Unresolved { .. }
                )
            })
            .count();
        if !certificate.open_obligations.is_empty() || unresolved > 0 {
            // A certificate that applied a case-local rule names it before the
            // summary, so the reader knows what the open obligation is.
            write_local_extension_lines(out, &certificate);
            writeln!(
                out,
                "证书有效且根已证明，但仍有未决义务（open_obligations {} 项，未决冲突 {} 项），不能报告为无保留的证明。",
                certificate.open_obligations.len(),
                unresolved
            )
            .ok();
            write_trust_line(out, &trust);
            if cmd != "explain" {
                report_conflicts(out, &certificate);
            }
            write_risk_warning(out, &risk);
            write_disclaimer(out);
            return Ok(Outcome::Gap);
        }

        // Determine the defeated-conflict note before printing the success
        // line: a comparison failure is an error, never a success followed by
        // an error. `:explain` already narrates every conflict, so it skips the
        // terse `:why` postscript.
        let won_conflict = if reachable && cmd != "explain" {
            won_conflict_note(&self.lib.env, &goal, &certificate)?
        } else {
            None
        };

        writeln!(out, "推导已通过独立校验。").ok();
        write_trust_line(out, &trust);
        if cmd != "explain" {
            report_conflicts(out, &certificate);
            if let Some((other, other_by, basis)) = won_conflict {
                writeln!(
                    out,
                    "注：与「{}」存在冲突，已按记录的裁决为本结论胜出。",
                    print_expr(&other)
                )
                .ok();
                write_certificate_basis(out, &basis, &other_by);
            }
        }
        write_risk_warning(out, &risk);
        write_disclaimer(out);
        Ok(Outcome::Proved)
    }

    /// `:issues` — every conclusion the current fact set can still contest.
    ///
    /// The scan itself lives in the reasoner; this command only renders the
    /// gap tree of each contestable conclusion and the limits that stopped the
    /// scan. A scan that finds nothing is a success: there is nothing to
    /// argue about under the current facts. A limit is always printed, never
    /// applied silently.
    fn issues_command(&mut self, arg: &str, out: &mut impl Write) -> Result<Outcome, String> {
        if !arg.is_empty() {
            return Err("用法：:issues（不接受参数；它列出当前事实集下所有可争的结论）".into());
        }
        if !self.loaded {
            // Same rule as `:cert`: the scan describes the current fact set,
            // and an unloaded session has no environment to describe.
            return Err(
                "尚未加载理论：:issues 需要已加载的环境才能扫描当前事实集，请先 :load <文件>"
                    .into(),
            );
        }
        let mut r = self.reasoner()?;
        saturate_with_goal(&mut r, None)?;
        write_priority_cycle_warning(out, &r.priority_cycles());

        let limits = GapLimits::default();
        let scan = r.issues_with(&limits)?;
        if scan.issues.is_empty() {
            writeln!(out, "没有可争的结论。").ok();
        } else {
            writeln!(
                out,
                "当前事实集下可争的结论 {} 条（缺口树：最大深度 {}，最多 {} 个节点，每条规则最多尝试 {} 次）：",
                scan.issues.len(),
                limits.max_depth,
                limits.max_nodes,
                limits.max_rule_attempts
            )
            .ok();
            for issue in &scan.issues {
                render_gap_tree(out, issue, &r, 2, "争点");
            }
        }
        for limit in &scan.limits {
            // "已截断" must say what was cut off: an issue cap drops whole
            // conclusions, a per-rule cap leaves instances of that rule
            // unenumerated.
            let suffix = match limit {
                GapLimit::RuleAttempts { .. } => "其余实例未枚举",
                _ => "其余未列出",
            };
            writeln!(out, "  已截断：{}；{suffix}。", gap_limit_text(limit)).ok();
        }
        if !scan.uninstantiable.is_empty() {
            writeln!(
                out,
                "  另有 {} 条规则无法在当前事实集上实例化（参数类型没有已声明的常量，或结论依赖前提证明）：{}",
                scan.uninstantiable.len(),
                format_limited_names(&scan.uninstantiable)
            )
            .ok();
        }
        if !scan.excluded.is_empty() {
            writeln!(
                out,
                "  另有 {} 条规则因所有可枚举实例都被时空适用性排除而未扫描：",
                scan.excluded.len()
            )
            .ok();
            let mut has_undecidable = false;
            for excluded in &scan.excluded {
                writeln!(out, "    ⟨{}⟩：", excluded.rule).ok();
                for verdict in &excluded.verdicts {
                    if matches!(verdict, Applicability::Undecidable { .. }) {
                        has_undecidable = true;
                    }
                    writeln!(out, "      {}", verdict.summary_zh()).ok();
                }
            }
            if has_undecidable {
                writeln!(
                    out,
                    "    提示：无法判定的实例需要为该争点显式指定引用时间（尚未实现）。"
                )
                .ok();
            }
        }
        Ok(if scan.issues.is_empty() {
            Outcome::Proved
        } else {
            Outcome::Gap
        })
    }

    /// `:applicability [<命题>]` — report the temporal/spatial judgement.
    ///
    /// With no goal it lists every rule judged as an empty instance (the
    /// rule's declarations plus `:asof` when set). With a goal it lists every
    /// rule the goal's derivation or gap tree uses, with the per-instance
    /// verdict and the event times/places it relied on. This is a report, not
    /// a query: it never changes a conclusion and always exits `0`, because
    /// "this rule does not apply" is information, not a failure.
    fn applicability_command(
        &mut self,
        arg: &str,
        out: &mut impl Write,
    ) -> Result<Outcome, String> {
        if !self.loaded {
            return Err(
                "尚未加载理论：:applicability 需要已加载的环境才能判定规则，请先 :load <文件>"
                    .into(),
            );
        }
        if arg.is_empty() {
            // Without a goal there is no instance to judge: the command only
            // reports the declarations. It must not judge an empty instance
            // with `:asof` (that would present the query date as the event
            // time), and it must not saturate the theory (oscillation would
            // otherwise turn a report into an error).
            let mut rules: Vec<&Decl> = self.lib.env.rules().into_iter().collect();
            rules.sort_by(|a, b| a.name.cmp(&b.name));
            writeln!(
                out,
                "时空适用性（未给定目标：不做判定，只列声明范围，共 {} 条规则）：",
                rules.len()
            )
            .ok();
            if rules.is_empty() {
                writeln!(out, "  环境中没有规则。").ok();
            }
            for decl in rules {
                let scope = declared_scope_text(&decl.scope);
                let scope = if scope.is_empty() {
                    "（无范围声明）".to_owned()
                } else {
                    scope
                };
                let sources = decl
                    .sources
                    .iter()
                    .map(|source| source.one_line())
                    .collect::<Vec<_>>()
                    .join("；");
                if sources.is_empty() {
                    writeln!(out, "  ⟨{}⟩：{scope}", decl.name).ok();
                } else {
                    writeln!(out, "  ⟨{}⟩：{scope}  ← {sources}", decl.name).ok();
                }
            }
            writeln!(out, "未判定：需要目标命题或带发生时间/地点的事实。").ok();
            return Ok(Outcome::Proved);
        }

        let goal = self.goal(arg)?;
        let mut r = self.reasoner()?;
        saturate_with_goal(&mut r, Some(&goal))?;

        let mut verdicts = BTreeSet::new();
        if r.knows(&goal) {
            let mut d = r.derivation();
            d.root = r.root_for(&goal);
            if let Some(root) = d.root {
                collect_derivation_verdicts(&d, root, &mut verdicts);
            }
        } else if let Some(conflict) = r.conflict_for(&goal) {
            // A conflicted goal is not in the fact base and has no gap tree.
            // An unresolved conflict needs both sides' rules; a decided one
            // needs only the goal's own side.
            let side_of_goal = r.conflict_side(&conflict, &goal);
            for (side, prop) in [(Side::Left, &conflict.left), (Side::Right, &conflict.right)] {
                let include = match &conflict.resolution {
                    Resolution::Unresolved { .. } => true,
                    Resolution::Defeated { .. } => side_of_goal == Some(side),
                };
                if !include {
                    continue;
                }
                if let Some(side_derivation) = r.derivation_for(prop) {
                    if let Some(side_root) = side_derivation.root {
                        collect_derivation_verdicts(&side_derivation, side_root, &mut verdicts);
                    }
                }
            }
        } else {
            let tree = r.gap_tree(&goal)?;
            collect_gap_verdicts(&tree, &mut verdicts);
        };
        writeln!(out, "时空适用性（目标：{}）：", print_expr(&goal)).ok();
        if verdicts.is_empty() {
            writeln!(
                out,
                "  目标没有用到任何规则：它要么由已登记事实（或解释应用）直接成立，要么没有任何候选规则。"
            )
            .ok();
            return Ok(Outcome::Proved);
        }
        for (rule, verdict) in &verdicts {
            writeln!(out, "  ⟨{rule}⟩：{verdict}").ok();
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
    ///
    /// Two explanation lines precede the JSON: the model-only disclaimer and the
    /// privacy notice that the certificate contains the case text and may
    /// contain personal information. They stay outside the JSON on purpose (the
    /// certificate is not a place for display text and gains no field), and
    /// display redaction never touches this command: the certificate words are
    /// what `:verify-cert` re-checks, so a redacted certificate could no longer
    /// be verified.
    fn export_certificate(&self, arg: &str, out: &mut impl Write) -> Result<Outcome, String> {
        if !self.loaded {
            return Err(
                "尚未加载理论：:cert 需要已加载的环境才能记录环境身份，请先 :load <文件>".into(),
            );
        }
        if arg.is_empty() {
            return Err("用法：:cert <目标命题>".into());
        }
        // Same ambiguity gate as `:why`: a two-jurisdiction environment cannot
        // stamp a certificate until the session says which legal system it is
        // speaking about. Choosing one only records it; no rule is filtered.
        self.require_jurisdiction()?;
        let goal = self.goal(arg)?;
        let mut r = self.reasoner()?;
        saturate_with_goal(&mut r, Some(&goal))?;

        let reachable = r.knows(&goal);
        let mut d = r.derivation();
        if reachable {
            d.root = r.root_for(&goal);
        } else {
            let ex = r.explain(&goal)?;
            let id = d.nodes.len();
            d.nodes.push(std_deduce_reason::Node::Gap {
                prop: goal.clone(),
                candidates: ex.candidates,
                axiom_candidates: ex.axiom_candidates,
                note: ex.note,
            });
            d.root = Some(id);
        }

        let mut certificate = reason_certificate(&self.lib.env, &d, &r.priority_order())?
            .with_environment(self.identity()?);
        self.mark_case_extensions(&mut certificate);
        let json = certificate
            .to_json_pretty()
            .map_err(|e| format!("证书序列化失败：{e}"))?;
        // The explanation lines stay before the JSON: from the first `{` on the
        // bytes are the certificate, so existing consumers are unaffected and
        // the certificate gains no field. Display redaction never applies here:
        // a redacted certificate could not be re-checked by `:verify-cert`.
        write_cert_notice(out);
        writeln!(out, "{json}").ok();
        Ok(if reachable {
            Outcome::Proved
        } else {
            Outcome::Gap
        })
    }

    /// `:labels <term>` — derive the goal's certificate and print its full
    /// trust-label report.
    ///
    /// The report is the same [`derive_trust`] view `:why` and `:explain` print
    /// near their result line, expanded to every label and its evidence. It is
    /// recomputed from a certificate built exactly as `:cert` builds one, so a
    /// target cannot receive different labels in different commands. The
    /// certificate is checked by both layers before any label is printed; a
    /// certificate that fails either layer is an error, never a labelled
    /// conclusion. After the five trust labels, the risk themes of the same
    /// certificate are printed as a separate section: they are a second label,
    /// not one of the five, and they do not change the label-based exit code.
    fn labels_command(&mut self, arg: &str, out: &mut impl Write) -> Result<Outcome, String> {
        if !self.loaded {
            return Err(
                "尚未加载理论：:labels 需要已加载的环境才能生成证书，请先 :load <文件>".into(),
            );
        }
        if arg.is_empty() {
            return Err("用法：:labels <目标命题>".into());
        }
        self.require_jurisdiction()?;
        let goal = self.goal(arg)?;
        let mut r = self.reasoner()?;
        saturate_with_goal(&mut r, Some(&goal))?;
        write_priority_cycle_warning(out, &r.priority_cycles());

        let reachable = r.knows(&goal);
        let mut d = r.derivation();
        if reachable {
            d.root = r.root_for(&goal);
        } else {
            let ex = r.explain(&goal)?;
            let id = d.nodes.len();
            d.nodes.push(std_deduce_reason::Node::Gap {
                prop: goal.clone(),
                candidates: ex.candidates,
                axiom_candidates: ex.axiom_candidates,
                note: ex.note,
            });
            d.root = Some(id);
        }
        let mut certificate = reason_certificate(&self.lib.env, &d, &r.priority_order())?;
        self.mark_case_extensions(&mut certificate);

        // The labels are printed only after both layers accept the certificate.
        self.certificate_layers(&certificate, out)?;

        let trust = derive_trust(&certificate)?;
        let risk = derive_risk(&self.lib.env, &certificate)?;
        writeln!(out, "{}", trust.summary()).ok();
        writeln!(out, "标签与依据（目标：{}）：", print_expr(&goal)).ok();
        for label in trust.labels() {
            writeln!(out, "  {}", label.name_zh()).ok();
            for evidence in trust.evidence(*label) {
                writeln!(out, "    - {evidence}").ok();
            }
        }
        // The risk themes are a second label, reported next to the five trust
        // labels and never inside them: a themed case keeps its trust label.
        write_risk_section(out, &risk);
        write_disclaimer(out);
        let proved_without_open = !trust.contains(TrustLabel::FactNeedsEvidence)
            && !trust.contains(TrustLabel::DisputeUnresolved)
            && !trust.contains(TrustLabel::NeedsLawyerJudgment);
        Ok(if proved_without_open {
            Outcome::Proved
        } else {
            Outcome::Gap
        })
    }

    /// `:review <命题> [--out <文件>]` — the Markdown review report.
    ///
    /// The report is rendered from the same certificate `:why` / `:cert` build
    /// (checked by both layers first), the reasoner's gap trees and the
    /// `:issues` scan, the declared burden/standard map, and the trust labels.
    /// It adds no inference of its own and is not legal advice. Without `--out`
    /// the report goes to stdout; with `--out` it is written to the named file
    /// and only the path line is printed. The write happens after the complete
    /// report string exists, through a temporary file in the destination's own
    /// directory; an existing destination's permission bits are copied to the
    /// temporary file before the rename, so the replacement keeps the target's
    /// permissions. A failed write, permission copy or rename leaves no
    /// half-written report and no partial destination.
    ///
    /// The exit code is `:why`'s: `0` only when the root is proved and no open
    /// obligation or unresolved conflict is recorded; every other outcome is
    /// `1`. A command, certificate or write error is `2`.
    fn review_command(&mut self, arg: &str, out: &mut impl Write) -> Result<Outcome, String> {
        if !self.loaded {
            return Err(
                "尚未加载理论：:review 需要已加载的环境才能生成复核报告，请先 :load <文件>".into(),
            );
        }
        let (goal_text, report_path) = split_review_argument(arg)?;
        // Same ambiguity gate as `:why` and `:cert`: a report about a
        // multi-jurisdiction environment must say which legal system it is
        // speaking about.
        self.require_jurisdiction()?;
        let goal = self.goal(goal_text)?;
        let mut r = self.reasoner()?;
        // The same query-level trigger as `:why` / `:cert`: when the first
        // saturation pass does not prove the goal, demand a universal-elimination
        // instance for it. Without this the report would describe a gap where
        // the certificate layer can derive the conclusion.
        saturate_with_goal(&mut r, Some(&goal))?;

        let reachable = r.knows(&goal);
        let mut derivation = r.derivation();
        if reachable {
            derivation.root = r.root_for(&goal);
        } else {
            let explanation = r.explain(&goal)?;
            let id = derivation.nodes.len();
            derivation.nodes.push(std_deduce_reason::Node::Gap {
                prop: goal.clone(),
                candidates: explanation.candidates,
                axiom_candidates: explanation.axiom_candidates,
                note: explanation.note,
            });
            derivation.root = Some(id);
        }
        let mut certificate = reason_certificate(&self.lib.env, &derivation, &r.priority_order())?;
        self.mark_case_extensions(&mut certificate);

        // A report is never generated from a certificate that does not pass
        // both layers: the labels and the report would then describe an
        // unchecked object.
        self.certificate_layers(&certificate, out)?;
        let trust = derive_trust(&certificate)?;
        let dependency = std_deduce_cert::open_concept_dependency(&self.lib.env, &certificate)
            .map_err(|error| format!("无法重算开放概念义务：{error}"))?;
        let limits = GapLimits::default();
        let issues = r.issues_with(&limits)?;
        let pleadings = r.pleadings();
        let root_gap = if reachable {
            None
        } else {
            Some(r.gap_tree_with(&goal, &limits)?)
        };
        // The report derives the same risk themes `:why` / `:explain` print from
        // the certificate inside the renderer, so risk cannot change the exit
        // code and cannot disagree with the report's own labels.
        let report = crate::review::render_review(
            &self.lib.env,
            &certificate,
            &trust,
            dependency.as_ref(),
            &issues,
            root_gap.as_ref(),
            &pleadings,
        )?;
        // `--redact` is a display-layer filter, and the report file is display
        // too: apply the same mapping before writing, so the file cannot leak a
        // name the stdout form would hide. With redaction off this is the same
        // report, byte for byte.
        let report = if self.redact {
            self.redact_text(&report)
        } else {
            report
        };

        match report_path {
            Some(path) => {
                write_review_file(path, &report)?;
                writeln!(out, "已写入复核报告：{}", escape_path(path)).ok();
            }
            None => {
                // The report already ends with a newline; no extra blank line
                // is appended, so the file and stdout forms are byte-identical.
                write!(out, "{report}").ok();
            }
        }

        let unresolved = certificate
            .conflicts
            .iter()
            .filter(|conflict| {
                matches!(
                    conflict.resolution,
                    std_deduce_cert::Resolution::Unresolved { .. }
                )
            })
            .count();
        let proved = trust.root_proved();
        let clean = proved && certificate.open_obligations.is_empty() && unresolved == 0;
        Ok(if clean {
            Outcome::Proved
        } else if proved && unresolved > 0 {
            Outcome::Unresolved
        } else {
            Outcome::Gap
        })
    }

    /// Record the case-local rules a certificate applied as one obligation.
    ///
    /// A rule a case file declared is not law from an audited pack. When the
    /// closed environment allowed such rules, the certificate must say so: one
    /// `local-extension` obligation names every case rule the proof applied and
    /// the nodes that apply them, so no consumer can mistake the conclusion for
    /// one derived from pack rules alone. A certificate that applied none is
    /// left untouched, and the default session records no case extensions at
    /// all, so its certificates never carry the obligation.
    fn mark_case_extensions(&self, certificate: &mut Certificate) {
        let mut used: BTreeMap<&str, Vec<usize>> = BTreeMap::new();
        for (index, node) in certificate.nodes.iter().enumerate() {
            let CertNode::RuleApplication { rule, .. } = node else {
                continue;
            };
            if self.case_extensions.get(rule).copied() != Some("rule") {
                continue;
            }
            let nodes = used.entry(rule.as_str()).or_default();
            if !nodes.contains(&index) {
                nodes.push(index);
            }
        }
        if used.is_empty() {
            return;
        }
        let mut nodes: Vec<usize> = used.values().flatten().copied().collect();
        nodes.sort_unstable();
        nodes.dedup();
        let names = used
            .keys()
            .map(|name| format!("`{name}`"))
            .collect::<Vec<_>>()
            .join("、");
        certificate.open_obligations.push(OpenObligation {
            id: LOCAL_EXTENSION_ID.to_owned(),
            kind: ObligationKind::NeedsHumanDetermination,
            description: format!(
                "规则 {names} 由案件文件声明，未经官方包审核；本证书的推导依赖这些规则"
            ),
            nodes,
        });
    }

    /// The concepts the certificate's root derivation turns into proved
    /// propositions, recomputed from the loaded environment and the proof graph.
    ///
    /// This is the certificate layer's own recomputation
    /// ([`std_deduce_cert::open_concept_dependency`]), which `cert::check`
    /// compares with the recorded `open_concept` obligation. Display never
    /// parses an obligation's description to recover the concept names.
    fn open_concepts(&self, certificate: &Certificate) -> Result<Vec<String>, String> {
        let dependency = std_deduce_cert::open_concept_dependency(&self.lib.env, certificate)
            .map_err(|error| format!("无法重算开放概念义务：{error}"))?;
        Ok(dependency
            .map(|dependency| {
                dependency
                    .concepts
                    .into_iter()
                    .map(|concept| concept.to_string())
                    .collect()
            })
            .unwrap_or_default())
    }

    /// Run the two certificate layers and report their failures.
    ///
    /// Both layers run and are reported separately: `cert::check` rebuilds
    /// rule instances and side conditions, then `kernel_proof` rebuilds the
    /// monotone proof terms and asks the kernel. A logical pass with a kernel
    /// failure is an error (`2`), not a valid certificate. Every caller that
    /// prints a trust line must call this first; a failed certificate must not
    /// be labelled as a conclusion.
    fn certificate_layers(
        &self,
        certificate: &Certificate,
        out: &mut impl Write,
    ) -> Result<(CheckReport, KernelProofReport), String> {
        let checked = std_deduce_cert::check(&self.lib.env, certificate);
        let kernel = std_deduce_cert::kernel_proof(&self.lib.env, certificate);
        match (checked, kernel) {
            (Ok(report), Ok(kernel)) => Ok((report, kernel)),
            (checked, kernel) => {
                let mut failures = Vec::new();
                if let Err(error) = checked {
                    let error = escape_control(&error.to_string());
                    writeln!(out, "逻辑校验失败：{error}").ok();
                    failures.push(format!("逻辑层：{error}"));
                }
                if let Err(error) = kernel {
                    let error = escape_control(&error.to_string());
                    writeln!(out, "内核证明失败：{error}").ok();
                    failures.push(format!("内核层：{error}"));
                }
                Err(format!("证书校验失败（{}）", failures.join("；")))
            }
        }
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
                let error = escape_control(&e.to_string());
                writeln!(out, "逻辑校验：失败（{error}）").ok();
                writeln!(out, "内核证明：未运行（逻辑校验失败）").ok();
                writeln!(out, "侧条件：未评估（逻辑校验失败）").ok();
                writeln!(out, "需人判断：未评估（逻辑校验失败）").ok();
                return Err(format!("证书校验失败（逻辑层）：{error}"));
            }
        };
        // Every rule application and gap candidate carries one applicability
        // record; `check` has just recomputed each one from the environment
        // and the certificate's own inputs. Report the count instead of
        // leaving the reader to assume the verdicts were trusted.
        let applicability_records: usize = certificate
            .nodes
            .iter()
            .map(|node| match node {
                CertNode::RuleApplication { .. } => 1,
                CertNode::Gap { candidates, .. } => candidates.len(),
                _ => 0,
            })
            .sum();
        writeln!(
            out,
            "逻辑校验：通过（检查 {} 个节点；适用性重算 {} 条；{}）",
            report.nodes_checked,
            applicability_records,
            root_summary(&certificate, &report)
        )
        .ok();

        // Layer 2: the monotone skeleton must survive the kernel, not only the
        // structural check above.
        let kernel = match std_deduce_cert::kernel_proof(&self.lib.env, &certificate) {
            Ok(kernel) => kernel,
            Err(e) => {
                let error = escape_control(&e.to_string());
                writeln!(out, "内核证明：失败（{error}）").ok();
                writeln!(out, "侧条件：未评估（内核证明失败）").ok();
                writeln!(out, "需人判断：未评估（内核证明失败）").ok();
                return Err(format!("证书校验失败（内核层）：{error}"));
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
                matches!(
                    conflict.resolution,
                    std_deduce_cert::Resolution::Unresolved { .. }
                )
            })
            .count();
        let requires_human = report.requires_human || unresolved > 0;

        // The certificate records the priority edge behind every defeat it
        // adjudicated; `check` compared each one with the environment. Report
        // what was compared instead of leaving the reader to assume it.
        let priority_text = if report.priority_edges_checked > 0 {
            format!("优先关系已核验（{} 条边）", report.priority_edges_checked)
        } else {
            "没有记录优先关系".to_owned()
        };
        writeln!(
            out,
            "侧条件：unless 未发现已成立的阻断条件；未决冲突 {unresolved} 项；{}{priority_text}",
            if report.conflict_resolved {
                "根冲突已按记录裁决；"
            } else {
                ""
            }
        )
        .ok();
        // A cycle in the environment disables the edges inside it. It is a
        // property of the environment, not of this certificate, so it is a
        // warning and never changes the exit code.
        write_priority_cycle_warning(out, &Reasoner::new(&self.lib.env).priority_cycles());
        writeln!(
            out,
            "需人判断：{}",
            human_summary(&certificate, requires_human, unresolved)
        )
        .ok();

        // An open concept the root derivation decided is named, so
        // "需人判断：是" points at which concept and which proof node. The
        // names come from the checker's recomputation, not from the recorded
        // description, which the checker has just validated field by field.
        write_open_concept_lines(out, &self.open_concepts(&certificate)?);

        // Case-local rules are recorded as an open obligation; name them so
        // "需人判断：是" points at what needs a human.
        write_local_extension_lines(out, &certificate);

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
        // The certificate is only as good as the packs it was derived from. A
        // non-official pack is accepted when the current environment has it,
        // but the reader must see that the conclusion depends on definitions
        // this project did not audit.
        let non_official: Vec<&std_deduce_cert::PackRecord> = current
            .packs
            .iter()
            .filter(|pack| pack.trust != TrustLevel::Official)
            .collect();
        if !non_official.is_empty() {
            let list = non_official
                .iter()
                .map(|pack| {
                    format!(
                        "{}@{}（{}）",
                        escape_control(&pack.name),
                        escape_control(&pack.version),
                        pack.trust
                    )
                })
                .collect::<Vec<_>>()
                .join("、");
            writeln!(
                out,
                "  注意：证书记录了非官方包：{list}；结论依赖这些包的定义"
            )
            .ok();
        }
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
                Some(CertNode::AxiomInstance { conclusion, .. }) => Expr::from(conclusion),
                Some(CertNode::InterpretationApplication { conclusion, .. }) => {
                    Expr::from(conclusion)
                }
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
    /// Each pack line shows its trust level as a label that says what the level
    /// means, followed by the maintainers, for a reviewed release the reviewer
    /// and date, the description behind a fixed `  说明：` prefix, and the file
    /// count. A pack whose manifest claims `official` is checked against
    /// `<root>/official.toml` before its line is printed: only a confirmed claim
    /// reads `official（本项目审核）`, any other claim reads
    /// `official（未通过白名单核对）`, and confirmation prints
    /// `白名单：通过（official.toml）` because the whitelist lists exactly the
    /// pack's name, version and locked hash. A missing whitelist, an unlisted
    /// release and a missing lock print a per-pack `路径: error: ...` line; an
    /// `official.toml` that cannot be read or validated prints one file-level
    /// `路径: error: ...` line. Every such error fails the command, and so does a
    /// failed lock verification (whose own error lines are printed instead of a
    /// whitelist verdict). A pack below `official` does not need to be listed,
    /// but a broken whitelist still fails the whole listing.
    ///
    /// When `root/std.lock` exists, the registry is verified before the listing
    /// is printed, so the whitelist verdict compares the hash of the lock that
    /// was just verified. Verification is skipped when the listing already
    /// failed, so a bad manifest is reported once.
    fn list_packs(&self, arg: &str, out: &mut impl Write) -> Result<Outcome, String> {
        let root = packs_root(arg)?;
        let found =
            std_deduce_lawpack::scan(&root).map_err(|error| escape_control(&error.to_string()))?;

        // The whitelist decides whether an `official` claim is honoured, so it
        // is read before the listing. A broken file is reported once, after the
        // pack blocks, with the registry's other errors.
        let mut whitelist_errors: Vec<PackError> = Vec::new();
        let whitelist = match read_whitelist(&root) {
            Ok(Some(whitelist)) => WhitelistState::Present(whitelist),
            Ok(None) => WhitelistState::Missing,
            Err(errors) => {
                whitelist_errors = errors;
                WhitelistState::Broken
            }
        };

        // Verify the lock before printing anything: an official pack's verdict
        // compares the hash the lock records, not a hash this command would
        // have to trust on its own. The status line is printed after the pack
        // blocks, as before.
        let (lock, lock_status, lock_errors) = inspect_lock(&root, !found.errors.is_empty());

        let mut corpus_errors = 0;
        let mut official_errors = 0;
        for pack in &found.packs {
            let info = &pack.manifest.pack;
            let manifest_path = pack.dir.join(MANIFEST_FILE);
            // The first line may only call a release audited when the
            // whitelist confirms it, so the verdict is decided before the line
            // is printed and reused for the whitelist report below.
            let verdict = (info.trust == Trust::Official)
                .then(|| official_verdict(&whitelist, &lock, &info.name, &info.version));
            let confirmed = matches!(verdict, Some(OfficialVerdict::Confirmed));
            writeln!(
                out,
                "{} {}  {}/{}  {}  {}  {}",
                info.name,
                info.version,
                info.jurisdiction,
                info.territory,
                effective_range(info),
                trust_label(info.trust, confirmed),
                escape_display_path(&pack.dir)
            )
            .ok();
            if !info.maintainers.is_empty() {
                writeln!(
                    out,
                    "  维护者：{}",
                    info.maintainers
                        .iter()
                        .map(|maintainer| escape_control(maintainer))
                        .collect::<Vec<_>>()
                        .join("、")
                )
                .ok();
            }
            if info.audit_status == AuditStatus::Reviewed {
                match (&info.audited_by, &info.audited_at) {
                    (Some(reviewer), Some(date)) => {
                        writeln!(
                            out,
                            "  审核：已审核（审核人 {}，{}）",
                            escape_control(reviewer),
                            escape_control(date)
                        )
                        .ok();
                    }
                    // Manifest validation rejects a reviewed pack without both
                    // fields, so this branch only renders a manifest the
                    // validator let through rather than inventing a reviewer.
                    _ => {
                        writeln!(out, "  审核：已审核（缺少审核人或审核日期）").ok();
                    }
                }
            }
            if let Some(verdict) = verdict {
                match verdict {
                    OfficialVerdict::Confirmed => {
                        writeln!(out, "  白名单：通过（{OFFICIAL_FILE}）").ok();
                    }
                    OfficialVerdict::Rejected(message) => {
                        official_errors += 1;
                        write_pack_error(out, &manifest_path, &message);
                    }
                    // The whitelist or lock error line already explains why no
                    // per-pack verdict is possible.
                    OfficialVerdict::Unverified => {}
                }
            }
            if let Some(description) = &info.description {
                writeln!(out, "  说明：{}", escape_control(description)).ok();
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
        if let Some(status) = lock_status {
            writeln!(out, "{}", escape_control(&status)).ok();
        }
        for error in &lock_errors {
            writeln!(out, "{}", escape_control(error)).ok();
        }
        for error in &whitelist_errors {
            write_pack_error(out, error.path(), error.message());
        }

        let errors = [
            (found.errors.len(), "法律包清单错误"),
            (lock_errors.len(), "锁定校验错误"),
            (corpus_errors, "语料错误"),
            (official_errors + whitelist_errors.len(), "官方白名单错误"),
        ];
        if errors.iter().any(|(count, _)| *count > 0) {
            return Err(listing_error(&errors));
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

/// The obligation id a certificate uses to list case-local rules it applied;
/// the certificate layer also recognizes it when it derives `需律师判断`.
const LOCAL_EXTENSION_ID: &str = LOCAL_EXTENSION_OBLIGATION_ID;

/// Check a top-level file against the closed-environment rules.
///
/// The closed environment accepts only a case file, so a module (a file with a
/// `namespace`) is refused: modules are legal packs and enter through `import`.
/// The case may state facts (`obj`, `axiom`) and query, but its legal concepts
/// must come from the loaded packs. A case that declares sorts, predicates,
/// definitions, rules, contraries, uniques or open-concept / risk-theme markers
/// is refused unless `--allow-case-rules` is given; the error names what was
/// declared so the author can move it into a pack or opt in explicitly.
///
/// Facts are checked too, because their *type* can carry a new legal concept:
/// an object must be declared at a sort from a loaded pack (not `Prop`, `Type`
/// or a function type), and an axiom's type must be a proposition (not `Prop`,
/// `Type` or a function type). A type that does not elaborate is left to
/// `lib.load`, which reports the unknown name with the closed-environment hint.
fn check_closed_case_file(
    path: &str,
    items: &[Item],
    namespace: Option<&str>,
    allow_case_rules: bool,
    env: &Env,
) -> Result<(), String> {
    if namespace.is_some() {
        return Err(std_deduce_lang::LoadError::new(
            "封闭环境（--closed-env）只接受案件文件（不带 namespace）；\
             模块文件必须作为法律包用 import 加载，不能直接 :load",
        )
        .render(path));
    }
    if allow_case_rules {
        return Ok(());
    }
    let mut declarations: Vec<String> = Vec::new();
    for item in items {
        match item {
            // A type that does not elaborate is left to `lib.load`, which
            // reports the unknown name with a closed-environment hint, so it is
            // not reported twice.
            Item::Obj { name, ty, .. } => {
                if let Ok(ety) = elab::elab_top(env, ty) {
                    if !is_pack_sort(env, &ety) {
                        declarations.push(format!("obj {name}（类型必须是已加载法律包里的 sort）"));
                    }
                }
            }
            Item::Axiom { name, ty, .. } => {
                if let Ok(ety) = elab::elab_top(env, ty) {
                    if check::check(env, &Ctx::new(), &ety, &Expr::Sort(0)).is_err() {
                        declarations.push(format!(
                            "axiom {name}（类型必须是命题，不能用 Prop/Type/函数类型造新概念）"
                        ));
                    }
                }
            }
            _ => {
                if let Some(declaration) = case_declaration(item) {
                    declarations.push(declaration);
                }
            }
        }
    }
    if declarations.is_empty() {
        return Ok(());
    }
    let listed = declarations
        .iter()
        .take(8)
        .map(|declaration| format!("`{declaration}`"))
        .collect::<Vec<_>>()
        .join("、");
    let listed = if declarations.len() > 8 {
        format!("{listed} 等 {} 项", declarations.len())
    } else {
        listed
    };
    Err(std_deduce_lang::LoadError::new(format!(
        "封闭环境（--closed-env）拒绝案件文件声明：{listed}。\
         案件文件只能 import 法律包并使用包内的 sort/pred/obj 与规则；\
         确需案件本地声明时加 --allow-case-rules（证书会把它标记为本地扩展）。"
    ))
    .render(path))
}

/// The closed-environment description of a declaration item, if it is one.
///
/// `contrary` and `unique` carry two names (the second is not a declaration
/// name), so they are written as the source writes them. `obj` and `axiom` have
/// no description here: their allowedness depends on the elaborated type and is
/// checked separately.
fn case_declaration(item: &Item) -> Option<String> {
    match item {
        Item::Sort { name, .. } => Some(format!("sort {name}")),
        Item::Pred { name, .. } => Some(format!("pred {name}")),
        Item::Def { name, .. } => Some(format!("def {name}")),
        Item::Rule { name, .. } => Some(format!("rule {name}")),
        Item::Interpretation { name, .. } => Some(format!("interpret {name}")),
        Item::Contrary { left, right, .. } => Some(format!("contrary {left} {right}")),
        Item::Unique { pred, index, .. } => Some(format!("unique {pred} {index}")),
        Item::Open { pred, .. } => Some(format!("open {pred}")),
        Item::Risk { theme, pred, .. } => Some(format!("risk {theme} {pred}")),
        _ => None,
    }
}

/// Whether an object's declared type is a sort from a loaded pack.
///
/// A plain individual is declared at a pack sort, for example
/// `obj 张三 : cn.constitution.人`. Any other type — `Prop`, `Type`, a function
/// type or a definition — would let the case name a legal concept, which the
/// closed environment does not allow without `--allow-case-rules`. This runs
/// before `lib.load`, so no case sort exists yet; [`record_case_extensions`]
/// additionally excludes sorts the case itself declared.
fn is_pack_sort(env: &Env, ty: &Expr) -> bool {
    let Expr::Const(name) = ty else {
        return false;
    };
    matches!(
        env.get(name.as_ref()).map(|decl| &decl.kind),
        Some(DeclKind::Sort)
    )
}

/// Whether a declaration is an individual, for display redaction.
///
/// An individual is a constant whose declared type is a sort: an `obj`
/// declaration (`obj 张三 : 公民`), or an `axiom` that only names a constant of
/// a sort (`axiom 张三 : 公民`). Predicates (their type ends in `Prop`),
/// definitions, sorts and asserted propositions are not individuals: redacting
/// them would erase the legal vocabulary the output is explaining. The check is
/// structural (the declared type's head is a declared sort), never a name list.
fn is_individual(env: &Env, decl: &Decl) -> bool {
    match &decl.kind {
        DeclKind::Obj => true,
        DeclKind::Axiom => match &decl.ty {
            Expr::Const(sort) => matches!(
                env.get(sort.as_ref()).map(|decl| &decl.kind),
                Some(DeclKind::Sort)
            ),
            _ => false,
        },
        _ => false,
    }
}

/// Collect every constant name an expression mentions.
fn expr_consts<'a>(expr: &'a Expr, out: &mut Vec<&'a str>) {
    match expr {
        Expr::Sort(_) | Expr::Var(_) => {}
        Expr::Const(name) => out.push(name.as_ref()),
        Expr::Pi {
            domain, codomain, ..
        } => {
            expr_consts(domain, out);
            expr_consts(codomain, out);
        }
        Expr::Lam { domain, body, .. } => {
            expr_consts(domain, out);
            expr_consts(body, out);
        }
        Expr::App { func, arg } => {
            expr_consts(func, out);
            expr_consts(arg, out);
        }
        Expr::Let { value, body, .. } => {
            expr_consts(value, out);
            expr_consts(body, out);
        }
    }
}

/// Record the declarations a case file added to the ledger.
///
/// `existing` is the set of declaration names from before the file loaded. The
/// kind declarations are recorded first, then the facts: an object is a plain
/// individual only when its type is a sort from a loaded pack — an object of a
/// sort this case declared, or of `Prop`/`Type`/a function type, is recorded
/// (`obj`). A fact is recorded when its type mentions any recorded extension
/// (`fact`); a plain fact stated with pack declarations and case objects is
/// not an extension. A non-proposition `axiom` is a local concept of its own
/// and is recorded too. Recording the kinds first lets a later fact see the
/// names this same file introduced.
fn record_case_extensions(
    lib: &Library,
    existing: &BTreeSet<String>,
    extensions: &mut BTreeMap<String, &'static str>,
) {
    for decl in lib.env.iter() {
        let name = decl.name.to_string();
        if existing.contains(&name) {
            continue;
        }
        let label = match &decl.kind {
            DeclKind::Sort => "sort",
            DeclKind::Pred => "pred",
            DeclKind::Def { .. } => "def",
            DeclKind::Rule(_) => "rule",
            DeclKind::Interpretation(_) => "interpret",
            DeclKind::Contrary { .. } => "contrary",
            DeclKind::Unique { .. } => "unique",
            DeclKind::OpenConcept { .. } => "open",
            DeclKind::Risk { .. } => "risk",
            DeclKind::Obj | DeclKind::Axiom | DeclKind::Fact { .. } | DeclKind::Priority { .. } => {
                continue
            }
        };
        extensions.insert(name, label);
    }
    for decl in lib.env.iter() {
        let name = decl.name.to_string();
        if existing.contains(&name) {
            continue;
        }
        match &decl.kind {
            DeclKind::Obj => {
                // The sort must come from a loaded pack, not from this case.
                // The kind pass above already recorded this file's own sorts,
                // and earlier loads recorded theirs, so their objects are
                // marked as extensions too.
                let is_pack_sort = match &decl.ty {
                    Expr::Const(const_name) => {
                        matches!(
                            lib.env.get(const_name.as_ref()).map(|decl| &decl.kind),
                            Some(DeclKind::Sort)
                        ) && !extensions.contains_key(const_name.as_ref())
                    }
                    _ => false,
                };
                if !is_pack_sort {
                    extensions.insert(name, "obj");
                }
            }
            DeclKind::Fact { .. } => {
                let mut consts = Vec::new();
                expr_consts(&decl.ty, &mut consts);
                // A fact's type is a proposition. It is a case extension only
                // when that proposition mentions a concept this case
                // introduced; a plain fact stated with pack declarations and
                // case objects does not.
                if consts
                    .iter()
                    .any(|const_name| extensions.contains_key(*const_name))
                {
                    extensions.insert(name, "fact");
                }
            }
            DeclKind::Axiom => {
                // The language gives every proposition-typed `axiom` a
                // `Fact`; an `Axiom` is therefore a constant the case declared
                // itself (`axiom P : Prop`, `axiom 恶意 : 人 → Prop`), which
                // is exactly a local legal concept.
                extensions.insert(name, "axiom");
            }
            _ => {}
        }
    }
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

/// Combine the independent error counts of a `:packs` run, omitting zeros.
///
/// A manifest or lock error used to be returned alone even when a linked corpus
/// had already failed to load; the stderr then under-reported the failures that
/// stdout had shown. Every nonzero count is reported instead.
fn listing_error(counts: &[(usize, &str)]) -> String {
    counts
        .iter()
        .filter(|(count, _)| *count > 0)
        .map(|(count, label)| format!("{count} 个{label}"))
        .collect::<Vec<_>>()
        .join("、")
}

/// Print one `:packs` problem as `path: error: message`.
///
/// Both parts are escaped, so a manifest, a whitelist or a lock cannot forge
/// another output line.
fn write_pack_error(out: &mut impl Write, path: &Path, message: &str) {
    writeln!(
        out,
        "{}: error: {}",
        escape_display_path(path),
        escape_control(message)
    )
    .ok();
}

/// What a trust level means, for a `:packs` listing line.
///
/// The label states the level's consequence, not only its wire name: an
/// `official` claim reads as audited only when `official_confirmed` is true, and
/// an unconfirmed claim says so instead of borrowing the audited label. The
/// lower levels never claim an audit.
fn trust_label(trust: Trust, official_confirmed: bool) -> &'static str {
    match trust {
        Trust::Official if official_confirmed => "official（本项目审核）",
        Trust::Official => "official（未通过白名单核对）",
        Trust::Community => "community（未经本项目审核）",
        Trust::Local => "local（本地自建）",
        Trust::Experimental => "experimental（实验性）",
    }
}

/// What a `:packs` run established about one pack's `official` claim.
enum OfficialVerdict {
    /// The whitelist lists exactly the pack's name, version and locked hash.
    Confirmed,
    /// The claim is not covered; the message is the diagnostic to print.
    Rejected(String),
    /// The registry's own errors already explain why no verdict is possible
    /// (a broken whitelist file or a failed lock check). The claim is still not
    /// confirmed.
    Unverified,
}

/// Decide whether an `official` claim is confirmed by the whitelist and lock.
///
/// An `official` pack is only audited when `official.toml` lists its name, the
/// manifest's version and the locked content hash, all three at once. A
/// registry without the file has no audited release, so the claim cannot be
/// verified and is a rejection rather than a lower trust level: silently
/// treating it as community would hide that the manifest asked for more.
fn official_verdict(
    whitelist: &WhitelistState,
    lock: &LockState,
    name: &str,
    version: &str,
) -> OfficialVerdict {
    match (whitelist, lock) {
        // The whitelist file's own error line already says why no per-pack
        // verdict is possible.
        (WhitelistState::Broken, _) => OfficialVerdict::Unverified,
        // The lock hash was not established; the lock errors say why.
        (_, LockState::Failed) => OfficialVerdict::Unverified,
        (_, LockState::Missing) => OfficialVerdict::Rejected(format!(
            "包 `{name}@{version}` 声明 trust = \"official\"，但注册表没有 std.lock，\
             没有锁哈希可以核对官方白名单"
        )),
        (WhitelistState::Missing, LockState::Verified(_)) => OfficialVerdict::Rejected(format!(
            "包 `{name}` 声明 trust = \"official\"，但注册表没有官方白名单 `{OFFICIAL_FILE}`"
        )),
        (WhitelistState::Present(whitelist), LockState::Verified(hashes)) => {
            match hashes.get(name) {
                Some(hash) if whitelist.covers(name, version, hash) => OfficialVerdict::Confirmed,
                Some(_) => OfficialVerdict::Rejected(format!(
                    "包 `{name}@{version}` 声明 trust = \"official\"，但未列入官方白名单，\
                     或锁哈希与白名单不一致；official 只用于本项目审核过的发行版"
                )),
                // `verify_lock` already requires every directory pack to be
                // locked, so a missing hash here would mean the lock check and
                // this lookup disagree.
                None => OfficialVerdict::Rejected(format!(
                    "包 `{name}@{version}` 不在 std.lock 中，没有锁哈希可以核对官方白名单"
                )),
            }
        }
    }
}

/// What a `:packs` run learned about the registry's lock.
enum LockState {
    /// `<root>/std.lock` does not exist.
    Missing,
    /// The lock verified; these are the locked hashes by pack name.
    Verified(BTreeMap<String, String>),
    /// Verification failed, or was skipped because the listing failed.
    Failed,
}

/// What a `:packs` run learned about the official whitelist.
enum WhitelistState {
    /// `<root>/official.toml` does not exist.
    Missing,
    /// The whitelist parsed.
    Present(Whitelist),
    /// The file exists but could not be read or validated; its errors were
    /// collected by the caller.
    Broken,
}

/// Verify `root/std.lock` without printing, and render its report lines.
///
/// Returns the state the whitelist verdict uses, the status line to print after
/// the pack blocks (absent when verification failed, because the error lines
/// are the report) and every error line. `listing_failed` skips verification so
/// one bad manifest is not reported twice. A successful check returns the hashes
/// of the lock it just compared with the directory, never a second read of the
/// file.
fn inspect_lock(root: &Path, listing_failed: bool) -> (LockState, Option<String>, Vec<String>) {
    if listing_failed {
        return (
            LockState::Failed,
            Some("锁定校验：未运行（清单错误）".to_owned()),
            Vec::new(),
        );
    }
    let lock_path = root.join(LOCK_FILE);
    match fs::symlink_metadata(&lock_path) {
        Ok(_) => match std_deduce_lawpack::verify_lock(root) {
            Ok(report) => {
                let hashes = report
                    .lockfile
                    .pack
                    .into_iter()
                    .map(|entry| (entry.name, entry.hash))
                    .collect();
                (
                    LockState::Verified(hashes),
                    Some(format!("锁定校验：通过（{} 个包）", report.verified)),
                    Vec::new(),
                )
            }
            Err(errors) => (
                LockState::Failed,
                None,
                errors.iter().map(|error| error.to_string()).collect(),
            ),
        },
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => (
            LockState::Missing,
            Some("锁定校验：未找到 std.lock（未锁定）".to_owned()),
            Vec::new(),
        ),
        Err(error) => (
            LockState::Failed,
            None,
            vec![format!("{}：无法读取锁文件：{error}", lock_path.display())],
        ),
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

/// Split `:review`'s argument into a goal and an optional output path.
///
/// The goal is everything before a standalone `--out` token; without `--out`
/// the whole argument is the goal. The path after `--out` is the rest of the
/// argument, so a path containing spaces needs no quotes; a path written in
/// double quotes is accepted as well and must not be followed by more text.
/// The `--out` token is recognised only at a whitespace boundary, so a
/// proposition that happens to contain the letters cannot steal the option.
fn split_review_argument(arg: &str) -> Result<(&str, Option<&str>), String> {
    let arg = arg.trim();
    if arg.is_empty() {
        return Err("用法：:review <命题> [--out <文件>]".into());
    }
    let mut found: Option<(usize, usize)> = None;
    for (position, _) in arg.match_indices("--out") {
        let before_ok = position == 0
            || arg[..position]
                .chars()
                .last()
                .is_some_and(char::is_whitespace);
        let after_position = position + "--out".len();
        let after_ok = after_position == arg.len()
            || arg[after_position..]
                .chars()
                .next()
                .is_some_and(char::is_whitespace);
        if before_ok && after_ok {
            if found.is_some() {
                return Err("用法错误：--out 只能使用一次".into());
            }
            found = Some((position, after_position));
        }
    }
    let Some((option_start, option_end)) = found else {
        return Ok((arg, None));
    };
    let goal = arg[..option_start].trim();
    if goal.is_empty() {
        return Err("用法：:review <命题> [--out <文件>]（--out 之前必须给出命题）".into());
    }
    let path = unquote_report_path(arg[option_end..].trim())?;
    Ok((goal, Some(path)))
}

/// The path after `--out`, optionally double-quoted.
fn unquote_report_path(path: &str) -> Result<&str, String> {
    if path.is_empty() {
        return Err("用法错误：--out 缺少文件路径".into());
    }
    if let Some(rest) = path.strip_prefix('"') {
        let Some(end) = rest.find('"') else {
            return Err("复核报告路径的引号未闭合".into());
        };
        let value = &rest[..end];
        let trailing = rest[end + 1..].trim();
        if !trailing.is_empty() {
            return Err(format!(
                "用法错误：--out 的路径后有多余内容 `{}`",
                escape_control(trailing)
            ));
        }
        if value.is_empty() {
            return Err("用法错误：--out 的文件路径为空".into());
        }
        return Ok(value);
    }
    Ok(path)
}

/// Write the report through a temporary file next to the destination.
///
/// The whole report exists before this is called. The temporary file lives in
/// the destination's own directory, so it is on the same file system and the
/// rename is atomic. If the destination already exists, its permission bits are
/// copied to the temporary file before the rename; a new destination gets the
/// directory's default permissions, exactly as a file created at that path
/// would. A failed write, permission copy or rename removes the temporary file
/// and returns an error, so the destination never contains half a report.
fn write_review_file(path: &str, report: &str) -> Result<(), String> {
    let destination = Path::new(path);
    let Some(file_name) = destination.file_name() else {
        return Err(format!(
            "写入复核报告 `{}` 失败：路径没有文件名",
            escape_path(path)
        ));
    };
    let parent = destination
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    let temporary = parent.join(format!(
        ".{}.tmp-{}",
        file_name.to_string_lossy(),
        std::process::id()
    ));
    let existing_permissions = match fs::metadata(destination) {
        Ok(meta) => {
            if meta.permissions().readonly() {
                return Err(format!(
                    "写入复核报告 `{}` 失败：目标不可写（只读）",
                    escape_path(path)
                ));
            }
            Some(meta.permissions())
        }
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => None,
        Err(error) => {
            return Err(format!(
                "写入复核报告 `{}` 失败：无法读取目标文件权限：{error}",
                escape_path(path)
            ));
        }
    };
    if let Err(error) = fs::write(&temporary, report) {
        let _ = fs::remove_file(&temporary);
        return Err(format!(
            "写入复核报告 `{}` 失败：{error}",
            escape_path(path)
        ));
    }
    if let Some(permissions) = existing_permissions {
        if let Err(error) = fs::set_permissions(&temporary, permissions) {
            let _ = fs::remove_file(&temporary);
            return Err(format!(
                "写入复核报告 `{}` 失败：无法设置报告文件权限：{error}",
                escape_path(path)
            ));
        }
    }
    if let Err(error) = fs::rename(&temporary, destination) {
        let _ = fs::remove_file(&temporary);
        return Err(format!(
            "写入复核报告 `{}` 失败：{error}",
            escape_path(path)
        ));
    }
    Ok(())
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

/// Render one field's provenance as a compact `（规则）` / `（继承）` / `（案件）`
/// marker, or nothing for a value with no recorded origin.
fn scope_origin_marker(origin: Option<ScopeOrigin>) -> String {
    match origin {
        Some(origin) => format!("（{}）", origin.label_zh()),
        None => String::new(),
    }
}

/// Render the range's provenance in endpoint order, collapsing equal origins.
///
/// A range that mixes an explicit start with an inherited end reads
/// `（规则/继承）`, so a reader does not have to guess which endpoint came from
/// the rule and which from the manifest.
fn scope_range_marker(scope: &Scope) -> String {
    let mut origins: Vec<ScopeOrigin> = Vec::new();
    for origin in [scope.effective_from_origin, scope.effective_to_origin]
        .into_iter()
        .flatten()
    {
        if !origins.contains(&origin) {
            origins.push(origin);
        }
    }
    match origins.as_slice() {
        [] => String::new(),
        [one] => format!("（{}）", one.label_zh()),
        many => format!(
            "（{}）",
            many.iter()
                .map(|origin| origin.label_zh())
                .collect::<Vec<_>>()
                .join("/")
        ),
    }
}

/// Render a declaration's recorded scope for `:inspect`.
///
/// Only declared or inherited fields are shown; an absent field prints nothing
/// (never a `默认` placeholder, and never a guessed value). Each value carries
/// its provenance: `（规则）` for a value written on the rule, `（继承）` for a
/// pack-manifest default, and `（案件）` for a case-local rule. The effective
/// range is `from..to` with an open endpoint left empty.
fn declared_scope_text(scope: &Scope) -> String {
    let mut parts = Vec::new();
    let range = match (&scope.effective_from, &scope.effective_to) {
        (Some(from), Some(to)) => format!("{from}..{to}"),
        (Some(from), None) => format!("{from}.."),
        (None, Some(to)) => format!("..{to}"),
        (None, None) => String::new(),
    };
    if !range.is_empty() {
        parts.push(format!("〔生效 {range}{}〕", scope_range_marker(scope)));
    }
    if let Some(code) = &scope.jurisdiction {
        parts.push(format!(
            "〔管辖 {code}{}〕",
            scope_origin_marker(scope.jurisdiction_origin)
        ));
    }
    if let Some(code) = &scope.territory {
        parts.push(format!(
            "〔地域 {code}{}〕",
            scope_origin_marker(scope.territory_origin)
        ));
    }
    parts.concat()
}

/// Render a fact's recorded occurrence for `:inspect`.
///
/// Only facts carry occurred fields, and an unrecorded one prints nothing; the
/// session's as-of date is not copied into it.
fn declared_occurrence_text(decl: &Decl) -> String {
    let mut parts = Vec::new();
    if let Some(date) = &decl.occurred_at {
        parts.push(format!("〔发生 {date}〕"));
    }
    if let Some(code) = &decl.occurred_in {
        parts.push(format!("〔发生地 {code}〕"));
    }
    parts.concat()
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

/// Print one `此处需人判断：`<concept>`` line per open concept the root
/// derivation decided.
///
/// The names are the checked recomputation of the environment's `open` markers
/// and the proof graph, never text parsed out of the certificate. They are
/// escaped, so a concept name cannot forge another output line.
fn write_open_concept_lines(out: &mut impl Write, concepts: &[String]) {
    for concept in concepts {
        writeln!(out, "  此处需人判断：`{}`", escape_control(concept)).ok();
    }
}

/// Print one `  本地扩展：...` line per case-local-extension obligation.
///
/// The description comes from the certificate, so it is escaped before it is
/// printed: a hand-edited certificate must not be able to forge another output
/// line.
fn write_local_extension_lines(out: &mut impl Write, certificate: &Certificate) {
    for obligation in certificate
        .open_obligations
        .iter()
        .filter(|obligation| obligation.id == LOCAL_EXTENSION_ID)
    {
        writeln!(
            out,
            "  本地扩展：{}",
            escape_control(&obligation.description)
        )
        .ok();
    }
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
        // The root is one side of an accepted unresolved factual standoff.
        // The check passed because the certificate is honest about not
        // deciding it, not because the root is settled: never say "已证明"
        // here, whatever the node kind or fact identity.
        Some(root) if report.root_conflict_unresolved => {
            let identity = match &certificate.nodes[root] {
                CertNode::Assumption { assumption } => certificate
                    .assumptions
                    .get(*assumption)
                    .map(|assumption| assumption.identity),
                _ => None,
            };
            match identity {
                Some(identity) if std_deduce_kernel::FactIdentity::from(&identity).is_strict() => {
                    "根为已登记的严格事实，但与另一严格事实的冲突未决".to_owned()
                }
                Some(identity) => format!(
                    "根为已登记的事实（{}），但与另一事实的冲突未决",
                    identity.label_zh()
                ),
                None => "根命题与另一事实的冲突未决，根不是已证明的结论".to_owned(),
            }
        }
        Some(root) if report.root_proved && report.root_is_assumption => {
            // The root's proposition is an assumption; its identity says who
            // asserts it, and the assumption table is the only record of it.
            let identity = match &certificate.nodes[root] {
                CertNode::Assumption { assumption } => certificate
                    .assumptions
                    .get(*assumption)
                    .map(|assumption| assumption.identity.label_zh()),
                _ => None,
            };
            let identity = match identity {
                Some(label) => format!("（{label}）"),
                None => String::new(),
            };
            format!(
                "根已证明，根为假设{identity}，证书共 {} 条假设",
                report.assumption_count
            )
        }
        Some(_) if report.root_proved => {
            let derived_by = match certificate.root {
                Some(root)
                    if matches!(
                        certificate.nodes[root],
                        CertNode::InterpretationApplication { .. }
                    ) =>
                {
                    "解释推导"
                }
                Some(root) if matches!(certificate.nodes[root], CertNode::AxiomInstance { .. }) => {
                    "公理实例推导"
                }
                _ => "规则推导",
            };
            format!(
                "根已证明，根为{derived_by}，证书共 {} 条假设",
                report.assumption_count
            )
        }
        Some(_) => "根未被证明".to_owned(),
    }
}

/// Print the one-line trust summary next to a query's result line.
///
/// The line is [`TrustReport::summary`], which comes from [`derive_trust`] over
/// the certificate the command is also rendering and checking. `:why`,
/// `:explain` and `:labels` all print this same string for the same target.
fn write_trust_line(out: &mut impl Write, trust: &TrustReport) {
    writeln!(out, "{}", trust.summary()).ok();
}

/// Print the one explicit high-risk line and its evidence, or the one
/// non-judgment hint when the case declares no `risk` covering this derivation.
///
/// A high-risk derivation prints exactly one warning line, followed by one
/// `  依据：…` line per proving node, so the reader can see which proposition,
/// rule and source produced the grading. A case without a matching declaration
/// prints at most one `提示：…` line from a small documented word list; that line
/// says it is only a hint, and it changes no label and no exit code. Neither
/// branch prints anything when there is nothing to say: a clean case must not be
/// buried under a line that says "no risk".
fn write_risk_warning(out: &mut impl Write, risk: &RiskReport) {
    if let Some(warning) = risk.warning_line() {
        writeln!(out, "{warning}").ok();
        for theme in risk.themes() {
            for evidence in risk.evidence(*theme) {
                writeln!(out, "  依据：{evidence}").ok();
            }
        }
        return;
    }
    if let Some(hint) = risk.hint_line() {
        writeln!(out, "{hint}").ok();
    }
}

/// Print the risk themes as the second-label section of `:labels`.
///
/// The section is separate from the five trust labels on purpose: the trust
/// labels say why the model may not decide (an open concept, a claim, a gap),
/// the risk themes say what the case is about. Both can hold at once, so a
/// theme is never folded into `需律师判断`. The non-judgment hint is deliberately
/// not printed here: `:labels` reports the certificate's declared themes and
/// must not be affected by a word-list hint.
fn write_risk_section(out: &mut impl Write, risk: &RiskReport) {
    if !risk.is_high_risk() {
        return;
    }
    writeln!(
        out,
        "题材风险（次标签，与上面的五种信任标签相互独立，不并入「需律师判断」）："
    )
    .ok();
    if let Some(warning) = risk.warning_line() {
        writeln!(out, "  {warning}").ok();
    }
    for theme in risk.themes() {
        writeln!(out, "  {}", theme.label_zh()).ok();
        for evidence in risk.evidence(*theme) {
            writeln!(out, "    - {evidence}").ok();
        }
    }
}

/// Print the short statement every result output carries once.
fn write_disclaimer(out: &mut impl Write) {
    writeln!(out, "{DISCLAIMER_LINE}").ok();
}

/// Print the `:cert` explanation lines before the certificate JSON.
///
/// The lines stay outside the JSON on purpose: certificate v8 gains no field,
/// and everything from the first `{` on is still the certificate itself.
fn write_cert_notice(out: &mut impl Write) {
    for line in CERT_NOTICE {
        writeln!(out, "{line}").ok();
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

fn report_unresolved(
    out: &mut impl Write,
    r: &Reasoner,
    goal: &Expr,
    c: &Conflict,
    reason: &std_deduce_reason::UnresolvedReason,
) {
    writeln!(out, "冲突未决：{}", print_expr(goal)).ok();
    writeln!(
        out,
        "  该结论没有进入事实库——系统不替你选，但也绝不悄悄丢掉它。"
    )
    .ok();
    write_unresolved_reason(out, r, c, reason);
    writeln!(
        out,
        "  左：{}  ← {}",
        print_expr(&c.left),
        describe(&c.left_by, r.identity_of(&c.left))
    )
    .ok();
    writeln!(
        out,
        "  右：{}  ← {}",
        print_expr(&c.right),
        describe(&c.right_by, r.identity_of(&c.right))
    )
    .ok();
    for (label, prop) in [("左", &c.left), ("右", &c.right)] {
        writeln!(out, "── 冲突{label}方：{} ──", print_expr(prop)).ok();
        show_derivation(out, r, prop);
    }
}

/// Print why a conflict has no winner.
///
/// The reason is part of the derivation, not a diagnostic: "no priority was
/// declared" and "priorities were declared but do not decide" call for
/// different work. An unusable priority lists every declared edge, because
/// that list is the audit trail the reader has to inspect. A conflict about a
/// fact names the fact's proposition and its identity, because "a user
/// assertion is not proof" and "an analysis assumption is not proof" call for
/// different work.
fn write_unresolved_reason(
    out: &mut impl Write,
    r: &Reasoner,
    c: &Conflict,
    reason: &std_deduce_reason::UnresolvedReason,
) {
    use std_deduce_reason::UnresolvedReason;
    match reason {
        UnresolvedReason::NoPriority => {
            if matches!(c.left_by, Provenance::Interpretation(_))
                || matches!(c.right_by, Provenance::Interpretation(_))
            {
                writeln!(
                    out,
                    "  原因：解释结论与另一方之间没有可用的优先声明，不能判定谁胜出"
                )
                .ok();
            } else {
                writeln!(out, "  原因：两侧规则之间没有声明任何优先关系").ok();
            }
        }
        UnresolvedReason::PriorityUnusable { declared } => {
            let order = r.priority_order();
            let in_cycle = declared
                .iter()
                .filter(|edge| order.same_cycle(&edge.winner, &edge.loser))
                .count();
            let cycle_note = if in_cycle > 0 {
                format!("（其中 {in_cycle} 条落在优先级环内）")
            } else {
                String::new()
            };
            writeln!(
                out,
                "  原因：已声明 {} 条优先关系，但不足以裁决{cycle_note}",
                declared.len()
            )
            .ok();
            writeln!(out, "    已声明：").ok();
            for edge in declared {
                writeln!(out, "      {}", declared_edge_line(edge)).ok();
            }
        }
        UnresolvedReason::UnknownWitnesses => {
            writeln!(out, "  原因：某侧的规则见证已无法重建").ok();
        }
        UnresolvedReason::ConflictingAssumptions => {
            let left = r.identity_of(&c.left);
            let right = r.identity_of(&c.right);
            match (left, right) {
                (Some(left), Some(right)) if left.is_strict() && right.is_strict() => {
                    writeln!(out, "  原因：两侧都是严格事实，事实之间没有先后").ok();
                }
                (Some(left), Some(right)) if !left.is_strict() && !right.is_strict() => {
                    writeln!(out, "  原因：两侧都只是主张，未经证明，不能判出一方胜出").ok();
                }
                // One strict fact and one claim is defeated, not unresolved, so
                // an unmatched or mixed pair cannot be described by identity.
                // Fall back to the reason-only wording instead of guessing one.
                _ => {
                    writeln!(out, "  原因：两侧都是事实，身份无法确定，不能判出一方胜出").ok();
                }
            }
        }
        UnresolvedReason::NonStrictFact { identity } => {
            // The reason records only the claim's identity; the claim's
            // proposition comes from the conflict, whose fact side is the one
            // `resolve` recorded as an assumption. The other side names what
            // the claim does not automatically beat: a rule conclusion, or an
            // interpretation conclusion (which is never a rule step).
            let fact_side = match (&c.left_by, &c.right_by) {
                (Provenance::Assumption, _) => Some(&c.left),
                (_, Provenance::Assumption) => Some(&c.right),
                _ => None,
            };
            let beaten = if matches!(c.left_by, Provenance::Interpretation(_))
                || matches!(c.right_by, Provenance::Interpretation(_))
            {
                "解释结论"
            } else {
                "规则结论"
            };
            match fact_side {
                Some(prop) => writeln!(
                    out,
                    "  原因：「{}」只是「{}」，未经证明，不能自动胜过{beaten}",
                    print_expr(prop),
                    identity.label_zh()
                )
                .ok(),
                None => writeln!(
                    out,
                    "  原因：一侧只是「{}」，未经证明，不能自动胜过{beaten}",
                    identity.label_zh()
                )
                .ok(),
            };
        }
    }
}

/// One declared priority edge as `:why` lists it under `已声明：`.
///
/// A top-level `priority` is claimed by a namespace; a rule-internal clause is
/// claimed by the rule that carries it.
fn declared_edge_line(edge: &std_deduce_reason::PriorityEdge) -> String {
    match &edge.origin {
        std_deduce_reason::PriorityOrigin::Declaration {
            declared_in,
            sources,
        } => format!(
            "{declared_in}：priority {} over {}（出处：{}）",
            edge.winner,
            edge.loser,
            reason_sources_text(sources)
        ),
        std_deduce_reason::PriorityOrigin::RuleClause {
            rule,
            clause,
            sources,
        } => reason_clause_line(rule, *clause, sources),
    }
}

/// One priority edge as the stated basis of a defeat.
fn reason_basis_edge_line(edge: &std_deduce_reason::PriorityEdge) -> String {
    match &edge.origin {
        std_deduce_reason::PriorityOrigin::Declaration {
            declared_in,
            sources,
        } => format!(
            "{declared_in} 的 priority {} over {}（出处：{}）",
            edge.winner,
            edge.loser,
            reason_sources_text(sources)
        ),
        std_deduce_reason::PriorityOrigin::RuleClause {
            rule,
            clause,
            sources,
        } => reason_clause_line(rule, *clause, sources),
    }
}

/// A rule-internal `defeated_by` / `prefer` clause as one line.
fn reason_clause_line(
    rule: &Name,
    clause: std_deduce_reason::PriorityClause,
    sources: &[SourceRef],
) -> String {
    let clause = match clause {
        std_deduce_reason::PriorityClause::Prefer => "prefer",
        std_deduce_reason::PriorityClause::DefeatedBy => "defeated_by",
    };
    format!(
        "规则 {rule} 的 {clause} 子句（出处：{}）",
        reason_sources_text(sources)
    )
}

/// The provenance of a reasoner-side priority edge as `text locator`, joining
/// several sources with `、`. Every field is escaped: source text is data.
fn reason_sources_text(sources: &[SourceRef]) -> String {
    sources
        .iter()
        .map(|source| citation_text(&source.text, &source.locator))
        .collect::<Vec<_>>()
        .join("、")
}

/// `text locator`, with both fields escaped.
fn citation_text(text: &str, locator: &str) -> String {
    format!("{} {}", escape_control(text), escape_control(locator))
}

/// Print the `  依据：...` lines of a defeat the reasoner recorded.
///
/// `loser` is the provenance of the side that lost. A strict fact outranks
/// both a defeasible rule conclusion and a claim, but the two are different
/// statements about why the loser could not stand, so they are not merged.
fn write_reason_basis(
    out: &mut impl Write,
    basis: &std_deduce_reason::ResolutionBasis,
    loser: &Provenance,
) {
    match basis {
        std_deduce_reason::ResolutionBasis::Assumption => {
            let text = if matches!(loser, Provenance::Interpretation(_)) {
                "严格事实优先于解释结论。"
            } else {
                strict_fact_basis_text(matches!(loser, Provenance::Rules(_)))
            };
            writeln!(out, "  依据：{text}").ok();
        }
        std_deduce_reason::ResolutionBasis::Priority { edges } => {
            for edge in edges {
                writeln!(out, "  依据：{}", reason_basis_edge_line(edge)).ok();
            }
        }
    }
}

/// The stated basis when a strict fact defeats the other side.
fn strict_fact_basis_text(loser_is_rule: bool) -> &'static str {
    if loser_is_rule {
        "严格事实优先于可废止规则结论。"
    } else {
        "严格事实优先于未经证明的主张。"
    }
}

/// Print the `  依据：...` lines of a defeat the certificate records.
///
/// `loser` is the provenance the certificate records for the losing side, so
/// the same split between a defeasible conclusion and a claim applies.
fn write_certificate_basis(
    out: &mut impl Write,
    basis: &ResolutionBasis,
    loser: &std_deduce_cert::Provenance,
) {
    match basis {
        ResolutionBasis::Assumption => {
            let text = if matches!(loser, std_deduce_cert::Provenance::Interpretation { .. }) {
                "严格事实优先于解释结论。"
            } else {
                strict_fact_basis_text(matches!(loser, std_deduce_cert::Provenance::Rules { .. }))
            };
            writeln!(out, "  依据：{text}").ok();
        }
        ResolutionBasis::Priority { edges } => {
            for edge in edges {
                writeln!(out, "  依据：{}", certificate_edge_line(edge)).ok();
            }
        }
    }
}

/// One certificate-side priority edge as the stated basis of a defeat.
fn certificate_edge_line(edge: &PriorityEdge) -> String {
    match &edge.origin {
        PriorityOrigin::PriorityDeclaration {
            declared_in,
            sources,
        } => format!(
            "{declared_in} 的 priority {} over {}（出处：{}）",
            edge.winner,
            edge.loser,
            certificate_sources_text(sources)
        ),
        PriorityOrigin::RuleClause {
            declaring_rule,
            clause,
            rule_sources,
        } => {
            let clause = match clause {
                PriorityClause::Prefer => "prefer",
                PriorityClause::DefeatedBy => "defeated_by",
            };
            format!(
                "规则 {declaring_rule} 的 {clause} 子句（出处：{}）",
                certificate_sources_text(rule_sources)
            )
        }
    }
}

/// The provenance of a certificate-side priority edge as `text locator`,
/// joining several sources with `、`. Every field is escaped: a hand-edited
/// certificate is untrusted input.
fn certificate_sources_text(sources: &[Source]) -> String {
    sources
        .iter()
        .map(|source| citation_text(&source.text, &source.locator))
        .collect::<Vec<_>>()
        .join("、")
}

fn report_defeated(
    out: &mut impl Write,
    r: &Reasoner,
    goal: &Expr,
    c: &Conflict,
    winner: Side,
    basis: &std_deduce_reason::ResolutionBasis,
) {
    let (win, win_by) = match winner {
        Side::Left => (&c.left, &c.left_by),
        Side::Right => (&c.right, &c.right_by),
    };
    let loser_by = match winner {
        Side::Left => &c.right_by,
        Side::Right => &c.left_by,
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
        describe(win_by, r.identity_of(win))
    )
    .ok();
    write_reason_basis(out, basis, loser_by);
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
    let certificate = match reason_certificate(r.env(), &d, &r.priority_order()) {
        Ok(certificate) => certificate,
        Err(error) => {
            writeln!(out, "  （该推导未能生成证书：{error}）").ok();
            return;
        }
    };
    let annotations = derivation_annotations(&d);
    match render_with_annotations(&certificate, &annotations) {
        Ok(rendered) => {
            // Each rule application's conclusion line carries its verdict and
            // evidence inline, so a conflict side is judged exactly as a
            // normal derivation.
            writeln!(out, "{rendered}").ok();
        }
        Err(error) => {
            writeln!(out, "  （该推导的证书无法渲染：{error}）").ok();
            return;
        }
    };
    // Display projection only: `check_display_projection` skips the
    // certificate-wide conflict-completeness scan, so its "ok" says the
    // one-sided tree is internally consistent — never that a certificate is
    // valid. The wording below must not claim independent verification.
    match std_deduce_cert::check_display_projection(r.env(), &certificate) {
        Ok(report) if report.root_proved => {
            writeln!(
                out,
                "  （该单侧展示的节点检查通过；证书有效性以完整证书的校验为准）"
            )
            .ok();
        }
        Ok(_) => {
            writeln!(
                out,
                "  （该单侧展示的节点检查未通过：根未被证明；证书有效性以完整证书的校验为准）"
            )
            .ok();
        }
        Err(error) => {
            writeln!(
                out,
                "  （该单侧展示的节点检查未通过：{}）",
                escape_control(&error.to_string())
            )
            .ok();
        }
    }
}

/// Print every conflict the certificate records.
fn report_conflicts(out: &mut impl Write, certificate: &Certificate) {
    for conflict in &certificate.conflicts {
        let how = match conflict.resolution {
            std_deduce_cert::Resolution::Unresolved { .. } => "未决",
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

/// Collect every rule and its verdict anywhere in a gap tree, including nested
/// candidates, so the report covers the whole tree.
fn collect_gap_verdicts(tree: &GapTree, out: &mut BTreeSet<(String, String)>) {
    for candidate in &tree.candidates {
        out.insert((
            candidate.rule.to_string(),
            candidate.applicability.summary_zh(),
        ));
        for premise in &candidate.missing {
            if let Some(child) = &premise.gap {
                collect_gap_verdicts(child, out);
            }
        }
    }
}

/// Collect the rules a derivation actually cites, walking from the root
/// through the premises that support it, together with the per-instance
/// verdict and the event times/places it relied on.
///
/// Rules that happen to be applied elsewhere in the settled state but not in
/// this goal's cone are not listed: `:applicability <goal>` answers for the
/// goal. A gap node carries its candidates' verdicts; a rule-application node
/// carries the verdict it fired under.
fn collect_derivation_verdicts(
    derivation: &Derivation,
    node: usize,
    out: &mut BTreeSet<(String, String)>,
) {
    match &derivation.nodes[node] {
        ReasonNode::Assumption { .. } => {}
        ReasonNode::RuleApplication {
            rule,
            premises,
            applicability,
            ..
        } => {
            out.insert((rule.to_string(), applicability.summary_zh()));
            for premise in premises {
                collect_derivation_verdicts(derivation, *premise, out);
            }
        }
        ReasonNode::InterpretationApplication { premise, .. } => {
            collect_derivation_verdicts(derivation, *premise, out);
        }
        ReasonNode::AxiomInstance { .. } => {}
        ReasonNode::Gap { candidates, .. } => {
            for candidate in candidates {
                out.insert((
                    candidate.rule.to_string(),
                    candidate.applicability.summary_zh(),
                ));
            }
        }
    }
}

/// The per-node annotation the certificate renderer prints on a rule
/// application's conclusion line.
///
/// The certificate format records no verdict, but the reasoner's derivation
/// nodes do and keep the same order, so the node id is enough to line them up.
/// Every applied rule is annotated: `适用性未判定（…）` when the judgement
/// lacked input (the rule still fired), and `适用（事件时间 …）` for a clean
/// verdict. An inapplicable or undecidable rule cannot appear here because it
/// never fired.
fn derivation_annotations(derivation: &Derivation) -> BTreeMap<usize, String> {
    derivation
        .nodes
        .iter()
        .enumerate()
        .filter_map(|(id, node)| match node {
            ReasonNode::RuleApplication { applicability, .. } => {
                Some((id, applicability.summary_zh()))
            }
            _ => None,
        })
        .collect()
}

/// Print the applicability of the gap candidates at the root of a derivation.
///
/// A gap root's candidate lines are rendered from the certificate, whose
/// format has no verdict, so the state is printed here. A rule application's
/// own conclusion line carries its verdict inline instead.
fn write_gap_applicability_notes(out: &mut impl Write, derivation: &Derivation, root: usize) {
    let ReasonNode::Gap { candidates, .. } = &derivation.nodes[root] else {
        return;
    };
    let mut verdicts = BTreeSet::new();
    for candidate in candidates {
        verdicts.insert((
            candidate.rule.to_string(),
            candidate.applicability.summary_zh(),
        ));
    }
    write_applicability_verdicts(out, &verdicts);
}

/// Print one `⟨rule⟩：verdict` line per distinct verdict, sorted by rule and
/// then by the rendered verdict (so the order never depends on traversal).
fn write_applicability_verdicts(out: &mut impl Write, verdicts: &BTreeSet<(String, String)>) {
    if verdicts.is_empty() {
        return;
    }
    writeln!(out, "时空适用性：").ok();
    for (rule, verdict) in verdicts {
        writeln!(out, "  ⟨{rule}⟩：{verdict}").ok();
    }
}

/// Print one hint per unenabled interpretation that could prove the queried
/// goal in one more step. The reasoner only suggests: nothing is applied.
fn write_interpretation_hints(
    out: &mut impl Write,
    reasoner: &Reasoner<'_>,
    goal: &Expr,
) -> Result<(), String> {
    for hint in reasoner.unused_interpretation_hints(goal)? {
        writeln!(
            out,
            "  存在未启用解释 `{}`（{} → {}）；用 :interpret enable {} 后重查",
            escape_control(&hint.id),
            print_expr(&hint.from),
            print_expr(&hint.to),
            escape_control(&hint.id)
        )
        .ok();
    }
    Ok(())
}

/// Register the ledger facts, saturate, and — when the goal is still unproved —
/// demand a universal-elimination instance for it and saturate again.
///
/// The second pass runs only when the first one did not prove the goal, so an
/// existing rule derivation is never displaced by an axiom instance. Demanding
/// a goal is the query-level trigger; premise-driven instantiation already
/// happens inside the saturation itself.
fn saturate_with_goal(r: &mut Reasoner<'_>, goal: Option<&Expr>) -> Result<(), String> {
    r.assume_ledger_axioms()?;
    r.saturate()?;
    if let Some(goal) = goal {
        if !r.knows(goal) {
            r.demand(goal)?;
            r.saturate()?;
        }
    }
    Ok(())
}

/// Build a reasoner with the given enabled interpretations.
///
/// This is the only place the CLI turns the session's set into reasoner state;
/// the empty set produces exactly the default reasoner.
fn configured_reasoner<'a>(
    env: &'a Env,
    enabled: &BTreeSet<String>,
) -> Result<Reasoner<'a>, String> {
    let mut reasoner = Reasoner::new(env);
    for id in enabled {
        reasoner.enable_interpretation(id)?;
    }
    Ok(reasoner)
}

/// Render one gap tree, with `label` on its root line.
///
/// The tree is the reasoner's own recursion: every missing premise with a
/// child gap is printed under the premise that needs it, indented one level
/// deeper, so the output shows *what* is missing, *why* it is missing and
/// *which rule* could use it. Limits are printed where they stopped the
/// expansion; a truncated branch is never left looking like a complete one.
fn render_gap_tree(
    out: &mut impl Write,
    tree: &GapTree,
    reasoner: &Reasoner<'_>,
    indent: usize,
    label: &str,
) {
    writeln!(
        out,
        "{}{label} ⟨{}⟩",
        " ".repeat(indent),
        print_expr(&tree.goal)
    )
    .ok();
    render_gap_body(out, tree, reasoner, indent + 2);
}

fn render_gap_body(out: &mut impl Write, tree: &GapTree, reasoner: &Reasoner<'_>, indent: usize) {
    let pad = " ".repeat(indent);
    match tree.status {
        GapStatus::Proved => {
            writeln!(out, "{pad}目标已可推出。").ok();
            return;
        }
        GapStatus::InterpretedOnly => {
            writeln!(
                out,
                "{pad}该命题已由解释推出，但规则阶段不消费解释结论，因此作为规则前提仍不算满足。"
            )
            .ok();
            return;
        }
        GapStatus::Conflicted => {
            writeln!(
                out,
                "{pad}目标处于冲突中：未决的结论不进入事实库，需要人工裁决。"
            )
            .ok();
            return;
        }
        GapStatus::Defeated => {
            writeln!(out, "{pad}目标在已裁决的冲突中败出，按记录不进入事实库。").ok();
            return;
        }
        GapStatus::NotAProposition => {
            writeln!(out, "{pad}目标不是命题。").ok();
            return;
        }
        GapStatus::OpenPattern => {
            writeln!(out, "{pad}前提含有未随目标闭合的规则参数，无法继续展开。").ok();
            return;
        }
        GapStatus::Cycle => {
            writeln!(out, "{pad}循环依赖：同一命题已在当前展开路径上，停止递归。").ok();
            return;
        }
        GapStatus::Unreachable => {}
    }
    if tree.candidates.is_empty() && tree.axiom_candidates.is_empty() && tree.limit.is_none() {
        writeln!(
            out,
            "{pad}没有任何规则以它为结论：要么补一条规则，要么把它作为已知事实登记。"
        )
        .ok();
    }
    for candidate in &tree.axiom_candidates {
        // A universal fact that unifies with the goal, with the bindings an
        // instance would need. A successful instance would have closed the
        // goal, so every listed candidate either was refused or was not
        // demanded on this path.
        let bindings = if candidate.bindings.is_empty() {
            String::new()
        } else {
            format!("（绑定：{}）", instance_bindings_text(&candidate.bindings))
        };
        writeln!(out, "{pad}公理候选 ⟨{}⟩{bindings}", candidate.axiom).ok();
        match &candidate.problem {
            Some(problem) => writeln!(out, "{pad}  未实例化：{problem}").ok(),
            None => writeln!(out, "{pad}  可由该全称公理实例化；当前推导没有触发它").ok(),
        };
    }
    for candidate in &tree.candidates {
        // Every candidate carries its per-instance verdict and the event
        // times/places it relied on: an excluded rule is listed, not hidden,
        // and an unchecked one cannot pass for a normal candidate.
        writeln!(
            out,
            "{pad}候选 ⟨{}⟩〔{}〕",
            candidate.rule,
            candidate.applicability.summary_zh()
        )
        .ok();
        if matches!(candidate.applicability, Applicability::Undecidable { .. }) {
            writeln!(
                out,
                "{pad}  提示：需要为该争点显式指定引用时间（尚未实现）。"
            )
            .ok();
        }
        if !candidate.missing.is_empty() {
            writeln!(
                out,
                "{pad}  判定口径：按已持有事实；补上缺失前提后判定可能变化。"
            )
            .ok();
        }
        for source in &candidate.sources {
            writeln!(out, "{pad}  ← {}", source.one_line()).ok();
        }
        for missing in &candidate.missing {
            writeln!(
                out,
                "{pad}  缺 ⟨{}⟩{}",
                print_expr(&missing.premise),
                requirement_burden_note(reasoner, candidate.rule.as_ref())
            )
            .ok();
            if let Some(child) = &missing.gap {
                render_gap_body(out, child, reasoner, indent + 4);
            }
        }
        for blocker in &candidate.blocked_by {
            // A blocker can be a session fact; its identity is part of why it
            // blocks, and a reasoner-derived conclusion has none.
            let identity = reasoner
                .identity_of(blocker)
                .map(|identity| format!("〔{}〕", identity.label_zh()))
                .unwrap_or_default();
            writeln!(
                out,
                "{pad}  被阻断：「{}」{}已成立，故本规则不触发{}",
                print_expr(blocker),
                identity,
                exception_burden_note(reasoner, candidate.rule.as_ref())
            )
            .ok();
        }
        if let Some(limit) = &candidate.limit {
            writeln!(
                out,
                "{pad}  已截断：{}；其余前提不再展开。",
                gap_limit_text(limit)
            )
            .ok();
        }
    }
    if let Some(limit) = &tree.limit {
        writeln!(
            out,
            "{pad}已截断：{}；其余缺口不再展开。",
            gap_limit_text(limit)
        )
        .ok();
    }
}

/// The burden/standard annotation of the rule that needs a missing premise.
///
/// The gap candidate records only a rule name, so the annotation is read from
/// the rule's declaration through the reasoner. This is the one lookup `:gap`
/// and `:issues` use; both render the same gap tree, so their annotations
/// cannot disagree. An undeclared field reads `未声明举证责任` /
/// `未声明证明标准`, never a default role or standard. A declaration that
/// cannot be found is stated as such instead of being replaced by a default.
fn requirement_burden_note(reasoner: &Reasoner<'_>, rule: &str) -> String {
    match reasoner.pleading(rule) {
        Some(pleading) => format!("〔举证：{}〕", pleading.requirements.pair_zh()),
        None => "〔举证：未找到规则声明，无法报告〕".to_owned(),
    }
}

/// The exception burden/standard annotation of a blocked rule.
///
/// `exception_burden` / `exception_standard` describe every `unless` of a rule,
/// so one annotation covers each blocker line. The values come from the same
/// declaration read as [`requirement_burden_note`], with the exception group.
fn exception_burden_note(reasoner: &Reasoner<'_>, rule: &str) -> String {
    match reasoner.pleading(rule) {
        Some(pleading) => format!(" 〔例外举证：{}〕", pleading.exceptions.pair_zh()),
        None => " 〔例外举证：未找到规则声明，无法报告〕".to_owned(),
    }
}

/// One limit in words, shared by gap trees and the issue scan.
fn gap_limit_text(limit: &GapLimit) -> String {
    match limit {
        GapLimit::Depth { limit } => format!("达到最大展开深度（{limit} 层）"),
        GapLimit::Nodes { limit } => format!("达到最大节点数（{limit} 个）"),
        GapLimit::RuleAttempts { rule, limit } => {
            format!("规则 ⟨{rule}⟩ 的尝试次数已达上限（{limit} 次）")
        }
        GapLimit::Issues { limit } => format!("可争的结论已达到上限（{limit} 条）"),
        GapLimit::Excluded { limit } => format!("被排除的规则已达到上限（{limit} 条）"),
    }
}

/// `p := 张三，q := 李四` for one universal instance.
///
/// The bindings are printed in binder order; a non-ASCII name is escaped
/// nowhere here because it comes from a declaration, not from free text.
fn instance_bindings_text(bindings: &[(Name, Expr)]) -> String {
    bindings
        .iter()
        .map(|(parameter, value)| format!("{parameter} := {}", print_expr(value)))
        .collect::<Vec<_>>()
        .join("，")
}

/// `⟨a⟩、⟨b⟩` for a rule list, with the first eight names and a total count.
fn format_limited_names(names: &[Name]) -> String {
    let shown = names
        .iter()
        .take(8)
        .map(|name| format!("⟨{name}⟩"))
        .collect::<Vec<_>>()
        .join("、");
    if names.len() > 8 {
        format!("{shown} 等 {} 条", names.len())
    } else {
        shown
    }
}

/// Warn once when the environment's declared priorities contain a cycle.
///
/// An edge inside a strongly connected component can never decide a conflict,
/// so a result that says "no usable priority" must not look like "nothing was
/// declared". The warning never changes the exit code: the cycle is a property
/// of the environment, not of the query or of one certificate.
fn write_priority_cycle_warning(out: &mut impl Write, cycles: &[Vec<Name>]) {
    if cycles.is_empty() {
        return;
    }
    let rendered = cycles
        .iter()
        .map(|cycle| {
            cycle
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join("、")
        })
        .collect::<Vec<_>>()
        .join("；");
    writeln!(
        out,
        "注意：当前环境的优先级声明存在环：{rendered}；环内的优先关系不生效。"
    )
    .ok();
}

/// The defeated competitor of a conflict the queried proposition won, together
/// with the recorded provenance of that competitor and the basis the
/// certificate records for the win.
///
/// The proposition is matched with kernel definitional equality, not by
/// comparing printed strings.
fn won_conflict_note(
    env: &Env,
    goal: &Expr,
    certificate: &Certificate,
) -> Result<Option<(Expr, std_deduce_cert::Provenance, ResolutionBasis)>, String> {
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
        let (Some(side), std_deduce_cert::Resolution::Defeated { winner, basis }) =
            (side, &conflict.resolution)
        else {
            continue;
        };
        if side != *winner {
            continue;
        }
        let (other, other_by) = match winner {
            std_deduce_cert::Side::Left => (&conflict.right, &conflict.right_by),
            std_deduce_cert::Side::Right => (&conflict.left, &conflict.left_by),
        };
        return Ok(Some((Expr::from(other), other_by.clone(), basis.clone())));
    }
    Ok(None)
}

/// The burden/standard annotations of a rule, as `:inspect` displays them.
///
/// Only declared fields are shown: an omitted clause prints nothing, neither a
/// placeholder nor a default. The positive group and the exception group are
/// independent; a group never contains a dangling `·`.
fn rule_pleading_suffix(rule: &RuleDecl) -> String {
    let mut groups = Vec::new();
    let mut requirements = Vec::new();
    if let Some(burden) = rule.burden {
        requirements.push(format!("举证 {}", burden.label()));
    }
    if let Some(standard) = rule.standard {
        requirements.push(format!("标准 {}", standard.label()));
    }
    if !requirements.is_empty() {
        groups.push(format!("  〔{}〕", requirements.join(" · ")));
    }
    let mut exceptions = Vec::new();
    if let Some(burden) = rule.exception_burden {
        exceptions.push(format!("例外举证 {}", burden.label()));
    }
    if let Some(standard) = rule.exception_standard {
        exceptions.push(format!("例外标准 {}", standard.label()));
    }
    if !exceptions.is_empty() {
        groups.push(format!("  〔{}〕", exceptions.join(" · ")));
    }
    groups.concat()
}

/// How one side of a conflict is supported, for a `:why` line.
///
/// A fact side carries the identity it was registered under, so the reader can
/// tell a court's finding from a claim. The identity comes from the same
/// assumption table that decided the conflict; when it cannot be found the line
/// falls back to the pre-identity wording rather than guessing one.
fn describe(p: &Provenance, identity: Option<FactIdentity>) -> String {
    match p {
        Provenance::Assumption => match identity {
            Some(identity) => format!("事实〔{}〕", identity.label_zh()),
            None => "事实（身份未记录）".into(),
        },
        Provenance::Rules(rs) if rs.is_empty() => "已无可重建的规则实例".into(),
        Provenance::Rules(rs) => format!(
            "规则 {}",
            rs.iter()
                .map(|r| format!("⟨{r}⟩"))
                .collect::<Vec<_>>()
                .join("、")
        ),
        Provenance::Axiom(axiom) => format!("公理实例 ⟨{axiom}⟩"),
        Provenance::Interpretation(interpretation) => {
            format!("解释⟨{}⟩", escape_control(interpretation))
        }
    }
}

/// The success line for a fact the session just registered.
fn registered_fact_line(identity: FactIdentity, prop: &Expr) -> String {
    let mut line = format!("已登记{}：{}", identity.label_zh(), print_expr(prop));
    if !identity.seeds_derivation() {
        line.push_str("（争议事实，不参与推导）");
    }
    line
}

/// Whether a batch path names a JSON case description by its extension.
///
/// Both `std-deduce <文件.json> [命令...]` and `std-deduce check <文件.json>`
/// load it through `:load-case`, so the two entries behave identically. The
/// extension is matched case-insensitively.
fn is_case_json(path: &str) -> bool {
    Path::new(path)
        .extension()
        .and_then(|extension| extension.to_str())
        .is_some_and(|extension| extension.eq_ignore_ascii_case("json"))
}

/// Diagnostics for one JSON case load.
///
/// Bundles the file, the document's imports and the environment state the
/// closed-environment hint needs, so every case error is rendered and annotated
/// in one place.
struct CaseDiagnostics<'a> {
    environment: &'a environment::Environment,
    imports: &'a [String],
    file: &'a str,
}

impl CaseDiagnostics<'_> {
    /// Render `file:JSON 路径: error: message`, then add the environment hints
    /// a failed `:load` would add.
    fn error(&self, json_path: &str, message: impl std::fmt::Display) -> String {
        let rendered = case::render(self.file, json_path, message);
        let rendered = self.environment.annotate_error(rendered, self.imports);
        self.environment.annotate_closed_error(rendered)
    }

    /// Reject a JSON fact that relabels a proposition already registered under
    /// a different identity.
    ///
    /// The comparison is kernel conversion, so an alpha variant or a `def`
    /// alias cannot dodge it. `written` reports the JSON path of a fact the
    /// same load already inserted; `existing` reports a fact that was in the
    /// environment before the load. The identity is evidence, so two identities
    /// for one proposition are refused instead of silently keeping both.
    fn identity_conflict(
        &self,
        env: &Env,
        existing: &[(Name, Expr, FactIdentity)],
        written: &[(String, Expr, FactIdentity)],
        prop: &Expr,
        identity: FactIdentity,
        json_path: &str,
    ) -> Result<Option<String>, String> {
        for (other_path, other_type, other_identity) in written {
            if *other_identity == identity {
                continue;
            }
            let same = convertible(env, &Ctx::new(), other_type, prop).map_err(|error| {
                self.error(json_path, format!("无法比较命题与已登记事实：{error}"))
            })?;
            if same {
                return Ok(Some(self.error(
                    &format!("{json_path}.identity"),
                    format!(
                        "同一命题只能有一种事实身份：已由 {other_path} 登记为{}，不能再登记为{}",
                        other_identity.label_zh(),
                        identity.label_zh()
                    ),
                )));
            }
        }
        for (name, other_type, other_identity) in existing {
            if *other_identity == identity {
                continue;
            }
            let same = convertible(env, &Ctx::new(), other_type, prop).map_err(|error| {
                self.error(json_path, format!("无法比较命题与已登记事实：{error}"))
            })?;
            if same {
                return Ok(Some(self.error(
                    &format!("{json_path}.identity"),
                    format!(
                        "同一命题只能有一种事实身份：`{}` 已登记为{}，不能再登记为{}",
                        name,
                        other_identity.label_zh(),
                        identity.label_zh()
                    ),
                )));
            }
        }
        Ok(None)
    }
}

/// The next free `事实N` ledger name for a case load.
///
/// The name is derived from the first free slot, not from the declaration
/// count, so metadata declarations cannot renumber facts. The ledger is a flat
/// map: a collision with a name from a loaded pack is skipped, never
/// overwritten.
fn next_case_fact_name(env: &Env, next: &mut usize) -> String {
    loop {
        let candidate = format!("事实{next}");
        *next += 1;
        if !env.contains(&candidate) {
            return candidate;
        }
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
        "  std-deduce check <文件.std> [...]  等价于直接给文件（check 是批处理入口；.json 同样接受）"
    )
    .ok();
    writeln!(
        out,
        "  std-deduce <文件.json> [命令...]   加载严格 JSON 案件描述（等价于 :load-case）"
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
        "  --as-of <YYYY-MM-DD>         实例完全没有事件时间时的兜底日期（:asof 可改；:cert 记录它）"
    )
    .ok();
    writeln!(
        out,
        "  --jurisdiction <代码>        会话的管辖代码（:jurisdiction 可改；:cert 记录它，也是适用性判定的管辖）"
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
    writeln!(
        out,
        "  --closed-env                 封闭环境：案件文件只能使用已加载法律包里的声明与规则"
    )
    .ok();
    writeln!(
        out,
        "  --allow-case-rules           在封闭环境中允许案件本地规则（证书会标记为本地扩展）"
    )
    .ok();
    writeln!(
        out,
        "  --interpret <解释名>         为本次会话启用一个解释（可重复；默认全部不启用）"
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
        ":asof / :jurisdiction 与 --as-of / --jurisdiction 写同一组会话值；\
         :cert / :verify-cert 记录并比对这些值。适用性判定先按事件时间/地点，\
         只有实例没有任何事件时间时 :asof 才作为兜底。"
    )
    .ok();
    writeln!(
        out,
        "时空适用性：按实例前提事实的发生时间/地点判定（事件时优先；无事件时间才用 :asof 兜底）；\
         不适用与部分覆盖（无法判定）不触发；无证据的未判定仍触发但每条结论行都会标注。:applicability [命题] 有目标列实例判定与依据，无目标只列声明范围。"
    )
    .ok();
    writeln!(
        out,
        "环境里的规则涉及两个及以上 jurisdiction 且未选管辖时，:why / :explain / :cert 退出 2。"
    )
    .ok();
    writeln!(
        out,
        "形式推导：:why <命题>；中文「因为……所以……」说明：:explain <命题>；\
         信任标签与依据：:labels <命题>。"
    )
    .ok();
    writeln!(
        out,
        "信任标签是证书的派生视图，不写入证书：:why / :explain 在结果行旁打印一行，\
         :labels 打印该目标的全套标签与依据。已验证只表示证书内仅用严格事实且无未决义务，\
         不等于法律上正确。"
    )
    .ok();
    writeln!(
        out,
        "解释默认不启用：--interpret <解释名> 或 :interpret enable <解释名> 显式启用；\
         :interpret list 查看状态，:gap / :why 的缺口会提示未启用的解释。"
    )
    .ok();
    writeln!(
        out,
        "律师复核报告：:review <命题> [--out <文件>]；报告只由证书、缺口树、举证元数据与信任标签生成，\
         不是法律意见。不写 --out 时报告写到 stdout；写文件时只打印报告路径，文件内容与 stdout 形式逐字节相同。\
         写文件采用同目录临时文件加原子改名的原子写语义，失败不留半份报告。\
         退出码与 :why 一致：根已证明且无未决义务为 0，其余为 1。"
    )
    .ok();
    writeln!(
        out,
        "案件描述 JSON：:load-case <文件.json> 加载严格版本化的案件描述（只允许事实、身份、来源、\
         时间地点与目标，不能声明规则/谓词/解释/风险/优先级）；批处理入口 std-deduce <文件.json>。"
    )
    .ok();
    writeln!(out).ok();
    writeln!(out, "声明：这是模型内推导，不是法律意见。").ok();
    writeln!(
        out,
        "证书包含案件原文，可能含个人信息，分享前请自行处理；:cert 导出的证书是原样文本，不脱敏\
         （脱敏后的证书无法再被 :verify-cert 复核）。"
    )
    .ok();
    writeln!(
        out,
        "--redact 开启显示层脱敏（:redact on|off 可在会话里切换）：:why / :explain / :labels 等输出把\
         个体名换成甲1、甲2…（来源与标签文本同样替换），证书 JSON 仍是原文；关闭时输出不变。"
    )
    .ok();
    writeln!(
        out,
        "风险题材：理论里 `risk <类别> <谓词>` 声明谓词属于刑事 / 人身安全 / 重大财产 / 临近期限 / \
         涉外或移民之一；根推导涉及这些命题时 :why / :explain 打印一行高风险警示与依据，\
         :labels 把它作为次标签列出。"
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

/// Load one theory file or JSON case description and then run the remaining
/// commands.
///
/// A `.json` path goes through `load_case`; every other path through
/// `load_theory`. A failed load prints the already-rendered
/// `path:line:col: error: ...`, `path:<JSON 路径>: error: ...` (or
/// `path: error: ...`) on stderr and exits `2` for a JSON case description (the
/// same code `:load-case` uses) or `1` for a `.std` theory (the existing batch
/// contract). The load error already names the file, so the batch entry adds no
/// path prefix of its own. Remaining commands are not run.
fn run_batch(session: &mut Session, file: &str, commands: &[String], out: &mut impl Write) -> i32 {
    // The load report names the declarations the file contributed, including
    // the case's individuals and facts, so display redaction must cover it too.
    // Buffering it keeps the report and its notice in one filtered write.
    let mut buffer = OutputBuffer::default();
    let is_case = is_case_json(file);
    let load_name = if is_case { "load-case" } else { "load" };
    let load_result = if is_case {
        session.load_case(file, &mut buffer)
    } else {
        session.load_theory(file, &mut buffer)
    };
    let text = match buffer.into_text(load_name) {
        Ok(text) => text,
        Err(error) => {
            eprintln!("{error}");
            return 2;
        }
    };
    if session.redact {
        let mut text = session.redact_text(&text);
        if !text.is_empty() {
            text.push_str(REDACT_NOTICE);
            text.push('\n');
        }
        write!(out, "{text}").ok();
    } else {
        write!(out, "{text}").ok();
    }
    if let Err(error) = load_result {
        let error = if session.redact {
            session.redact_text(&error)
        } else {
            error
        };
        eprintln!("{error}");
        // A rejected JSON case description is an untrusted-input rejection: the
        // batch entry reports it as a command-style error (2), the same code the
        // `:load-case` command uses. The existing `.std` batch load contract
        // stays 1 and is not changed here.
        return if is_case { 2 } else { 1 };
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
                ":load <文件>  :load-case <文件.json>  :inspect  :given <命题>  :fact [list|show|add|assumed|disputed <命题>]  \
                 :asof [YYYY-MM-DD]  :jurisdiction [代码]  \
                 :interpret [list|enable|disable <解释名>]  \
                 :why <命题>  :explain <命题>  :labels <命题>  :review <命题> [--out <文件>]  :gap <命题>  :issues  :applicability [命题]  :cert <命题>  :verify-cert <证书文件> [目标命题]  \
                 :why <命题>  :explain <命题>  :labels <命题>  :gap <命题>  :issues  :applicability [命题]  :cert <命题>  :verify-cert <证书文件> [目标命题]  \
                 :redact [on|off]  \
                 :packs [目录]  :lock [目录]  :audit [目录]（只核对带 quote 的来源）  :quit"
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
