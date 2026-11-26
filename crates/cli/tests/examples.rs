//! End-to-end regression tests for the theory files in `examples/`.
//!
//! Every example is loaded through the real CLI binary. The assertions pin the
//! documented exit codes (0 for a proof, 1 for a gap or an unresolved conflict)
//! and a few stable substrings, not whole-output snapshots.

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicU64, Ordering};

const PROVED: i32 = 0;
const GAP_OR_CONFLICT: i32 = 1;
const LOAD_ERROR: i32 = 2;

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn examples_dir() -> PathBuf {
    repo_root().join("examples")
}

fn example(name: &str) -> String {
    let path = examples_dir().join(name);
    assert!(path.is_file(), "missing example file: {}", path.display());
    path.to_string_lossy().into_owned()
}

/// Run the CLI from the repository root. `lawpacks/` is resolved relative to
/// the working directory, so an `import` of an official pack only finds it there.
fn run(commands: Vec<String>) -> Output {
    Command::new(env!("CARGO_BIN_EXE_std-deduce"))
        .current_dir(repo_root())
        .args(commands)
        .output()
        .unwrap_or_else(|e| panic!("failed to run the CLI: {e}"))
}

fn load(name: &str) -> Output {
    run(vec![format!(":load {}", example(name))])
}

fn session(name: &str, commands: &[&str]) -> Output {
    let mut all = vec![format!(":load {}", example(name))];
    all.extend(commands.iter().map(|command| command.to_string()));
    run(all)
}

/// A theory file outside the repository, removed when the test ends.
struct TempTheory {
    path: PathBuf,
}

impl TempTheory {
    fn new(tag: &str, source: &str) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "std-deduce-cli-{}-{tag}-{n}.std",
            std::process::id()
        ));
        fs::write(&path, source).unwrap_or_else(|e| panic!("write {}: {e}", path.display()));
        TempTheory { path }
    }
}

impl Drop for TempTheory {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.path);
    }
}

fn session_with_theory(theory: &TempTheory, commands: &[&str]) -> Output {
    let mut all = vec![format!(":load {}", theory.path.display())];
    all.extend(commands.iter().map(|command| command.to_string()));
    run(all)
}

fn exit_code(output: &Output) -> Option<i32> {
    output.status.code()
}

fn stdout(output: &Output) -> String {
    String::from_utf8_lossy(&output.stdout).into_owned()
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

/// Assert the exit code and that stdout contains every needle.
fn check(output: Output, expected: i32, needles: &[&str]) -> Output {
    let code = exit_code(&output);
    let out = stdout(&output);
    let err = stderr(&output);
    assert_eq!(
        code,
        Some(expected),
        "expected exit {expected}, got {code:?}\nstdout:\n{out}\nstderr:\n{err}"
    );
    for needle in needles {
        assert!(
            out.contains(needle),
            "stdout does not contain {needle:?}\nstdout:\n{out}\nstderr:\n{err}"
        );
    }
    output
}

/// Assert the exit code and that stderr contains every needle.
fn check_stderr(output: Output, expected: i32, needles: &[&str]) -> Output {
    let code = exit_code(&output);
    let out = stdout(&output);
    let err = stderr(&output);
    assert_eq!(
        code,
        Some(expected),
        "expected exit {expected}, got {code:?}\nstdout:\n{out}\nstderr:\n{err}"
    );
    for needle in needles {
        assert!(
            err.contains(needle),
            "stderr does not contain {needle:?}\nstdout:\n{out}\nstderr:\n{err}"
        );
    }
    output
}

#[test]
fn constitution_39_loads_and_proves() {
    check(
        load("constitution-39.std"),
        PROVED,
        &["已加载", "非法搜查即侵犯"],
    );
    check(
        session("constitution-39.std", &[":why 不受侵犯 张三 甲宅"]),
        PROVED,
        &["▸ 不受侵犯 张三 甲宅", "推导已通过独立校验"],
    );
}

/// The import example is facts-only: sorts, predicates and the rule come from
/// `import cn.constitution`, and the fixed `lawpacks/` registry supplies them.
#[test]
fn constitution_39_import_example_proves_through_the_official_pack() {
    check(
        session(
            "宪法第三十九条-导入包.std",
            &[":why cn.constitution.住宅受侵犯 张三 甲宅"],
        ),
        PROVED,
        &[
            "已加载",
            "导入 cn.constitution",
            "▸ cn.constitution.住宅受侵犯 张三 甲宅",
            "推导已通过独立校验",
        ],
    );
}

#[test]
fn complementary_predicates_report_an_unresolved_conflict() {
    check(
        load("冲突-互补谓词.std"),
        PROVED,
        &["已加载", "contrary 批准 不批准"],
    );
    check(
        session("冲突-互补谓词.std", &[":why 批准 甲"]),
        GAP_OR_CONFLICT,
        &["冲突未决：批准 甲", "该结论没有进入事实库"],
    );
    // The downstream rule depends on the losing side of the conflict, so its
    // premise never enters the fact base.
    check(
        session("冲突-互补谓词.std", &[":why 可复议 甲"]),
        GAP_OR_CONFLICT,
        &[
            "? 可复议 甲",
            "缺：不批准 甲",
            "证书有效，但根为缺口，结论未被证明。",
        ],
    );
}

/// The main file only proves the constitutional right: nationality to
/// citizenship to the right to education, all from `cn.constitution`.
#[test]
fn qiyuling_proves_the_constitutional_right_to_education() {
    check(
        load("宪法案例-齐玉苓.std"),
        PROVED,
        &["已加载", "导入 cn.constitution"],
    );
    check(
        session(
            "宪法案例-齐玉苓.std",
            &[":why cn.constitution.受教育权 齐玉苓"],
        ),
        PROVED,
        &[
            "▸ cn.constitution.受教育权 齐玉苓",
            "▸ cn.constitution.公民 齐玉苓",
            "推导已通过独立校验",
        ],
    );
    // The reply's conclusion is not part of this theory: the predicate is
    // unknown, and the CLI must say so rather than report a gap.
    check_stderr(
        session("宪法案例-齐玉苓.std", &[":why 应承担民事责任 顶替 齐玉苓"]),
        LOAD_ERROR,
        &["未知名称"],
    );
}

/// The reply is a separate theory: both files declare 齐玉苓 and her
/// nationality, so they must never be loaded into the same session.
#[test]
fn qiyuling_reply_uses_out_of_pack_documents_and_the_revocation_blocks_it() {
    check(
        load("宪法案例-齐玉苓-批复.std"),
        PROVED,
        &["已加载", "导入 cn.constitution"],
    );
    check(
        session(
            "宪法案例-齐玉苓-批复.std",
            &[":why 应承担民事责任 顶替 齐玉苓"],
        ),
        PROVED,
        &["▸ 应承担民事责任 顶替 齐玉苓", "推导已通过独立校验"],
    );
    check(
        session(
            "宪法案例-齐玉苓-批复.std",
            &[":given 批复已废止", ":gap 应承担民事责任 顶替 齐玉苓"],
        ),
        GAP_OR_CONFLICT,
        &[
            "无法推出 应承担民事责任 顶替 齐玉苓",
            "被阻断：「批复已废止」〔用户陈述〕已成立",
        ],
    );
}

/// The pack derives citizenship from nationality, so the detention fact is the
/// only premise its owning rule misses; a session `:given` fills it and proves
/// the pack rule.
#[test]
fn sun_zhigang_pack_gap_is_filled_by_a_given_detention_fact() {
    check(
        load("宪法案例-孙志刚.std"),
        PROVED,
        &["已加载", "导入 cn.constitution", "收容遣送第九条第六款"],
    );
    let output = check(
        session(
            "宪法案例-孙志刚.std",
            &[":gap cn.constitution.人身自由受侵犯 孙志刚"],
        ),
        GAP_OR_CONFLICT,
        &[
            "无法推出 cn.constitution.人身自由受侵犯 孙志刚",
            "缺 ⟨cn.constitution.非法拘禁 孙志刚⟩",
        ],
    );
    let out = stdout(&output);
    assert!(
        !out.contains("缺 ⟨cn.constitution.公民 孙志刚⟩"),
        "the pack derives citizenship from nationality; it is not a missing premise:\n{out}"
    );
    check(
        session(
            "宪法案例-孙志刚.std",
            &[
                ":given cn.constitution.非法拘禁 孙志刚",
                ":why cn.constitution.人身自由受侵犯 孙志刚",
            ],
        ),
        PROVED,
        &[
            "▸ cn.constitution.人身自由受侵犯 孙志刚",
            "⟨cn.constitution.非法拘禁侵犯人身自由⟩",
            "推导已通过独立校验",
        ],
    );
}

#[test]
fn sun_zhigang_detention_stays_a_gap_while_the_independent_rule_proves() {
    check(
        session("宪法案例-孙志刚.std", &[":gap 应当收容 孙志刚"]),
        GAP_OR_CONFLICT,
        &[
            "无法推出 应当收容 孙志刚",
            "缺 ⟨无合法证件 孙志刚⟩",
            "缺 ⟨无正常居所 孙志刚⟩",
            "缺 ⟨无正当生活来源 孙志刚⟩",
        ],
    );
    check(
        session("宪法案例-孙志刚.std", &[":why 不得收容 孙志刚"]),
        PROVED,
        &[
            "▸ 不得收容 孙志刚",
            "· 缺暂住证 孙志刚  〔用户陈述〕",
            "⟨省人大法工委解释⟩",
            "推导已通过独立校验",
        ],
    );
}

#[test]
fn henan_seed_conflict_is_reported_as_unresolved() {
    check(
        load("法律位阶-河南种子案-冲突.std"),
        PROVED,
        &["已加载", "unique 应适用 1"],
    );
    check(
        session(
            "法律位阶-河南种子案-冲突.std",
            &[":why 应适用 种子法 汝阳种子公司案"],
        ),
        GAP_OR_CONFLICT,
        &[
            "冲突未决：应适用 种子法 汝阳种子公司案",
            "该结论没有进入事实库",
        ],
    );
}

#[test]
fn henan_seed_hierarchy_resolves_the_conflict() {
    check(
        load("法律位阶-河南种子案-裁决.std"),
        PROVED,
        &["已加载", "位阶决定应适用"],
    );
    check(
        session(
            "法律位阶-河南种子案-裁决.std",
            &[":why 应适用 种子法 汝阳种子公司案"],
        ),
        PROVED,
        &[
            "▸ 应适用 种子法 汝阳种子公司案",
            "冲突（已裁决）",
            "推导已通过独立校验",
        ],
    );
    check(
        session(
            "法律位阶-河南种子案-裁决.std",
            &[":gap 应适用 河南省农作物种子管理条例 汝阳种子公司案"],
        ),
        GAP_OR_CONFLICT,
        &["冲突已裁决：", "被否决"],
    );
}

#[test]
fn criminal_law_20_basic_proves_no_liability() {
    check(
        load("刑法第二十条-基本.std"),
        PROVED,
        &["已加载", "正当防卫不负刑责"],
    );
    check(
        session("刑法第二十条-基本.std", &[":why 不负刑事责任 乙行为"]),
        PROVED,
        &["▸ 不负刑事责任 乙行为", "推导已通过独立校验"],
    );
    check(
        session("刑法第二十条-基本.std", &[":gap 应当负刑事责任 乙行为"]),
        GAP_OR_CONFLICT,
        &["无法推出 应当负刑事责任 乙行为", "缺 ⟨防卫过当 乙行为⟩"],
    );
}

#[test]
fn criminal_law_20_excessive_defense_blocks_no_liability() {
    check(
        load("刑法第二十条-防卫过当.std"),
        PROVED,
        &["已加载", "超过限度"],
    );
    check(
        session("刑法第二十条-防卫过当.std", &[":why 应当负刑事责任 乙行为"]),
        PROVED,
        &["▸ 应当负刑事责任 乙行为", "推导已通过独立校验"],
    );
    check(
        session("刑法第二十条-防卫过当.std", &[":gap 不负刑事责任 乙行为"]),
        GAP_OR_CONFLICT,
        &[
            "无法推出 不负刑事责任 乙行为",
            "被阻断：「防卫过当 乙行为」已成立",
        ],
    );
}

#[test]
fn software_copyright_proves_infringement_and_full_damages() {
    check(
        load("最高法-软件著作权-最高法知民终155号.std"),
        PROVED,
        &["已加载", "妨害保全的不利推定"],
    );
    check(
        session(
            "最高法-软件著作权-最高法知民终155号.std",
            &[":why 侵害复制权 被诉侵权软件 沃某模具公司"],
        ),
        PROVED,
        &[
            "▸ 侵害复制权 被诉侵权软件 沃某模具公司",
            "▸ 复制 被诉侵权软件 沃某模具公司",
            "· 特有信息一致 被诉侵权软件 案涉软件  〔法院查明〕",
            "推导已通过独立校验",
        ],
    );
    check(
        session(
            "最高法-软件著作权-最高法知民终155号.std",
            &[":why 全额支持损失 沃某模具公司 案涉软件"],
        ),
        PROVED,
        &[
            "▸ 全额支持损失 沃某模具公司 案涉软件",
            "▸ 推定亦安装 沃某模具公司 案涉软件",
            "推导已通过独立校验",
        ],
    );
    check(
        session(
            "最高法-软件著作权-最高法知民终155号.std",
            &[":gap 举证证明无实质性相似 沃某模具公司"],
        ),
        GAP_OR_CONFLICT,
        &[
            "无法推出 举证证明无实质性相似 沃某模具公司",
            "没有任何规则以它为结论",
        ],
    );
}

#[test]
fn negation_theorems_and_axioms_load_and_inspect() {
    check(
        load("否定-定理与公理.std"),
        PROVED,
        &["已加载", "双重否定引入", "经典双重否定消去"],
    );
    check(
        session("否定-定理与公理.std", &[":inspect"]),
        PROVED,
        &[
            "假 : Prop",
            "非 : Prop → Prop",
            "fact  经典双重否定消去",
            "〔分析假设〕",
        ],
    );
    // The classical elimination axiom is assumed as a fact, so the reasoner
    // can use it directly.
    check(
        session("否定-定理与公理.std", &[":why ∀ (p : Prop), 非 (非 p) → p"]),
        PROVED,
        &[
            "· ∀ (p : Prop)",
            "[经典双重否定消去]",
            "〔分析假设〕",
            "推导已通过独立校验",
        ],
    );
    // `axiom 假 : Prop` only declares a constant; it asserts nothing, so the
    // proposition cannot be derived.
    check(
        session("否定-定理与公理.std", &[":gap 假"]),
        GAP_OR_CONFLICT,
        &["无法推出 假", "没有任何规则以它为结论"],
    );
}

#[test]
fn negation_experiment_one_checks_double_negation_introduction() {
    check(
        load("否定-实验一-定理.std"),
        PROVED,
        &[
            "已加载",
            "✓ 引入 (下雨 今天) 今天确实下雨 : 非 (非 (下雨 今天))",
        ],
    );
    check(
        session("否定-实验一-定理.std", &[":why 下雨 今天"]),
        PROVED,
        &["· 下雨 今天", "推导已通过独立校验"],
    );
    check(
        session("否定-实验一-定理.std", &[":gap 非 (下雨 今天)"]),
        GAP_OR_CONFLICT,
        &["无法推出 非 (下雨 今天)", "没有任何规则以它为结论"],
    );
}

#[test]
fn negation_experiment_two_fake_proof_is_rejected_at_load() {
    // This example exists to show the kernel rejecting a bad proof term, so a
    // failed load is its expected behaviour.
    check_stderr(
        load("否定-实验二-伪证明.std"),
        LOAD_ERROR,
        &["错误：", "伪消去", "类型不匹配"],
    );
}

/// A proved root is not a successful query if the same certificate still
/// carries an unrelated unresolved conflict: `:verify-cert` would exit `1`, and
/// `:why` must not report a cleaner result than the certificate checker.
#[test]
fn a_proved_root_with_an_unrelated_unresolved_conflict_is_not_a_success() {
    let output = check(
        session("冲突-互补谓词.std", &[":why 符合条件 甲"]),
        GAP_OR_CONFLICT,
        &[
            "· 符合条件 甲",
            "证书有效且根已证明，但仍有未决义务",
            "不能报告为无保留的证明",
        ],
    );
    let out = stdout(&output);
    assert!(
        !out.contains("推导已通过独立校验。"),
        "a certificate with open obligations must not print the success line:\n{out}"
    );
}

/// The conservative blocker check may reject a derivation the reasoner built.
/// That is a false red, not a licence to print a success: `:why` must fail
/// closed and exit `2`.
#[test]
fn why_fails_closed_when_a_blocker_cannot_be_cleared() {
    let theory = TempTheory::new(
        "why-conservative-blocker",
        r#"
sort 公民
obj 张三 : 公民
obj 李四 : 公民
pred 侵占 : 公民 → Prop
pred 违法 : 公民 → Prop
pred 无辜 : 公民 → Prop
pred 佐证 : 侵占 李四 → Prop
axiom 侵占事实 : 侵占 张三
  source text "测试" locator "夹具"
rule 依赖推定 :
  premise h : 侵占 李四
  unless 佐证 h
  conclude 无辜 张三
  source text "测试" locator "夹具"
rule r :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 无辜 p
  source text "测试" locator "夹具"
"#,
    );
    let output = session_with_theory(&theory, &[":why 违法 张三"]);
    let output = check(output, LOAD_ERROR, &["▸ 违法 张三", "逻辑校验失败"]);
    let out = stdout(&output);
    let err = stderr(&output);
    assert!(
        !out.contains("推导已通过独立校验。"),
        "a failed certificate must not print the success line:\nstdout:\n{out}\nstderr:\n{err}"
    );
    assert!(
        err.contains("证书校验失败（逻辑层"),
        "the failure must name the failed layer:\nstderr:\n{err}"
    );
}

/// `:inspect` keeps the one-line citation and adds the structured fields.
/// Control characters in a quotation are rendered as escapes, so a quotation
/// that spans lines cannot forge extra output lines.
#[test]
fn inspect_prints_the_structured_source_fields_on_one_line_each() {
    let theory = TempTheory::new(
        "inspect-structured-source",
        r#"
sort 公民
pred 违法 : 公民 → Prop
obj 张三 : 公民
axiom 事实 : 违法 张三
  source text "宪法" locator "第三十九条" version "2018" effective "1982-12-04"
         quote "第一行\n第二行" url "https://www.npc.gov.cn/law?article=39&lang=zh"
         jurisdiction "CN" retrieved_at "2026-11-21" hash "sha256:abc" note "备注"
"#,
    );
    let output = check(
        session_with_theory(&theory, &[":inspect"]),
        PROVED,
        &[
            "← 「宪法第三十九条」（2018）",
            "引文：第一行\\n第二行",
            "链接：https://www.npc.gov.cn/law?article=39&lang=zh",
            "管辖：CN",
            "抓取时间：2026-11-21",
            "哈希：sha256:abc",
            "备注：备注",
        ],
    );
    let out = stdout(&output);
    assert!(
        !out.contains("第一行\n第二行"),
        "an escaped newline in a quote must not split the output line:\n{out}"
    );
}

/// A fact entered by hand is a user/session assertion. Its recorded source
/// must say so, and `:inspect` must never print an empty citation.
#[test]
fn given_facts_carry_a_user_session_source() {
    let theory = TempTheory::new(
        "given-source",
        r#"
sort 公民
pred 违法 : 公民 → Prop
obj 张三 : 公民
"#,
    );
    let output = check(
        session_with_theory(&theory, &[":given 违法 张三", ":inspect"]),
        PROVED,
        &["已登记用户陈述：违法 张三", "← 「用户输入交互会话」"],
    );
    let out = stdout(&output);
    assert!(
        !out.contains("「」"),
        "a given fact must not print an empty source:\n{out}"
    );
}

/// The same provenance rule applies when commands arrive on stdin instead of
/// argv: an interactive `:given` is still a user/session assertion.
#[test]
fn given_through_stdin_uses_the_interactive_session_source() {
    use std::io::Write;
    use std::process::{Command, Stdio};

    let theory = TempTheory::new(
        "given-stdin",
        r#"
sort 公民
pred 违法 : 公民 → Prop
obj 张三 : 公民
"#,
    );
    let mut child = Command::new(env!("CARGO_BIN_EXE_std-deduce"))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("start the CLI");
    {
        let stdin = child.stdin.as_mut().expect("piped stdin");
        writeln!(stdin, ":load {}", theory.path.display()).unwrap();
        writeln!(stdin, ":given 违法 张三").unwrap();
        writeln!(stdin, ":inspect").unwrap();
        writeln!(stdin, ":quit").unwrap();
    }
    let output = child.wait_with_output().expect("the CLI exits");
    check(output, PROVED, &["← 「用户输入交互会话」"]);
}

/// `:fact` registers a fact with an explicit identity and lists it with that
/// identity. `disputed` is recorded but announced as not participating.
#[test]
fn fact_command_registers_and_lists_facts_with_identities() {
    let theory = TempTheory::new(
        "fact-register",
        r#"
sort 公民
pred 违法 : 公民 → Prop
obj 张三 : 公民
obj 李四 : 公民
obj 王五 : 公民
"#,
    );
    let output = check(
        session_with_theory(
            &theory,
            &[
                ":fact add 违法 张三",
                ":fact assumed 违法 李四",
                ":fact disputed 违法 王五",
                ":fact list",
            ],
        ),
        PROVED,
        &[
            "已登记用户陈述：违法 张三",
            "已登记分析假设：违法 李四",
            "已登记对方争议：违法 王五（争议事实，不参与推导）",
            "用户陈述  违法 张三  [事实1]  ← 「用户输入交互会话」",
            "分析假设  违法 李四  [事实2]  ← 「用户输入交互会话」",
            "对方争议  违法 王五  [事实3]  ← 「用户输入交互会话」（争议事实，不参与推导）",
        ],
    );
    assert!(
        !stdout(&output).contains("已登记假设"),
        ":fact must use the identity labels"
    );
}

/// A disputed fact is recorded, but it does not enter the fact base: the
/// proposition stays a gap. A user-asserted fact with the same shape does.
#[test]
fn a_disputed_fact_does_not_seed_a_derivation() {
    let theory = TempTheory::new(
        "fact-disputed",
        r#"
sort 公民
pred 违法 : 公民 → Prop
obj 张三 : 公民
"#,
    );
    check(
        session_with_theory(&theory, &[":fact disputed 违法 张三", ":why 违法 张三"]),
        GAP_OR_CONFLICT,
        &["? 违法 张三", "结论未被证明"],
    );
    check(
        session_with_theory(&theory, &[":fact add 违法 张三", ":why 违法 张三"]),
        PROVED,
        &["· 违法 张三", "推导已通过独立校验"],
    );
}

/// `:fact show` finds a fact up to kernel equivalence and prints its identity,
/// name and provenance; an unregistered proposition is a clear error.
#[test]
fn fact_show_reports_identity_name_and_sources() {
    let theory = TempTheory::new(
        "fact-show",
        r#"
sort 公民
pred 违法 : 公民 → Prop
obj 张三 : 公民
obj 李四 : 公民
"#,
    );
    check(
        session_with_theory(&theory, &[":fact add 违法 张三", ":fact show 违法 张三"]),
        PROVED,
        &["身份：用户陈述", "名称：事实1", "← 「用户输入交互会话」"],
    );
    check_stderr(
        session_with_theory(&theory, &[":fact show 违法 李四"]),
        2,
        &["没有登记为事实的命题"],
    );
}

/// The session cannot claim what a court found or what both sides agreed:
/// those identities come from a case file, with its source.
#[test]
fn fact_verified_and_stipulated_are_refused_in_a_session() {
    let theory = TempTheory::new(
        "fact-refused",
        r#"
sort 公民
pred 违法 : 公民 → Prop
obj 张三 : 公民
"#,
    );
    for (subcommand, needle) in [("verified", "verified"), ("stipulated", "stipulated")] {
        let command = format!(":fact {subcommand} 违法 张三");
        let output = check_stderr(
            session_with_theory(&theory, &[command.as_str()]),
            2,
            &[
                "只能写在案件文件的事实声明里",
                "交互会话不能声明法院查明或双方无争议",
            ],
        );
        assert!(
            stderr(&output).contains(needle),
            "the refusal must name {needle}:\n{}",
            stderr(&output)
        );
    }
}

/// A fact declared in a file shows its Chinese identity label in `:inspect`;
/// an explicit `verified` is honoured and a case file defaults to the user's
/// assertion.
#[test]
fn inspect_shows_the_fact_identity_label() {
    let theory = TempTheory::new(
        "inspect-identity",
        r#"
sort 公民
pred 违法 : 公民 → Prop
pred 违规 : 公民 → Prop
obj 张三 : 公民
axiom 判决事实 : 违法 张三
  identity verified
  source text "判决" locator "第一页"
axiom 陈述事实 : 违规 张三
  source text "笔录" locator "第一页"
"#,
    );
    check(
        session_with_theory(&theory, &[":inspect", ":why 违法 张三"]),
        PROVED,
        &[
            "fact  判决事实 : 违法 张三  〔法院查明〕",
            "fact  陈述事实 : 违规 张三  〔用户陈述〕",
            "推导已通过独立校验",
        ],
    );
}

/// Every example file that has a regression test in this crate
/// (`宪法第三十九条-默认环境.std` is exercised by `environment.rs`,
/// `复核-*.std` by `review.rs`, `赔偿合计.std` and `金额算错-合计冲突.std` by
/// `arithmetic.rs`). The guard below keeps this table in step with the contents
/// of `examples/`.
const COVERED_EXAMPLES: &[&str] = &[
    "constitution-39.std",
    "宪法第三十九条-导入包.std",
    "宪法第三十九条-默认环境.std",
    "冲突-互补谓词.std",
    "宪法案例-齐玉苓.std",
    "宪法案例-齐玉苓-批复.std",
    "宪法案例-孙志刚.std",
    "法律位阶-河南种子案-冲突.std",
    "法律位阶-河南种子案-裁决.std",
    "刑法第二十条-基本.std",
    "刑法第二十条-防卫过当.std",
    "最高法-软件著作权-最高法知民终155号.std",
    "否定-定理与公理.std",
    "否定-实验一-定理.std",
    "否定-实验二-伪证明.std",
    "复核-闭合证明.std",
    "复核-用户陈述与缺口.std",
    "复核-开放概念与生效区间.std",
    "复核-三层缺口.std",
    "赔偿合计.std",
    "金额算错-合计冲突.std",
];

#[test]
fn all_example_files_are_covered() {
    let dir = examples_dir();
    let mut on_disk = BTreeSet::new();
    for entry in
        std::fs::read_dir(&dir).unwrap_or_else(|e| panic!("failed to read {}: {e}", dir.display()))
    {
        let entry = entry.expect("failed to read an examples/ entry");
        let path = entry.path();
        if path.is_file() && path.extension() == Some(std::ffi::OsStr::new("std")) {
            on_disk.insert(entry.file_name().to_string_lossy().into_owned());
        }
    }
    let covered: BTreeSet<String> = COVERED_EXAMPLES
        .iter()
        .map(|name| name.to_string())
        .collect();
    let uncovered: Vec<String> = on_disk.difference(&covered).cloned().collect();
    let missing: Vec<String> = covered.difference(&on_disk).cloned().collect();
    let list = |names: &[String]| {
        if names.is_empty() {
            "（无）".to_string()
        } else {
            names.join(", ")
        }
    };
    assert!(
        uncovered.is_empty() && missing.is_empty(),
        "example coverage table is out of date\n未覆盖的文件: {}\n覆盖表中已不存在的文件: {}",
        list(&uncovered),
        list(&missing),
    );
}
