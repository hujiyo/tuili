//! Direct certificate-checker tests.
//!
//! Every certificate here is constructed by hand from the certificate model.
//! The reasoner is not used, and no derivation is converted into a
//! certificate: the checker is tested on its own contract.

use std_deduce_cert::{
    check, Assumption, Binding, CertExpr, Certificate, CheckError, CheckReport, Conflict,
    EnvironmentIdentity, FormatVersion, Node, ObligationKind, OpenObligation, Provenance,
    Resolution, Side,
};
use std_deduce_kernel::Env;
use std_deduce_lang::Library;

const THEORY: &str = r#"
sort 公民
pred 侵占 : 公民 → Prop
pred 违法 : 公民 → Prop
pred 无辜 : 公民 → Prop
obj 张三 : 公民
obj 李四 : 公民

rule r :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 无辜 p
  source text "测试" locator "一"
"#;

/// The same rule as `THEORY`, plus an environment axiom that proves its
/// `unless` condition. A certificate may omit the axiom's node; the checker
/// must not.
const AXIOM_THEORY: &str = r#"
sort 公民
pred 侵占 : 公民 → Prop
pred 违法 : 公民 → Prop
pred 无辜 : 公民 → Prop
obj 张三 : 公民

axiom 无辜事实 : 无辜 张三
  source text "测试" locator "夹具"

rule r :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 无辜 p
  source text "测试" locator "一"
"#;

/// Rules whose premise binder (`premise h : ...`) is referenced by a later
/// premise or by an `unless`.
const DEPENDENT_THEORY: &str = r#"
sort 公民
pred 侵占 : 公民 → Prop
pred 违法 : 公民 → Prop
obj 张三 : 公民
pred 佐证 : 侵占 张三 → Prop

rule 依赖阻断 :
  premise h : 侵占 张三
  unless 佐证 h
  conclude 违法 张三
  source text "测试" locator "夹具"

rule 依赖前提 :
  premise h : 侵占 张三
  premise e : 佐证 h
  conclude 违法 张三
  source text "测试" locator "夹具"
"#;

/// An environment rule derives the blocker `无辜 张三` from an axiom. A
/// certificate may prove the premise of `r` and omit the blocker's own
/// derivation node; the checker must still see that the blocker is derivable.
const DERIVED_BLOCKER_THEORY: &str = r#"
sort 公民
pred 侵占 : 公民 → Prop
pred 违法 : 公民 → Prop
pred 无辜 : 公民 → Prop
pred 有罪 : 公民 → Prop
obj 张三 : 公民
axiom 有罪事实 : 有罪 张三
  source text "测试" locator "夹具"
axiom 侵占事实 : 侵占 张三
  source text "测试" locator "夹具"

rule 推定无辜 :
  params p : 公民
  premise 有罪 p
  conclude 无辜 p
  source text "测试" locator "二"

rule r :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 无辜 p
  source text "测试" locator "一"
"#;

/// The blocker is only reachable through a chain of environment rules, so a
/// one-step closure would miss it.
const TRANSITIVE_BLOCKER_THEORY: &str = r#"
sort 公民
pred 侵占 : 公民 → Prop
pred 违法 : 公民 → Prop
pred 无辜 : 公民 → Prop
pred 有罪 : 公民 → Prop
pred 可罚 : 公民 → Prop
obj 张三 : 公民
axiom 有罪事实 : 有罪 张三
  source text "测试" locator "夹具"

rule 有罪则可罚 :
  params p : 公民
  premise 有罪 p
  conclude 可罚 p
  source text "测试" locator "夹具"

rule 可罚则无辜 :
  params p : 公民
  premise 可罚 p
  conclude 无辜 p
  source text "测试" locator "夹具"

rule r :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 无辜 p
  source text "测试" locator "夹具"
"#;

/// The environment can derive `无辜 李四`, but the certificate is about
/// `张三`. A blocker about another individual must not block this step.
const UNRELATED_BLOCKER_THEORY: &str = r#"
sort 公民
pred 侵占 : 公民 → Prop
pred 违法 : 公民 → Prop
pred 无辜 : 公民 → Prop
pred 有罪 : 公民 → Prop
obj 张三 : 公民
obj 李四 : 公民
axiom 李四有罪 : 有罪 李四
  source text "测试" locator "夹具"

rule 推定无辜 :
  params p : 公民
  premise 有罪 p
  conclude 无辜 p
  source text "测试" locator "夹具"

rule r :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 无辜 p
  source text "测试" locator "夹具"
"#;

/// A rule concludes `无辜`, but its premise matches no fact: it derives
/// nothing and must not make the blocker look reachable.
const UNMATCHED_BLOCKER_THEORY: &str = r#"
sort 公民
pred 侵占 : 公民 → Prop
pred 违法 : 公民 → Prop
pred 无辜 : 公民 → Prop
pred 有罪 : 公民 → Prop
obj 张三 : 公民

rule 推定无辜 :
  params p : 公民
  premise 有罪 p
  conclude 无辜 p
  source text "测试" locator "夹具"

rule r :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 无辜 p
  source text "测试" locator "夹具"
"#;

/// A rule whose `unless` references a premise binder cannot be evaluated
/// statically, so its conclusion (`无辜 张三`) is an opaque pattern. An
/// unproved blocker that matches the pattern cannot be cleared.
const OPAQUE_BLOCKER_THEORY: &str = r#"
sort 公民
pred 侵占 : 公民 → Prop
pred 违法 : 公民 → Prop
pred 无辜 : 公民 → Prop
obj 张三 : 公民
pred 佐证 : 侵占 张三 → Prop

rule 依赖推定 :
  premise h : 侵占 张三
  unless 佐证 h
  conclude 无辜 张三
  source text "测试" locator "夹具"

rule r :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 无辜 p
  source text "测试" locator "夹具"
"#;

/// An opaque rule concludes `中间 张三`; the rule `中间 p → 无辜 p` propagates
/// that pattern into the blocker `r` is checking.
const OPAQUE_CHAIN_THEORY: &str = r#"
sort 公民
pred 侵占 : 公民 → Prop
pred 违法 : 公民 → Prop
pred 无辜 : 公民 → Prop
pred 中间 : 公民 → Prop
obj 张三 : 公民
pred 佐证 : 侵占 张三 → Prop

rule 依赖中间 :
  premise h : 侵占 张三
  unless 佐证 h
  conclude 中间 张三
  source text "测试" locator "夹具"

rule 中间推无辜 :
  params p : 公民
  premise 中间 p
  conclude 无辜 p
  source text "测试" locator "夹具"

rule r :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 无辜 p
  source text "测试" locator "夹具"
"#;

/// A two-hop chain: one propagation pass is not enough to reach the blocker.
const OPAQUE_TRANSITIVE_CHAIN_THEORY: &str = r#"
sort 公民
pred 侵占 : 公民 → Prop
pred 违法 : 公民 → Prop
pred 无辜 : 公民 → Prop
pred 中间 : 公民 → Prop
pred 第二中间 : 公民 → Prop
obj 张三 : 公民
pred 佐证 : 侵占 张三 → Prop

rule 依赖中间 :
  premise h : 侵占 张三
  unless 佐证 h
  conclude 中间 张三
  source text "测试" locator "夹具"

rule 中间推第二 :
  params p : 公民
  premise 中间 p
  conclude 第二中间 p
  source text "测试" locator "夹具"

rule 第二推无辜 :
  params p : 公民
  premise 第二中间 p
  conclude 无辜 p
  source text "测试" locator "夹具"

rule r :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 无辜 p
  source text "测试" locator "夹具"
"#;

/// Two opaque rules in a row: the second one's premise consumes the first
/// one's opaque conclusion. Both are excluded from fact derivation, but both
/// must stay in the pattern-propagation graph.
const OPAQUE_CHAIN_THROUGH_OPAQUE_THEORY: &str = r#"
sort 公民
pred 侵占 : 公民 → Prop
pred 违法 : 公民 → Prop
pred 中间 : 公民 → Prop
pred 无辜 : 公民 → Prop
obj 张三 : 公民
pred 佐证 : 侵占 张三 → Prop

rule 依赖中间 :
  premise h : 侵占 张三
  conclude 中间 张三
  unless 佐证 h
  source text "测试" locator "夹具"

rule 依赖无辜 :
  premise h : 侵占 张三
  premise m : 中间 张三
  conclude 无辜 张三
  unless 佐证 h
  source text "测试" locator "夹具"

rule r :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 无辜 p
  source text "测试" locator "夹具"
"#;

/// Like [`OPAQUE_CHAIN_THEORY`], but the opaque conclusion appears nested
/// inside another predicate's argument rather than as the whole premise.
const OPAQUE_NESTED_CHAIN_THEORY: &str = r#"
sort 公民
pred 侵占 : 公民 → Prop
pred 违法 : 公民 → Prop
pred 无辜 : 公民 → Prop
pred 中间 : 公民 → Prop
pred 可信 : Prop → Prop
obj 张三 : 公民
pred 佐证 : 侵占 张三 → Prop

rule 依赖中间 :
  premise h : 侵占 张三
  unless 佐证 h
  conclude 中间 张三
  source text "测试" locator "夹具"

rule 嵌套推无辜 :
  params p : 公民
  premise 可信 (中间 p)
  conclude 无辜 p
  source text "测试" locator "夹具"

rule r :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 无辜 p
  source text "测试" locator "夹具"
"#;

/// A rule whose premise head is a parameter (`?p 甲`) consumes an opaque
/// conclusion of any head and instantiates its own conclusion with it.
const OPAQUE_VARIABLE_HEAD_THEORY: &str = r#"
sort 公民
pred 侵占 : 公民 → Prop
pred 违法 : 公民 → Prop
pred 无辜 : 公民 → Prop
pred 中间 : 公民 → Prop
obj 张三 : 公民
obj 甲 : 公民
pred 佐证 : 侵占 张三 → Prop

rule 依赖中间 :
  premise h : 侵占 张三
  unless 佐证 h
  conclude 中间 甲
  source text "测试" locator "夹具"

rule 任意谓词推无辜 :
  params p : 公民 → Prop
  premise p 甲
  conclude 无辜 张三
  source text "测试" locator "夹具"

rule r :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 无辜 p
  source text "测试" locator "夹具"
"#;

/// The blocker is a quantified proposition, so it has no predicate head the
/// checker could confirm.
const HEADLESS_UNLESS_THEORY: &str = r#"
sort 公民
pred 侵占 : 公民 → Prop
pred 违法 : 公民 → Prop
pred 无辜 : 公民 → Prop
obj 张三 : 公民

rule r :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless ∀ (x : 公民), 无辜 x
  source text "测试" locator "夹具"
"#;

/// The environment derives a blocker whose only difference from `r`'s
/// `unless` is the binder name. `print_expr` keeps binder names, so the
/// string key misses it; kernel conversion must not.
const ALPHA_VARIANT_THEORY: &str = r#"
sort 公民
pred 侵占 : 公民 → Prop
pred 违法 : 公民 → Prop
pred 可信 : Prop → Prop
obj 张三 : 公民
axiom 侵占事实 : 侵占 张三
  source text "测试" locator "夹具"

rule 引入可信 :
  premise 侵占 张三
  conclude 可信 (∀ (z : 公民), 侵占 z)
  source text "测试" locator "夹具"

rule r :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 可信 (∀ (y : 公民), 侵占 y)
  source text "测试" locator "夹具"
"#;

/// `可信 侵占` and `可信 (λ x := 侵占 x)` are η-equivalent, but their
/// printed forms differ.
const ETA_VARIANT_THEORY: &str = r#"
sort 公民
pred 侵占 : 公民 → Prop
pred 违法 : 公民 → Prop
pred 可信 : (公民 → Prop) → Prop
obj 张三 : 公民
axiom 侵占事实 : 侵占 张三
  source text "测试" locator "夹具"

rule 引入可信 :
  premise 侵占 张三
  conclude 可信 侵占
  source text "测试" locator "夹具"

rule r :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 可信 (λ (x : 公民) := 侵占 x)
  source text "测试" locator "夹具"
"#;

/// An opaque rule concludes the ground proposition `无辜 李四`. It must block
/// `无辜 李四` and leave `无辜 张三` clear.
const OPAQUE_GROUND_CONCLUSION_THEORY: &str = r#"
sort 公民
pred 侵占 : 公民 → Prop
pred 违法 : 公民 → Prop
pred 无辜 : 公民 → Prop
obj 张三 : 公民
obj 李四 : 公民
pred 佐证 : 侵占 张三 → Prop

rule 依赖推定 :
  premise h : 侵占 张三
  unless 佐证 h
  conclude 无辜 李四
  source text "测试" locator "夹具"

rule r张三 :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 无辜 张三
  source text "测试" locator "夹具"

rule r李四 :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 无辜 李四
  source text "测试" locator "夹具"
"#;

/// The opaque rule concludes `无辜 p`, so its schema is `无辜 ?p`: every
/// individual's `无辜` proposition may hold.
const OPAQUE_VARIABLE_CONCLUSION_THEORY: &str = r#"
sort 公民
pred 侵占 : 公民 → Prop
pred 违法 : 公民 → Prop
pred 无辜 : 公民 → Prop
obj 张三 : 公民
obj 李四 : 公民
pred 佐证 : 侵占 张三 → Prop

rule 依赖推定 :
  params p : 公民
  premise h : 侵占 张三
  premise e : 侵占 p
  unless 佐证 h
  conclude 无辜 p
  source text "测试" locator "夹具"

rule r张三 :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 无辜 张三
  source text "测试" locator "夹具"

rule r李四 :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 无辜 李四
  source text "测试" locator "夹具"
"#;

/// An opaque ground conclusion `中间 李四` feeds the evaluable rule
/// `中间 p → 无辜 p`; only `无辜 李四` may be blocked.
const OPAQUE_ARGUMENT_CHAIN_THEORY: &str = r#"
sort 公民
pred 侵占 : 公民 → Prop
pred 违法 : 公民 → Prop
pred 无辜 : 公民 → Prop
pred 中间 : 公民 → Prop
obj 张三 : 公民
obj 李四 : 公民
pred 佐证 : 侵占 张三 → Prop

rule 依赖中间 :
  premise h : 侵占 张三
  unless 佐证 h
  conclude 中间 李四
  source text "测试" locator "夹具"

rule 中间推无辜 :
  params p : 公民
  premise 中间 p
  conclude 无辜 p
  source text "测试" locator "夹具"

rule r张三 :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 无辜 张三
  source text "测试" locator "夹具"

rule r李四 :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 无辜 李四
  source text "测试" locator "夹具"
"#;

/// The intermediate predicate sits inside another predicate's argument:
/// `可信 (中间 p) → 无辜 p`. The pattern `中间 李四` reaches the nested
/// occurrence and must bind `p` to `李四` only.
const OPAQUE_NESTED_ARGUMENT_THEORY: &str = r#"
sort 公民
pred 侵占 : 公民 → Prop
pred 违法 : 公民 → Prop
pred 无辜 : 公民 → Prop
pred 中间 : 公民 → Prop
pred 可信 : Prop → Prop
obj 张三 : 公民
obj 李四 : 公民
pred 佐证 : 侵占 张三 → Prop

rule 依赖中间 :
  premise h : 侵占 张三
  unless 佐证 h
  conclude 中间 李四
  source text "测试" locator "夹具"

rule 嵌套推无辜 :
  params p : 公民
  premise 可信 (中间 p)
  conclude 无辜 p
  source text "测试" locator "夹具"

rule r张三 :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 无辜 张三
  source text "测试" locator "夹具"

rule r李四 :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 无辜 李四
  source text "测试" locator "夹具"
"#;

/// A premise whose head is a rule parameter (`?f 甲`) consumes the opaque
/// conclusion `中间 甲`; the resulting ground conclusion is `无辜 张三` only.
const OPAQUE_PARAMETER_HEAD_THEORY: &str = r#"
sort 公民
pred 侵占 : 公民 → Prop
pred 违法 : 公民 → Prop
pred 无辜 : 公民 → Prop
pred 中间 : 公民 → Prop
obj 张三 : 公民
obj 李四 : 公民
obj 甲 : 公民
pred 佐证 : 侵占 张三 → Prop

rule 依赖中间 :
  premise h : 侵占 张三
  unless 佐证 h
  conclude 中间 甲
  source text "测试" locator "夹具"

rule 任意谓词推无辜 :
  params f : 公民 → Prop
  premise f 甲
  conclude 无辜 张三
  source text "测试" locator "夹具"

rule r张三 :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 无辜 张三
  source text "测试" locator "夹具"

rule r李四 :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 无辜 李四
  source text "测试" locator "夹具"
"#;

/// The opaque conclusion is an application of a function parameter,
/// `?f 甲`. Such a parameter may be instantiated by `λ _. B`, so the
/// conclusion can denote any proposition; it must not be matched by binding
/// `?f` to the syntactic function part only.
const OPAQUE_APPLIED_VARIABLE_THEORY: &str = r#"
sort 公民
pred 侵占 : 公民 → Prop
pred 违法 : 公民 → Prop
pred 任二 : 公民 → 公民 → Prop
pred 任意 : (公民 → Prop) → Prop
obj 张三 : 公民
obj 甲 : 公民
obj 乙 : 公民
pred 佐证 : 侵占 张三 → Prop

rule 依赖任意 :
  params f : 公民 → Prop
  premise h : 侵占 张三
  premise e : 任意 f
  unless 佐证 h
  conclude f 甲
  source text "测试" locator "夹具"

rule r二元 :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 任二 甲 乙
  source text "测试" locator "夹具"

rule r二元同参 :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 任二 甲 甲
  source text "测试" locator "夹具"
"#;

/// The opaque conclusion is `可信 (中间 李四)`. Rules whose blocker shares
/// the same outer head but another argument or another nesting depth must not
/// be rejected.
const OPAQUE_SAME_HEAD_STRUCTURE_THEORY: &str = r#"
sort 公民
pred 侵占 : 公民 → Prop
pred 违法 : 公民 → Prop
pred 中间 : 公民 → Prop
pred 可信 : Prop → Prop
obj 张三 : 公民
obj 李四 : 公民
pred 佐证 : 侵占 张三 → Prop

rule 依赖可信 :
  premise h : 侵占 张三
  unless 佐证 h
  conclude 可信 (中间 李四)
  source text "测试" locator "夹具"

rule r另一参数 :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 可信 (中间 张三)
  source text "测试" locator "夹具"

rule r另一层 :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 可信 (可信 (中间 李四))
  source text "测试" locator "夹具"

rule r自身 :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 可信 (中间 李四)
  source text "测试" locator "夹具"
"#;

/// A rule conclusion contains a literal beta-redex, so the reasoner stores a
/// fact whose raw form matches `应用 (?g 甲)` while its normal form does not.
/// A rule with such a premise cannot be matched against normal facts exactly.
const OPAQUE_BETA_PREMISE_THEORY: &str = r#"
sort 公民
pred 侵占 : 公民 → Prop
pred 违法 : 公民 → Prop
pred 无辜 : 公民 → Prop
pred 应用 : Prop → Prop
obj 张三 : 公民
obj 甲 : 公民

axiom 侵占事实 : 侵占 张三
  source text "测试" locator "夹具"

rule 产生应用 :
  premise 侵占 张三
  conclude 应用 ((λ (x : 公民) := 侵占 张三) 甲)
  source text "测试" locator "夹具"

rule 应用推无辜 :
  params g : 公民 → Prop
  premise 应用 (g 甲)
  conclude 无辜 张三
  source text "测试" locator "夹具"

rule r :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 无辜 张三
  source text "测试" locator "夹具"
"#;

/// The opaque conclusion applies a function parameter under a binder, so an
/// instance can depend on the bound variable through beta-reduction:
/// `g := λ x, x` turns `应用 (g x)` into `应用 x`, which the environment
/// axiom makes reachable.
const OPAQUE_BOUND_APPLICATION_THEORY: &str = r#"
sort 公民
pred 侵占 : 公民 → Prop
pred 违法 : 公民 → Prop
pred 应用 : 公民 → Prop
pred 可信 : Prop → Prop
pred 任意 : (公民 → 公民) → Prop
obj 张三 : 公民
pred 佐证 : 侵占 张三 → Prop

axiom 任意事实 : 任意 (λ (x : 公民) := x)
  source text "测试" locator "夹具"

rule 依赖全称 :
  params g : 公民 → 公民
  premise h : 侵占 张三
  premise e : 任意 g
  unless 佐证 h
  conclude 可信 (∀ (x : 公民), 应用 (g x))
  source text "测试" locator "夹具"

rule r :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 可信 (∀ (x : 公民), 应用 x)
  source text "测试" locator "夹具"
"#;

/// The opaque rule concludes `可信 侵占`; the gating rule asks for its
/// eta-expanded form `可信 (λ x, 侵占 x)`. Only conversion, not printed
/// equality, sees them as the same proposition.
const OPAQUE_ETA_CONCLUSION_THEORY: &str = r#"
sort 公民
pred 侵占 : 公民 → Prop
pred 违法 : 公民 → Prop
pred 可信 : (公民 → Prop) → Prop
obj 张三 : 公民
pred 佐证 : 侵占 张三 → Prop

rule 依赖可信 :
  premise h : 侵占 张三
  unless 佐证 h
  conclude 可信 侵占
  source text "测试" locator "夹具"

rule r :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 可信 (λ (x : 公民) := 侵占 x)
  source text "测试" locator "夹具"
"#;

/// The opaque rule concludes an eta-expanded `可信 (λ x, 侵占 x)`; the next
/// rule consumes the eta-expanded `可信 (λ x, f x)`. Both must be matched in
/// their common short form, or the chain is missed.
const OPAQUE_ETA_PROPAGATION_THEORY: &str = r#"
sort 公民
pred 侵占 : 公民 → Prop
pred 违法 : 公民 → Prop
pred 无辜 : 公民 → Prop
pred 可信 : (公民 → Prop) → Prop
obj 张三 : 公民
pred 佐证 : 侵占 张三 → Prop

rule 依赖展开 :
  premise h : 侵占 张三
  unless 佐证 h
  conclude 可信 (λ (x : 公民) := 侵占 x)
  source text "测试" locator "夹具"

rule 展开推无辜 :
  params f : 公民 → Prop
  premise 可信 (λ (x : 公民) := f x)
  conclude 无辜 张三
  source text "测试" locator "夹具"

rule r :
  params p : 公民
  premise 侵占 p
  conclude 违法 p
  unless 无辜 张三
  source text "测试" locator "夹具"
"#;

fn env_from(name: &str, source: &str) -> Env {
    let mut library = Library::new();
    library.load(name, source).expect("test theory loads");
    library.env
}

fn env() -> Env {
    env_from("cert-check", THEORY)
}

fn axiom_env() -> Env {
    env_from("cert-check-axiom", AXIOM_THEORY)
}

fn dependent_env() -> Env {
    env_from("cert-check-dependent", DEPENDENT_THEORY)
}

fn derived_blocker_env() -> Env {
    env_from("cert-check-derived-blocker", DERIVED_BLOCKER_THEORY)
}

fn transitive_blocker_env() -> Env {
    env_from("cert-check-transitive-blocker", TRANSITIVE_BLOCKER_THEORY)
}

fn unrelated_blocker_env() -> Env {
    env_from("cert-check-unrelated-blocker", UNRELATED_BLOCKER_THEORY)
}

fn unmatched_blocker_env() -> Env {
    env_from("cert-check-unmatched-blocker", UNMATCHED_BLOCKER_THEORY)
}

fn opaque_blocker_env() -> Env {
    env_from("cert-check-opaque-blocker", OPAQUE_BLOCKER_THEORY)
}

fn opaque_chain_env() -> Env {
    env_from("cert-check-opaque-chain", OPAQUE_CHAIN_THEORY)
}

fn opaque_transitive_chain_env() -> Env {
    env_from(
        "cert-check-opaque-transitive-chain",
        OPAQUE_TRANSITIVE_CHAIN_THEORY,
    )
}

fn opaque_chain_through_opaque_env() -> Env {
    env_from(
        "cert-check-opaque-chain-through-opaque",
        OPAQUE_CHAIN_THROUGH_OPAQUE_THEORY,
    )
}

fn opaque_nested_chain_env() -> Env {
    env_from("cert-check-opaque-nested-chain", OPAQUE_NESTED_CHAIN_THEORY)
}

fn opaque_variable_head_env() -> Env {
    env_from(
        "cert-check-opaque-variable-head",
        OPAQUE_VARIABLE_HEAD_THEORY,
    )
}

fn headless_unless_env() -> Env {
    env_from("cert-check-headless-unless", HEADLESS_UNLESS_THEORY)
}

fn alpha_variant_env() -> Env {
    env_from("cert-check-alpha-variant", ALPHA_VARIANT_THEORY)
}

fn eta_variant_env() -> Env {
    env_from("cert-check-eta-variant", ETA_VARIANT_THEORY)
}

fn opaque_ground_conclusion_env() -> Env {
    env_from(
        "cert-check-opaque-ground-conclusion",
        OPAQUE_GROUND_CONCLUSION_THEORY,
    )
}

fn opaque_variable_conclusion_env() -> Env {
    env_from(
        "cert-check-opaque-variable-conclusion",
        OPAQUE_VARIABLE_CONCLUSION_THEORY,
    )
}

fn opaque_argument_chain_env() -> Env {
    env_from(
        "cert-check-opaque-argument-chain",
        OPAQUE_ARGUMENT_CHAIN_THEORY,
    )
}

fn opaque_nested_argument_env() -> Env {
    env_from(
        "cert-check-opaque-nested-argument",
        OPAQUE_NESTED_ARGUMENT_THEORY,
    )
}

fn opaque_parameter_head_env() -> Env {
    env_from(
        "cert-check-opaque-parameter-head",
        OPAQUE_PARAMETER_HEAD_THEORY,
    )
}

fn opaque_applied_variable_env() -> Env {
    env_from(
        "cert-check-opaque-applied-variable",
        OPAQUE_APPLIED_VARIABLE_THEORY,
    )
}

fn opaque_same_head_structure_env() -> Env {
    env_from(
        "cert-check-opaque-same-head-structure",
        OPAQUE_SAME_HEAD_STRUCTURE_THEORY,
    )
}

fn opaque_beta_premise_env() -> Env {
    env_from("cert-check-opaque-beta-premise", OPAQUE_BETA_PREMISE_THEORY)
}

fn opaque_bound_application_env() -> Env {
    env_from(
        "cert-check-opaque-bound-application",
        OPAQUE_BOUND_APPLICATION_THEORY,
    )
}

fn opaque_eta_conclusion_env() -> Env {
    env_from(
        "cert-check-opaque-eta-conclusion",
        OPAQUE_ETA_CONCLUSION_THEORY,
    )
}

fn opaque_eta_propagation_env() -> Env {
    env_from(
        "cert-check-opaque-eta-propagation",
        OPAQUE_ETA_PROPAGATION_THEORY,
    )
}

/// A rule with three premises over 120 facts has more than the closure's
/// matching budget. A certificate without any `unless` must not pay for it.
fn many_facts_env() -> Env {
    let mut source = String::from(
        "sort 公民\n\
         pred P : 公民 → Prop\n\
         pred Q : 公民 → 公民 → 公民 → Prop\n\
         rule 组合 :\n\
           params a : 公民, b : 公民, c : 公民\n\
           premise P a\n\
           premise P b\n\
           premise P c\n\
           conclude Q a b c\n\
           source text \"测试\" locator \"夹具\"\n",
    );
    for i in 0..120 {
        source.push_str(&format!("obj c{i} : 公民\n"));
    }
    for i in 0..120 {
        source.push_str(&format!(
            "axiom p{i} : P c{i}\n  source text \"测试\" locator \"夹具\"\n"
        ));
    }
    env_from("cert-check-many-facts", &source)
}

fn constant(name: &str) -> CertExpr {
    CertExpr::Const {
        name: name.to_owned(),
    }
}

fn app(func: CertExpr, arg: CertExpr) -> CertExpr {
    CertExpr::App {
        func: Box::new(func),
        arg: Box::new(arg),
    }
}

fn atom(predicate: &str, object: &str) -> CertExpr {
    app(constant(predicate), constant(object))
}

fn premise(proposition: CertExpr) -> Assumption {
    Assumption {
        proposition,
        sources: Vec::new(),
        label: None,
    }
}

fn assumption_node(assumption: usize) -> Node {
    Node::Assumption { assumption }
}

fn rule_node(conclusion: CertExpr, premises: Vec<usize>, bindings: Vec<(&str, CertExpr)>) -> Node {
    rule_node_for("r", conclusion, premises, bindings)
}

fn rule_node_for(
    rule: &str,
    conclusion: CertExpr,
    premises: Vec<usize>,
    bindings: Vec<(&str, CertExpr)>,
) -> Node {
    Node::RuleApplication {
        rule: rule.to_owned(),
        conclusion,
        premises,
        bindings: bindings
            .into_iter()
            .map(|(parameter, value)| Binding {
                parameter: parameter.to_owned(),
                value,
            })
            .collect(),
        sources: Vec::new(),
    }
}

fn conflict(left: CertExpr, right: CertExpr, resolution: Resolution) -> Conflict {
    Conflict {
        left,
        right,
        left_by: Provenance::Rules {
            rules: vec!["r".to_owned()],
        },
        right_by: Provenance::Rules {
            rules: vec!["r".to_owned()],
        },
        resolution,
    }
}

fn gap_node(proposition: CertExpr) -> Node {
    Node::Gap {
        proposition,
        candidates: Vec::new(),
        note: None,
    }
}

fn certificate(assumptions: Vec<Assumption>, nodes: Vec<Node>, root: Option<usize>) -> Certificate {
    Certificate {
        format_version: FormatVersion::CURRENT,
        environment: EnvironmentIdentity::Unrecorded,
        assumptions,
        nodes,
        root,
        conflicts: Vec::new(),
        open_obligations: Vec::new(),
        metadata: Default::default(),
    }
}

fn legal_certificate() -> Certificate {
    certificate(
        vec![premise(atom("侵占", "张三"))],
        vec![
            assumption_node(0),
            rule_node(atom("违法", "张三"), vec![0], vec![("p", constant("张三"))]),
        ],
        Some(1),
    )
}

fn reject(cert: &Certificate) -> CheckError {
    check(&env(), cert).expect_err("certificate must be rejected")
}

fn reject_at(cert: &Certificate, node: usize) -> CheckError {
    let error = reject(cert);
    assert_eq!(error.node, Some(node), "{error}");
    error
}

#[test]
fn legal_certificate_passes() {
    let report = check(&env(), &legal_certificate()).expect("legal certificate passes");
    assert_eq!(
        report,
        CheckReport {
            root_proved: true,
            root_is_assumption: false,
            assumption_count: 1,
            conflict_resolved: false,
            requires_human: false,
            priority_sources_checked: false,
            nodes_checked: 2,
        }
    );
}

#[test]
fn assumption_root_is_a_conditional_proof() {
    let cert = certificate(
        vec![premise(atom("侵占", "张三"))],
        vec![assumption_node(0)],
        Some(0),
    );
    let report = check(&env(), &cert).expect("an assumption root is a legal proof");
    assert_eq!(
        report,
        CheckReport {
            root_proved: true,
            root_is_assumption: true,
            assumption_count: 1,
            conflict_resolved: false,
            requires_human: false,
            priority_sources_checked: false,
            nodes_checked: 1,
        }
    );
}

#[test]
fn premise_count_mismatch_is_rejected() {
    let mut cert = legal_certificate();
    cert.nodes[1] = rule_node(
        atom("违法", "张三"),
        Vec::new(),
        vec![("p", constant("张三"))],
    );
    let error = reject_at(&cert, 1);
    assert!(error.message.contains("有 1 个前提"), "{error}");
}

#[test]
fn extra_premise_is_rejected() {
    let mut cert = legal_certificate();
    cert.nodes[1] = rule_node(
        atom("违法", "张三"),
        vec![0, 0],
        vec![("p", constant("张三"))],
    );
    let error = reject_at(&cert, 1);
    assert!(error.message.contains("本步引用了 2 个节点"), "{error}");
}

#[test]
fn out_of_range_premise_node_is_rejected() {
    let mut cert = legal_certificate();
    cert.nodes[1] = rule_node(atom("违法", "张三"), vec![7], vec![("p", constant("张三"))]);
    let error = reject_at(&cert, 1);
    assert!(error.message.contains("越界"), "{error}");
}

#[test]
fn forward_premise_reference_is_rejected() {
    let cert = certificate(
        vec![premise(atom("侵占", "张三"))],
        vec![
            rule_node(atom("违法", "张三"), vec![1], vec![("p", constant("张三"))]),
            assumption_node(0),
        ],
        Some(0),
    );
    let error = reject_at(&cert, 0);
    assert!(error.message.contains("之前的节点"), "{error}");
}

#[test]
fn unknown_rule_is_rejected() {
    let mut cert = legal_certificate();
    let Node::RuleApplication { rule, .. } = &mut cert.nodes[1] else {
        panic!("node 1 is a rule application");
    };
    *rule = "不存在".to_owned();
    let error = reject_at(&cert, 1);
    assert!(error.message.contains("未知规则"), "{error}");
}

#[test]
fn non_rule_declaration_is_rejected() {
    let mut cert = legal_certificate();
    let Node::RuleApplication { rule, .. } = &mut cert.nodes[1] else {
        panic!("node 1 is a rule application");
    };
    *rule = "侵占".to_owned();
    let error = reject_at(&cert, 1);
    assert!(error.message.contains("不是规则"), "{error}");
}

#[test]
fn missing_binding_is_rejected() {
    let mut cert = legal_certificate();
    cert.nodes[1] = rule_node(atom("违法", "张三"), vec![0], Vec::new());
    let error = reject_at(&cert, 1);
    assert!(error.message.contains("没有绑定"), "{error}");
}

#[test]
fn unknown_binding_parameter_is_rejected() {
    let mut cert = legal_certificate();
    cert.nodes[1] = rule_node(
        atom("违法", "张三"),
        vec![0],
        vec![("p", constant("张三")), ("q", constant("李四"))],
    );
    let error = reject_at(&cert, 1);
    assert!(error.message.contains("不是规则 `r` 的参数"), "{error}");
}

#[test]
fn duplicate_binding_is_rejected() {
    let mut cert = legal_certificate();
    cert.nodes[1] = rule_node(
        atom("违法", "张三"),
        vec![0],
        vec![("p", constant("张三")), ("p", constant("李四"))],
    );
    let error = reject_at(&cert, 1);
    assert!(error.message.contains("重复绑定"), "{error}");
}

#[test]
fn unclosed_binding_is_rejected() {
    let mut cert = legal_certificate();
    cert.nodes[1] = rule_node(
        atom("违法", "张三"),
        vec![0],
        vec![("p", CertExpr::Var { index: 0 })],
    );
    let error = reject_at(&cert, 1);
    assert!(error.message.contains("不是闭合项"), "{error}");
}

#[test]
fn binding_drift_is_rejected() {
    let mut cert = legal_certificate();
    cert.nodes[1] = rule_node(atom("违法", "李四"), vec![0], vec![("p", constant("李四"))]);
    let error = reject_at(&cert, 1);
    assert!(error.message.contains("第 1 个前提实例"), "{error}");
}

#[test]
fn conclusion_mismatch_is_rejected() {
    let mut cert = legal_certificate();
    cert.nodes[1] = rule_node(atom("违法", "李四"), vec![0], vec![("p", constant("张三"))]);
    let error = reject_at(&cert, 1);
    assert!(error.message.contains("实例结论"), "{error}");
}

#[test]
fn proved_unless_condition_is_rejected() {
    let cert = certificate(
        vec![premise(atom("侵占", "张三")), premise(atom("无辜", "张三"))],
        vec![
            assumption_node(0),
            assumption_node(1),
            rule_node(atom("违法", "张三"), vec![0], vec![("p", constant("张三"))]),
        ],
        Some(2),
    );
    let error = reject_at(&cert, 2);
    assert!(error.message.contains("阻断条件"), "{error}");
}

#[test]
fn unless_proved_later_in_the_certificate_still_blocks() {
    let cert = certificate(
        vec![premise(atom("侵占", "张三")), premise(atom("无辜", "张三"))],
        vec![
            assumption_node(0),
            rule_node(atom("违法", "张三"), vec![0], vec![("p", constant("张三"))]),
            assumption_node(1),
        ],
        Some(1),
    );
    let error = reject_at(&cert, 1);
    assert!(error.message.contains("阻断条件"), "{error}");
}

#[test]
fn environment_axiom_blocks_unless_when_the_certificate_omits_its_node() {
    // The same certificate passes when the axiom is absent: only the trimmed
    // proof differs, the environment fact is what the step must see.
    let cert = legal_certificate();
    check(&env(), &cert).expect("without the axiom the certificate passes");

    let error =
        check(&axiom_env(), &cert).expect_err("a trimmed certificate must not drop the blocker");
    assert_eq!(error.node, Some(1), "{error}");
    assert!(error.message.contains("阻断条件"), "{error}");
    assert!(error.message.contains("无辜"), "{error}");
}

#[test]
fn unless_that_depends_on_a_premise_binder_is_rejected() {
    let cert = certificate(
        vec![premise(atom("侵占", "张三"))],
        vec![
            assumption_node(0),
            rule_node_for("依赖阻断", atom("违法", "张三"), vec![0], Vec::new()),
        ],
        Some(1),
    );
    let error = check(&dependent_env(), &cert)
        .expect_err("a blocker that mentions a premise binder is not supported");
    assert_eq!(error.node, Some(1), "{error}");
    assert!(error.message.contains("依赖前提暂不支持"), "{error}");
}

#[test]
fn a_later_premise_that_depends_on_a_premise_binder_is_rejected() {
    let cert = certificate(
        vec![premise(atom("侵占", "张三")), premise(atom("侵占", "张三"))],
        vec![
            assumption_node(0),
            assumption_node(1),
            rule_node_for("依赖前提", atom("违法", "张三"), vec![0, 1], Vec::new()),
        ],
        Some(2),
    );
    let error = check(&dependent_env(), &cert)
        .expect_err("a premise that mentions a premise binder is not supported");
    assert_eq!(error.node, Some(2), "{error}");
    assert!(error.message.contains("依赖前提暂不支持"), "{error}");
}

#[test]
fn gap_cannot_be_a_premise() {
    let cert = certificate(
        Vec::new(),
        vec![
            gap_node(atom("侵占", "张三")),
            rule_node(atom("违法", "张三"), vec![0], vec![("p", constant("张三"))]),
        ],
        Some(1),
    );
    let error = reject_at(&cert, 1);
    assert!(error.message.contains("缺口"), "{error}");
}

#[test]
fn root_index_out_of_range_is_rejected() {
    let mut cert = legal_certificate();
    cert.root = Some(9);
    let error = reject_at(&cert, 9);
    assert!(error.message.contains("根节点索引越界"), "{error}");
}

#[test]
fn root_may_be_a_gap_and_is_not_proved() {
    let cert = certificate(Vec::new(), vec![gap_node(atom("侵占", "张三"))], Some(0));
    let report = check(&env(), &cert).expect("a gap-only certificate is well-formed");
    assert_eq!(
        report,
        CheckReport {
            root_proved: false,
            root_is_assumption: false,
            assumption_count: 0,
            conflict_resolved: false,
            requires_human: false,
            priority_sources_checked: false,
            nodes_checked: 1,
        }
    );
}

#[test]
fn root_in_an_unresolved_conflict_is_rejected() {
    let mut cert = legal_certificate();
    cert.conflicts.push(conflict(
        atom("违法", "张三"),
        atom("无辜", "张三"),
        Resolution::Unresolved,
    ));
    let error = reject_at(&cert, 1);
    assert!(error.message.contains("未决状态"), "{error}");
    assert!(error.message.contains("冲突"), "{error}");
}

#[test]
fn root_on_the_losing_side_of_a_resolved_conflict_is_rejected() {
    let mut cert = legal_certificate();
    cert.conflicts.push(conflict(
        atom("违法", "张三"),
        atom("无辜", "张三"),
        Resolution::Defeated {
            winner: Side::Right,
        },
    ));
    let error = reject_at(&cert, 1);
    assert!(error.message.contains("败方"), "{error}");
}

#[test]
fn root_on_the_winning_side_of_a_resolved_conflict_is_reported() {
    let mut cert = legal_certificate();
    cert.conflicts.push(conflict(
        atom("违法", "张三"),
        atom("无辜", "张三"),
        Resolution::Defeated { winner: Side::Left },
    ));
    let report = check(&env(), &cert).expect("a winning root is allowed");
    assert!(report.root_proved);
    assert!(report.conflict_resolved);
    assert!(
        !report.priority_sources_checked,
        "the priority source behind the defeat is not validated"
    );
}

#[test]
fn an_unresolved_conflict_about_another_proposition_does_not_reject_the_root() {
    let mut cert = legal_certificate();
    cert.conflicts.push(conflict(
        atom("侵占", "李四"),
        atom("无辜", "李四"),
        Resolution::Unresolved,
    ));
    let report = check(&env(), &cert).expect("only the root's conflicts are adjudicated");
    assert!(!report.conflict_resolved);
}

#[test]
fn open_obligations_do_not_fail_but_require_human() {
    let mut cert = legal_certificate();
    cert.open_obligations.push(OpenObligation {
        id: "ob-1".to_owned(),
        kind: ObligationKind::MissingSource,
        description: "缺少来源".to_owned(),
        nodes: vec![1],
    });
    let report = check(&env(), &cert).expect("open obligations do not fail the check");
    assert!(report.root_proved);
    assert!(report.requires_human);
}

#[test]
fn missing_root_is_not_proved() {
    let mut cert = legal_certificate();
    cert.root = None;
    let report = check(&env(), &cert).expect("a rootless certificate is well-formed");
    assert!(!report.root_proved);
    assert_eq!(report.nodes_checked, 2);
}

#[test]
fn out_of_range_assumption_index_is_rejected() {
    let cert = certificate(Vec::new(), vec![assumption_node(0)], Some(0));
    let error = reject_at(&cert, 0);
    assert!(error.message.contains("不存在的假设"), "{error}");
}

#[test]
fn assumption_must_be_a_proposition() {
    let cert = certificate(
        vec![premise(constant("侵占"))],
        vec![assumption_node(0)],
        Some(0),
    );
    let error = reject_at(&cert, 0);
    assert!(error.message.contains("假设不是命题"), "{error}");
}

/// A certificate that proves only the premise of `r`, not the blocker its
/// environment can derive. The checker must reject the step: the environment
/// proves `无辜 张三`, and the certificate's silence is not a counter-proof.
#[test]
fn derived_blocker_is_not_bypassed_by_omitting_its_node() {
    let cert = certificate(
        vec![premise(atom("侵占", "张三"))],
        vec![
            assumption_node(0),
            rule_node(atom("违法", "张三"), vec![0], vec![("p", constant("张三"))]),
        ],
        Some(1),
    );
    let error = check(&derived_blocker_env(), &cert)
        .expect_err("a blocker derived by an environment rule must not be omitted");
    assert_eq!(error.node, Some(1), "{error}");
    assert!(
        error.message.contains("无辜") || error.message.contains("阻断"),
        "{error}"
    );
}

/// `有罪 p → 可罚 p → 无辜 p`: the closure must reach a fixed point, not stop
/// after one layer of environment rules.
#[test]
fn transitive_derived_blocker_is_detected() {
    let cert = certificate(
        vec![premise(atom("侵占", "张三"))],
        vec![
            assumption_node(0),
            rule_node(atom("违法", "张三"), vec![0], vec![("p", constant("张三"))]),
        ],
        Some(1),
    );
    let error = check(&transitive_blocker_env(), &cert)
        .expect_err("a blocker derived through two environment rules must be found");
    assert_eq!(error.node, Some(1), "{error}");
    assert!(
        error.message.contains("无辜") || error.message.contains("阻断"),
        "{error}"
    );
}

/// The environment derives `无辜 李四`, not `无辜 张三`. Predicate names alone
/// are not enough: the individual matters.
#[test]
fn unrelated_individual_does_not_block() {
    let cert = certificate(
        vec![premise(atom("侵占", "张三"))],
        vec![
            assumption_node(0),
            rule_node(atom("违法", "张三"), vec![0], vec![("p", constant("张三"))]),
        ],
        Some(1),
    );
    let report = check(&unrelated_blocker_env(), &cert)
        .expect("a blocker derived for another individual does not block this step");
    assert!(report.root_proved);
}

/// An assumption in the table blocks the rule even when no node cites it:
/// `root_proved` is relative to every assumption the certificate lists.
#[test]
fn unused_blocker_assumption_is_detected() {
    let cert = certificate(
        vec![premise(atom("侵占", "张三")), premise(atom("无辜", "张三"))],
        vec![
            assumption_node(0),
            rule_node(atom("违法", "张三"), vec![0], vec![("p", constant("张三"))]),
        ],
        Some(1),
    );
    let error = check(&env(), &cert)
        .expect_err("an unused blocker assumption is still part of the context");
    assert_eq!(error.node, Some(1), "{error}");
    assert!(error.message.contains("阻断条件"), "{error}");
    assert!(error.message.contains("无辜"), "{error}");
}

/// The only rule concluding `无辜` has a premise that matches no fact. It
/// derives nothing, so the blocker is not reachable.
#[test]
fn a_rule_that_cannot_derive_the_blocker_does_not_block() {
    let cert = certificate(
        vec![premise(atom("侵占", "张三"))],
        vec![
            assumption_node(0),
            rule_node(atom("违法", "张三"), vec![0], vec![("p", constant("张三"))]),
        ],
        Some(1),
    );
    let report = check(&unmatched_blocker_env(), &cert)
        .expect("a rule whose premises match no fact derives nothing");
    assert!(report.root_proved);
}

/// The opaque rule concludes `中间 张三`; the intermediate rule turns
/// `中间 p` into `无辜 p`. The opaque conclusion must propagate through the
/// intermediate rule, or `r`'s blocker looks clear.
#[test]
fn opaque_head_propagates_through_an_intermediate_rule() {
    let error = check(&opaque_chain_env(), &legal_certificate())
        .expect_err("the opaque conclusion must propagate through the intermediate rule");
    assert_eq!(error.node, Some(1), "{error}");
    assert!(error.message.contains("无法确认阻断状态"), "{error}");
}

/// One propagation pass would stop at `第二中间`; the loop must continue until
/// `无辜 张三` is a pattern as well.
#[test]
fn opaque_head_propagation_reaches_a_fixed_point() {
    let error = check(&opaque_transitive_chain_env(), &legal_certificate())
        .expect_err("opaque conclusions must propagate across multiple rules");
    assert_eq!(error.node, Some(1), "{error}");
    assert!(error.message.contains("无法确认阻断状态"), "{error}");
}

/// Both rules are opaque; the second one's conclusion is registered as a
/// pattern when it is opened. This test also guards that opaque rules stay in
/// the propagation graph instead of being silently dropped from it.
#[test]
fn opaque_head_propagates_through_another_opaque_rule() {
    let error = check(&opaque_chain_through_opaque_env(), &legal_certificate())
        .expect_err("an opaque rule's conclusion must stay in the propagation graph");
    assert_eq!(error.node, Some(1), "{error}");
    assert!(error.message.contains("无法确认阻断状态"), "{error}");
}

/// The opaque conclusion appears nested inside `可信 (...)`, not as the whole
/// premise. Propagation must still find it.
#[test]
fn opaque_head_propagates_from_a_nested_premise() {
    let error = check(&opaque_nested_chain_env(), &legal_certificate())
        .expect_err("a nested occurrence of an opaque conclusion must propagate");
    assert_eq!(error.node, Some(1), "{error}");
    assert!(error.message.contains("无法确认阻断状态"), "{error}");
}

/// A parameter-headed premise (`?p 甲`) consumes the opaque conclusion
/// `中间 甲` and instantiates its own conclusion with it.
#[test]
fn a_parameter_head_premise_is_opaque_when_opaque_heads_exist() {
    let error = check(&opaque_variable_head_env(), &legal_certificate())
        .expect_err("a parameter-head premise must consume the opaque conclusion");
    assert_eq!(error.node, Some(1), "{error}");
    assert!(error.message.contains("无法确认阻断状态"), "{error}");
}

/// A quantified `unless` has no predicate head; leaving that unconfirmed must
/// reject, not pass.
#[test]
fn unless_without_extractable_head_is_rejected() {
    let error = check(&headless_unless_env(), &legal_certificate())
        .expect_err("a blocker without an extractable head cannot be cleared");
    assert_eq!(error.node, Some(1), "{error}");
    assert!(error.message.contains("没有可提取的谓词头"), "{error}");
}

/// A listed assumption must be a proposition even when no node cites it.
#[test]
fn unused_assumption_must_be_a_proposition() {
    let cert = certificate(vec![premise(constant("侵占"))], Vec::new(), None);
    let error = check(&env(), &cert).expect_err("an unused assumption must still be a proposition");
    assert!(error.message.contains("不是命题"), "{error}");
}

/// The environment derives the same quantified proposition as the blocker,
/// but with a different binder name. String keys miss it; conversion must not.
#[test]
fn alpha_variant_of_blocker_is_detected() {
    let error = check(&alpha_variant_env(), &legal_certificate())
        .expect_err("an alpha variant of the derived blocker must block the step");
    assert_eq!(error.node, Some(1), "{error}");
    assert!(
        error.message.contains("阻断") || error.message.contains("可能"),
        "{error}"
    );
}

/// The environment derives `可信 侵占`; the blocker is its η-expanded form.
#[test]
fn eta_variant_of_blocker_is_detected() {
    let error = check(&eta_variant_env(), &legal_certificate())
        .expect_err("an eta variant of the derived blocker must block the step");
    assert_eq!(error.node, Some(1), "{error}");
    assert!(
        error.message.contains("阻断") || error.message.contains("可能"),
        "{error}"
    );
}

/// The environment's three-premise rule exceeds the closure's matching budget.
/// A gap-only certificate has no `unless`, so it must not run the closure.
#[test]
fn a_gap_certificate_does_not_require_the_unless_closure() {
    let cert = certificate(Vec::new(), vec![gap_node(atom("P", "c0"))], Some(0));
    let report = check(&many_facts_env(), &cert)
        .expect("a certificate without unless conditions does not need the closure");
    assert!(!report.root_proved);
}

#[test]
fn an_opaque_rule_head_prevents_clearing_the_blocker() {
    let cert = certificate(
        vec![premise(atom("侵占", "张三"))],
        vec![
            assumption_node(0),
            rule_node(atom("违法", "张三"), vec![0], vec![("p", constant("张三"))]),
        ],
        Some(1),
    );
    let error = check(&opaque_blocker_env(), &cert)
        .expect_err("an unconfirmable blocker must not be cleared");
    assert_eq!(error.node, Some(1), "{error}");
    assert!(error.message.contains("无法确认阻断状态"), "{error}");
    assert!(error.message.contains("无法静态求值"), "{error}");
}

/// A rule step whose only `unless` is `rule`'s, instantiated with `p = 张三`.
fn gated_step(rule: &str) -> Certificate {
    certificate(
        vec![premise(atom("侵占", "张三"))],
        vec![
            assumption_node(0),
            rule_node_for(
                rule,
                atom("违法", "张三"),
                vec![0],
                vec![("p", constant("张三"))],
            ),
        ],
        Some(1),
    )
}

/// A ground opaque conclusion blocks itself and nothing else with the same
/// predicate name.
#[test]
fn opaque_ground_conclusion_blocks_only_its_own_argument() {
    let env = opaque_ground_conclusion_env();
    let report = check(&env, &gated_step("r张三"))
        .expect("an opaque conclusion about another individual must not block");
    assert!(report.root_proved);

    let error = check(&env, &gated_step("r李四"))
        .expect_err("the opaque rule's own ground conclusion must block");
    assert_eq!(error.node, Some(1), "{error}");
    assert!(error.message.contains("无法确认阻断状态"), "{error}");
    assert!(error.message.contains("无辜"), "{error}");
}

/// A `?p` conclusion schema blocks every individual.
#[test]
fn opaque_variable_conclusion_blocks_every_individual() {
    let env = opaque_variable_conclusion_env();
    for rule in ["r张三", "r李四"] {
        let error = check(&env, &gated_step(rule))
            .expect_err("an opaque variable conclusion must block every individual");
        assert_eq!(error.node, Some(1), "{error}");
        assert!(error.message.contains("无法确认阻断状态"), "{error}");
    }
}

/// Pattern propagation follows an evaluable rule from an opaque intermediate
/// conclusion to the blocker, keeping the bound individual.
#[test]
fn opaque_chain_reaches_the_blocker_argument() {
    let env = opaque_argument_chain_env();
    let report = check(&env, &gated_step("r张三"))
        .expect("the chained conclusion is about another individual");
    assert!(report.root_proved);

    let error = check(&env, &gated_step("r李四"))
        .expect_err("the chain must propagate 中间 李四 to 无辜 李四");
    assert_eq!(error.node, Some(1), "{error}");
    assert!(error.message.contains("无法确认阻断状态"), "{error}");
}

/// A pattern nested inside a premise argument is matched and binds only the
/// argument it contains.
#[test]
fn opaque_nested_premise_reaches_the_blocker_argument() {
    let env = opaque_nested_argument_env();
    let report = check(&env, &gated_step("r张三"))
        .expect("a nested opaque conclusion about 李四 must not block 张三");
    assert!(report.root_proved);

    let error =
        check(&env, &gated_step("r李四")).expect_err("the nested premise must consume 中间 李四");
    assert_eq!(error.node, Some(1), "{error}");
    assert!(error.message.contains("无法确认阻断状态"), "{error}");
}

/// A parameter-headed premise (`?f 甲`) consumes the opaque conclusion.
#[test]
fn opaque_parameter_head_instantiates_the_conclusion() {
    let env = opaque_parameter_head_env();
    let error = check(&env, &gated_step("r张三"))
        .expect_err("a parameter-head premise must consume the opaque conclusion");
    assert_eq!(error.node, Some(1), "{error}");
    assert!(error.message.contains("无法确认阻断状态"), "{error}");

    let report =
        check(&env, &gated_step("r李四")).expect("the instantiated conclusion is about 张三 only");
    assert!(report.root_proved);
}

/// A function parameter applied in the opaque conclusion can denote any
/// proposition (`λ _. B`), so it is matched as a wildcard, not by binding the
/// function part of the blocker.
#[test]
fn opaque_applied_variable_conclusion_blocks_every_application() {
    let env = opaque_applied_variable_env();
    for rule in ["r二元", "r二元同参"] {
        let error = check(&env, &gated_step(rule))
            .expect_err("an applied function parameter must conservatively block any proposition");
        assert_eq!(error.node, Some(1), "{error}");
        assert!(error.message.contains("无法确认阻断状态"), "{error}");
    }
}

/// The same outer head with another argument or another nesting depth is not
/// polluted by a ground opaque conclusion.
#[test]
fn opaque_same_head_does_not_pollute_argument_or_nesting() {
    let env = opaque_same_head_structure_env();
    for rule in ["r另一参数", "r另一层"] {
        let report = check(&env, &gated_step(rule))
            .expect("another argument or nesting depth must not be blocked");
        assert!(report.root_proved);
    }

    let error =
        check(&env, &gated_step("r自身")).expect_err("the opaque conclusion itself must block");
    assert_eq!(error.node, Some(1), "{error}");
    assert!(error.message.contains("无法确认阻断状态"), "{error}");
}

/// An opaque conclusion and the blocker only differ by eta: the pattern match
/// is followed by kernel conversion, so the blocker is still rejected.
#[test]
fn opaque_eta_variant_of_the_conclusion_blocks() {
    let env = opaque_eta_conclusion_env();
    let error = check(&env, &gated_step("r"))
        .expect_err("an eta variant of the opaque conclusion must block");
    assert_eq!(error.node, Some(1), "{error}");
    assert!(error.message.contains("无法确认阻断状态"), "{error}");
}

/// Pattern propagation through an eta-expanded premise is done on short
/// normal forms on both sides; an eta difference must not hide the chain.
#[test]
fn opaque_eta_variant_propagates_through_a_premise() {
    let env = opaque_eta_propagation_env();
    let error = check(&env, &gated_step("r"))
        .expect_err("an eta-expanded premise must still consume the opaque conclusion");
    assert_eq!(error.node, Some(1), "{error}");
    assert!(error.message.contains("无法确认阻断状态"), "{error}");
}

/// A rule premise that applies a function parameter must not be matched
/// against a beta-reduced normal fact; the rule contributes its conclusion
/// schema instead, so the omitted blocker is still rejected.
#[test]
fn opaque_beta_premise_is_conservative() {
    let env = opaque_beta_premise_env();
    let error = check(&env, &gated_step("r"))
        .expect_err("a parameter application in a premise must not hide the blocker");
    assert_eq!(error.node, Some(1), "{error}");
    assert!(error.message.contains("无法确认阻断状态"), "{error}");
}

/// An opaque conclusion that applies a function parameter under a binder has
/// no first-order pattern: its instances may mention the bound variable.
/// The whole schema becomes a wildcard, so the blocker is still rejected.
#[test]
fn opaque_applied_variable_under_a_binder_is_conservative() {
    let env = opaque_bound_application_env();
    let error = check(&env, &gated_step("r"))
        .expect_err("a binder-dependent application instance must not be missed");
    assert_eq!(error.node, Some(1), "{error}");
    assert!(error.message.contains("无法确认阻断状态"), "{error}");
}

/// A step proving `Q x0` while `r` is gated by `P (λz.z)`. The environment's
/// rules A同 and Z常 conclude the identity lambda and the constant lambda
/// respectively; their printed forms collide when the binder is anonymous.
fn o_identity_certificate() -> Certificate {
    certificate(
        vec![premise(atom("Q", "x0"))],
        vec![
            assumption_node(0),
            rule_node_for("r", atom("Q", "x0"), vec![0], vec![("p", constant("x0"))]),
        ],
        Some(1),
    )
}

/// Pattern identity must distinguish `Var(0)` from a real constant named
/// `x0`. The two opaque schemas below print identically once binder names are
/// erased; a printed-key map would drop the identity schema and clear the step.
#[test]
fn pattern_key_distinguishes_a_bound_variable_from_a_constant() {
    let env = env_from(
        "cert-check-pattern-key-collision",
        r#"
sort 人
obj x0 : 人
pred Q : 人 → Prop
pred 佐证 : Q x0 → Prop
pred P : (人 → 人) → Prop

rule A同 :
  premise h : Q x0
  unless 佐证 h
  conclude P (λ (z : 人) := z)
  source text "测试" locator "夹具"

rule Z常 :
  premise h : Q x0
  unless 佐证 h
  conclude P (λ (z : 人) := x0)
  source text "测试" locator "夹具"

rule r :
  params p : 人
  premise Q p
  conclude Q p
  unless P (λ (z : 人) := z)
  source text "测试" locator "夹具"
"#,
    );
    let error = check(&env, &o_identity_certificate())
        .expect_err("the identity schema must survive the constant schema with the same print");
    assert_eq!(error.node, Some(1), "{error}");
    assert!(error.message.contains("无法确认阻断状态"), "{error}");
    assert!(error.message.contains("P"), "{error}");
}

/// A pattern can double in every propagation round without increasing the
/// pattern count. The per-term node bound must stop it with an error instead
/// of letting the process grow the term until memory runs out.
#[test]
fn growing_pattern_hits_the_term_size_bound() {
    let env = env_from(
        "cert-check-growing-pattern",
        r#"
sort 人
obj 甲 : 人
pred Q : 人 → Prop
pred P : 人 → Prop
pred F : 人 → 人 → 人
pred 佐证 : Q 甲 → Prop

rule 依赖 :
  premise h : Q 甲
  unless 佐证 h
  conclude P 甲
  source text "测试" locator "夹具"

rule 生长 :
  params x : 人
  premise P x
  conclude P (F x x)
  source text "测试" locator "夹具"

rule r :
  params p : 人
  premise Q p
  conclude Q p
  unless P 甲
  source text "测试" locator "夹具"
"#,
    );
    let cert = certificate(
        vec![premise(atom("Q", "甲"))],
        vec![
            assumption_node(0),
            rule_node_for("r", atom("Q", "甲"), vec![0], vec![("p", constant("甲"))]),
        ],
        Some(1),
    );
    let error = check(&env, &cert).expect_err("a doubling pattern must hit the size bound");
    assert!(error.message.contains("节点上限"), "{error}");
}

/// Fact identity has the same collision: `def 我 := x0` and a binder named
/// `x0` print the same, but one body is a constant and the other a bound
/// variable. The identity fact must remain visible to the blocker check.
#[test]
fn fact_key_distinguishes_a_bound_variable_from_a_constant() {
    let env = env_from(
        "cert-check-fact-key-collision",
        r#"
sort 人
obj x0 : 人
def 我 : 人 := x0
pred Q : 人 → Prop
pred P : (人 → 人) → Prop
axiom Q事实 : Q x0
  source text "测试" locator "夹具"

rule A常 :
  premise Q x0
  conclude P (λ (x0 : 人) := 我)
  source text "测试" locator "夹具"

rule Z同 :
  premise Q x0
  conclude P (λ (x0 : 人) := x0)
  source text "测试" locator "夹具"

rule r :
  params p : 人
  premise Q p
  conclude Q p
  unless P (λ (x0 : 人) := x0)
  source text "测试" locator "夹具"
"#,
    );
    let error = check(&env, &o_identity_certificate())
        .expect_err("the identity fact must survive the constant fact with the same print");
    assert_eq!(error.node, Some(1), "{error}");
    assert!(
        error.message.contains("可能由环境规则推出") || error.message.contains("阻断条件"),
        "{error}"
    );
    assert!(error.message.contains("P"), "{error}");
}
