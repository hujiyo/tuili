//! The environment: the declaration ledger and the local context.
//!
//! The environment is an append-only ledger. A name collision is an error,
//! never a silent overwrite, and every declaration *may* carry provenance.
//! A legal derivation is worthless without knowing which version of which
//! article it used, so provenance is a first-class field rather than a comment.

use std::collections::{BTreeMap, BTreeSet};

use crate::check;
use crate::error::{Error, Result};
use crate::meta::Scope;
use crate::term::{Expr, Name};

/// Where a declaration comes from.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct SourceRef {
    /// The file or law name, for example `中华人民共和国宪法`.
    pub text: String,
    /// The article or section within `text`, for example `第三十九条`.
    pub locator: String,
    pub version: String,
    pub effective: Option<String>,
    /// Why we formalised the article this way, when that is not obvious.
    pub note: String,
    /// The quoted wording of the provision. `text` is the instrument name;
    /// this is the article's text.
    pub quote: String,
    pub url: String,
    pub jurisdiction: String,
    pub retrieved_at: String,
    pub hash: String,
}

impl SourceRef {
    pub fn new(text: impl Into<String>, locator: impl Into<String>) -> Self {
        SourceRef {
            text: text.into(),
            locator: locator.into(),
            ..Default::default()
        }
    }
    pub fn with_version(mut self, v: impl Into<String>) -> Self {
        self.version = v.into();
        self
    }
    pub fn with_effective(mut self, v: impl Into<String>) -> Self {
        self.effective = Some(v.into());
        self
    }
    pub fn with_quote(mut self, v: impl Into<String>) -> Self {
        self.quote = v.into();
        self
    }
    pub fn with_url(mut self, v: impl Into<String>) -> Self {
        self.url = v.into();
        self
    }
    pub fn with_jurisdiction(mut self, v: impl Into<String>) -> Self {
        self.jurisdiction = v.into();
        self
    }
    pub fn with_retrieved_at(mut self, v: impl Into<String>) -> Self {
        self.retrieved_at = v.into();
        self
    }
    pub fn with_hash(mut self, v: impl Into<String>) -> Self {
        self.hash = v.into();
        self
    }
    /// The citation in one line: `「<text><locator>」`, followed by
    /// `（<version>）` when a version is recorded. Control characters are
    /// escaped, so the result is always exactly one line.
    pub fn one_line(&self) -> String {
        let mut s = format!(
            "「{}{}」",
            escape_control(&self.text),
            escape_control(&self.locator)
        );
        if !self.version.is_empty() {
            s.push_str(&format!("（{}）", escape_control(&self.version)));
        }
        s
    }

    /// Every non-empty field on its own line, with control characters
    /// escaped. Empty optional fields are omitted rather than printed blank.
    pub fn full(&self) -> String {
        let mut lines = Vec::new();
        for (label, value) in [
            ("文本", self.text.as_str()),
            ("条号", self.locator.as_str()),
            ("版本", self.version.as_str()),
            ("生效", self.effective.as_deref().unwrap_or("")),
            ("引文", self.quote.as_str()),
            ("链接", self.url.as_str()),
            ("管辖", self.jurisdiction.as_str()),
            ("抓取时间", self.retrieved_at.as_str()),
            ("哈希", self.hash.as_str()),
            ("备注", self.note.as_str()),
        ] {
            if !value.is_empty() {
                lines.push(format!("{label}：{}", escape_control(value)));
            }
        }
        lines.join("\n")
    }
}

/// Escape control and invisible formatting characters so an external value
/// cannot inject another output line, a terminal control sequence or a
/// bidirectional display override. Newline, carriage return and tab get their
/// short forms; a literal backslash is doubled; every control or formatting
/// character becomes `\u{XXXX}`.
pub fn escape_control(value: &str) -> String {
    let mut escaped = String::with_capacity(value.len());
    for ch in value.chars() {
        match ch {
            '\n' => escaped.push_str("\\n"),
            '\r' => escaped.push_str("\\r"),
            '\t' => escaped.push_str("\\t"),
            '\\' => escaped.push_str("\\\\"),
            ch if ch.is_control()
                || matches!(
                    ch,
                    '\u{061C}'
                        | '\u{180E}'
                        | '\u{200B}'..='\u{200F}'
                        | '\u{2028}'
                        | '\u{2029}'
                        | '\u{202A}'..='\u{202E}'
                        | '\u{2060}'..='\u{206F}'
                        | '\u{FEFF}'
                ) =>
            {
                escaped.push_str(&format!("\\u{{{:04X}}}", ch as u32));
            }
            ch => escaped.push(ch),
        }
    }
    escaped
}

/// Who asserts a fact.
///
/// The identity is part of the evidence: "the court found it" and "the user
/// says so" are different claims even when the proposition is the same, and the
/// difference decides conflicts. A strict identity (`verified` / `stipulated`)
/// outranks a defeasible conclusion; a claim (`user_asserted` / `assumed`) may
/// seed a derivation and block an `unless`, but it never automatically beats a
/// rule conclusion. A `disputed` fact asserts what the other side claims and is
/// not used as a premise at all.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FactIdentity {
    /// Found by a court or stated in an official document.
    Verified,
    /// Stated by the user.
    UserAsserted,
    /// Assumed for the sake of the analysis.
    Assumed,
    /// Disputed by the other side.
    Disputed,
    /// Agreed by both sides.
    Stipulated,
}

impl FactIdentity {
    /// The keyword written after `identity`.
    pub fn keyword(self) -> &'static str {
        match self {
            FactIdentity::Verified => "verified",
            FactIdentity::UserAsserted => "user_asserted",
            FactIdentity::Assumed => "assumed",
            FactIdentity::Disputed => "disputed",
            FactIdentity::Stipulated => "stipulated",
        }
    }

    /// The identity named by a keyword, or `None` for an unknown keyword.
    pub fn from_keyword(s: &str) -> Option<Self> {
        match s {
            "verified" => Some(FactIdentity::Verified),
            "user_asserted" => Some(FactIdentity::UserAsserted),
            "assumed" => Some(FactIdentity::Assumed),
            "disputed" => Some(FactIdentity::Disputed),
            "stipulated" => Some(FactIdentity::Stipulated),
            _ => None,
        }
    }

    /// The Chinese label shown by `:inspect` and `:fact`.
    pub fn label_zh(self) -> &'static str {
        match self {
            FactIdentity::Verified => "法院查明",
            FactIdentity::UserAsserted => "用户陈述",
            FactIdentity::Assumed => "分析假设",
            FactIdentity::Disputed => "对方争议",
            FactIdentity::Stipulated => "双方无争议",
        }
    }

    /// Whether this identity is a strict fact.
    ///
    /// Strictness decides conflicts: a strict fact outranks a defeasible
    /// conclusion and a claim, while a claim never automatically outranks a
    /// rule conclusion, and two strict facts have no order between them.
    pub fn is_strict(self) -> bool {
        matches!(self, FactIdentity::Verified | FactIdentity::Stipulated)
    }

    /// Whether a fact with this identity seeds a derivation.
    ///
    /// A disputed fact asserts what the other side claims, not what is the
    /// case, so it must not be used as a premise. Every other identity is a
    /// claim the fact base can derive from for now.
    pub fn seeds_derivation(self) -> bool {
        !matches!(self, FactIdentity::Disputed)
    }
}

/// The theme risk categories a predicate can be declared under.
///
/// A `risk <类别> <谓词>` declaration records that reasoning about this
/// predicate's propositions belongs to one of these themes. It is a declared
/// property of the theory, not a word list the system matches against printed
/// text: the surface declaration names the category, `:inspect` shows it and the
/// certificate layer compares predicate heads with it. The kernel only stores
/// the marker; it never seeds a derivation, blocks a rule or changes a verdict.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum RiskTheme {
    /// `刑事` — criminal liability and criminal procedure.
    Criminal,
    /// `人身安全` — personal safety, bodily integrity and personal liberty.
    PersonalSafety,
    /// `重大财产` — major property interests and large-value assets.
    MajorProperty,
    /// `临近期限` — a deadline or limitation period that is about to run out.
    ApproachingDeadline,
    /// `涉外或移民` — foreign elements, immigration and cross-border matters.
    ForeignOrImmigration,
}

impl RiskTheme {
    /// The keywords a `risk` declaration accepts, in a stable order. Error
    /// messages list the same set so a near miss can be corrected.
    pub fn keywords() -> &'static [&'static str] {
        &["刑事", "人身安全", "重大财产", "临近期限", "涉外或移民"]
    }

    /// The theme named by its keyword, or `None` when the keyword is unknown.
    /// There is no default: an unknown theme is a load error.
    pub fn parse(keyword: &str) -> Option<Self> {
        match keyword {
            "刑事" => Some(RiskTheme::Criminal),
            "人身安全" => Some(RiskTheme::PersonalSafety),
            "重大财产" => Some(RiskTheme::MajorProperty),
            "临近期限" => Some(RiskTheme::ApproachingDeadline),
            "涉外或移民" => Some(RiskTheme::ForeignOrImmigration),
            _ => None,
        }
    }

    /// The surface keyword, which is also what `:inspect` prints next to the
    /// predicate and what the risk report names.
    pub fn keyword(self) -> &'static str {
        match self {
            RiskTheme::Criminal => "刑事",
            RiskTheme::PersonalSafety => "人身安全",
            RiskTheme::MajorProperty => "重大财产",
            RiskTheme::ApproachingDeadline => "临近期限",
            RiskTheme::ForeignOrImmigration => "涉外或移民",
        }
    }

    /// The theme's own name, as the risk report prints it.
    pub fn label_zh(self) -> &'static str {
        self.keyword()
    }
}

/// Who must prove a rule's positive requirements, or its exceptions.
///
/// The three values are relative roles, not party names: a file never invents
/// a name like "张三" to say who bears the burden. `court` covers a burden the
/// court discharges on its own authority.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Burden {
    /// The party asserting the claim (`主张方`).
    Claimant,
    /// The opposing party (`相对方`).
    Respondent,
    /// The court, of its own motion (`法院职权`).
    Court,
}

impl Burden {
    /// The keyword written after `burden` / `exception_burden`, which is also
    /// what `:inspect` prints.
    pub fn label(self) -> &'static str {
        match self {
            Burden::Claimant => "claimant",
            Burden::Respondent => "respondent",
            Burden::Court => "court",
        }
    }

    /// The Chinese role name shown by the burden report. These are relative
    /// roles, not party names: the report never invents a person.
    pub fn label_zh(self) -> &'static str {
        match self {
            Burden::Claimant => "主张方",
            Burden::Respondent => "相对方",
            Burden::Court => "法院职权",
        }
    }

    /// The role as the actor of the report's plain-language sentence:
    /// `主张方提出`, `相对方提出`, `法院依职权查明`. `court` is not a
    /// person, so the sentence names the court's own inquiry instead of
    /// saying that the role "presents" evidence.
    pub fn actor_zh(self) -> &'static str {
        match self {
            Burden::Claimant => "主张方提出",
            Burden::Respondent => "相对方提出",
            Burden::Court => "法院依职权查明",
        }
    }

    /// The values the clause accepts, in a stable order. Error messages list
    /// the same set, so a near miss can be corrected from the diagnostic.
    pub fn labels() -> &'static [&'static str] {
        &["claimant", "respondent", "court"]
    }

    /// The burden named by a keyword, or `None` when the keyword is unknown.
    /// There is no default: an unknown value is an error, never a fallback.
    pub fn parse(keyword: &str) -> Option<Self> {
        match keyword {
            "claimant" => Some(Burden::Claimant),
            "respondent" => Some(Burden::Respondent),
            "court" => Some(Burden::Court),
            _ => None,
        }
    }
}

/// The standard of proof required for a rule's positive requirements, or for
/// its exceptions. The values are labels, not probabilities: the system does
/// not assign numbers to them.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Standard {
    /// `preponderance` — the balance of probabilities.
    Preponderance,
    /// `clear_and_convincing`.
    ClearAndConvincing,
    /// `beyond_reasonable_doubt`.
    BeyondReasonableDoubt,
}

impl Standard {
    /// The keyword written after `standard` / `exception_standard`.
    pub fn label(self) -> &'static str {
        match self {
            Standard::Preponderance => "preponderance",
            Standard::ClearAndConvincing => "clear_and_convincing",
            Standard::BeyondReasonableDoubt => "beyond_reasonable_doubt",
        }
    }

    /// The Chinese label shown by the burden report. It names the standard of
    /// proof and nothing more: no probability or score is attached.
    pub fn label_zh(self) -> &'static str {
        match self {
            Standard::Preponderance => "优势证据",
            Standard::ClearAndConvincing => "清楚可信",
            Standard::BeyondReasonableDoubt => "排除合理怀疑",
        }
    }

    /// The values the clause accepts, in a stable order.
    pub fn labels() -> &'static [&'static str] {
        &[
            "preponderance",
            "clear_and_convincing",
            "beyond_reasonable_doubt",
        ]
    }

    /// The standard named by a keyword, or `None` when the keyword is unknown.
    /// There is no default: an unknown value is an error, never a fallback.
    pub fn parse(keyword: &str) -> Option<Self> {
        match keyword {
            "preponderance" => Some(Standard::Preponderance),
            "clear_and_convincing" => Some(Standard::ClearAndConvincing),
            "beyond_reasonable_doubt" => Some(Standard::BeyondReasonableDoubt),
            _ => None,
        }
    }
}

/// The burden and standard a rule declares for one group of propositions.
///
/// `None` is a real answer: the file declared nothing, so every report spells
/// out `未声明举证责任` / `未声明证明标准` instead of naming a default party or
/// standard. The standard is a label only; nothing here is a probability.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct ProofBurden {
    /// Who must prove the group, or `None` when undeclared.
    pub burden: Option<Burden>,
    /// The standard of proof for the group, or `None` when undeclared.
    pub standard: Option<Standard>,
}

impl ProofBurden {
    /// The burden and standard the rule declares for its positive premises.
    pub fn requirements(rule: &RuleDecl) -> Self {
        ProofBurden {
            burden: rule.burden,
            standard: rule.standard,
        }
    }

    /// The burden and standard the rule declares for its `unless` exceptions.
    pub fn exceptions(rule: &RuleDecl) -> Self {
        ProofBurden {
            burden: rule.exception_burden,
            standard: rule.exception_standard,
        }
    }

    /// The declared values as report text, in the fixed order
    /// `(举证方, 证明标准)`. An undeclared value is written out; it is never
    /// replaced by a default role or standard.
    pub fn labels_zh(self) -> (&'static str, &'static str) {
        (
            match self.burden {
                Some(burden) => burden.label_zh(),
                None => "未声明举证责任",
            },
            match self.standard {
                Some(standard) => standard.label_zh(),
                None => "未声明证明标准",
            },
        )
    }

    /// The one-line pair the gap tree prints in brackets:
    /// `主张方 / 优势证据`, `主张方 / 未声明证明标准`,
    /// `未声明举证责任 / 优势证据` or `未声明举证责任 / 未声明证明标准`.
    pub fn pair_zh(self) -> String {
        let (burden, standard) = self.labels_zh();
        format!("{burden} / {standard}")
    }

    /// The plain-language sentence the narrative prints. `exceptions` selects
    /// the exception group's wording; the values are the same ones
    /// [`ProofBurden::pair_zh`] writes, so the two reports cannot disagree.
    pub fn sentence_zh(self, exceptions: bool) -> String {
        let (burden, standard) = self.labels_zh();
        let actor = match self.burden {
            Some(burden) => burden.actor_zh(),
            None => burden,
        };
        let subject = if exceptions { "例外" } else { "这条证据" };
        match (self.burden, self.standard) {
            (Some(_), Some(_)) => format!("{subject}由{actor}，标准是{standard}"),
            (Some(_), None) => format!("{subject}由{actor}，但{standard}"),
            (None, Some(_)) => format!("{subject}{burden}，标准是{standard}"),
            (None, None) => format!("{subject}{burden}，{standard}"),
        }
    }
}

/// The two burden reports a rule can declare: its positive requirements and
/// its `unless` exceptions. They are independent; a group is never filled in
/// from the other.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct RulePleading {
    pub requirements: ProofBurden,
    pub exceptions: ProofBurden,
}

impl RulePleading {
    /// Read both groups from a rule's declaration, keeping an undeclared field
    /// as `None`.
    pub fn of_rule(rule: &RuleDecl) -> Self {
        RulePleading {
            requirements: ProofBurden::requirements(rule),
            exceptions: ProofBurden::exceptions(rule),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum DeclKind {
    /// A new sort: `sort 公民`.
    Sort,
    /// A predicate symbol: `pred 侵害 : 公民 → 行为 → Prop`.
    Pred,
    /// A constant whose declared type is not a proposition: `axiom 假 : Prop`,
    /// `axiom 恶意 : 人 → Prop`. It names a concept and asserts nothing.
    Axiom,
    /// An asserted proposition together with who asserts it:
    /// `axiom 侵占事实 : 侵占 张三`, followed on its own line by
    /// `identity verified`. The declared type must be a proposition
    /// (`Sort 0`); a claim about who asserts it belongs with the claim
    /// itself, not with the type.
    Fact { identity: FactIdentity },
    /// An individual constant: `obj 张三 : 公民`.
    Obj,
    /// `def ... := ...`; unfolds during conversion.
    Def { body: Expr },
    /// A rule; opaque under conversion, driving the reasoner instead.
    Rule(Box<RuleDecl>),
    /// A marked interpretation: it turns a premise into another premise. The
    /// declaration is opaque under conversion; the reasoner applies it only
    /// when the query explicitly enables it, and a certificate records the
    /// application step and its declaration. The kernel itself never applies
    /// it or interprets its direction.
    Interpretation(Box<Interpretation>),
    /// Two predicates whose facts cannot both hold: any pair with these heads
    /// and identical arguments is a conflict. Declared, never guessed, because
    /// a legal system cannot read Chinese and decide on its own that 「该批准」
    /// and 「不该批准」 are opposites.
    Contrary { left: Name, right: Name },
    /// A predicate that can hold of only one value at argument `index`
    /// (zero-based): two facts with the same head that differ at `index` and
    /// agree everywhere else are a conflict. `unique 应适用 1` says one case
    /// can have only one applicable norm.
    Unique { pred: Name, index: usize },
    /// A provenance-carrying priority between two rules: `winner` outranks
    /// `loser`. `declared_in` is the namespace of the module that asserted
    /// the relation, because who claims the priority is part of the claim.
    Priority {
        winner: Name,
        loser: Name,
        declared_in: Name,
    },
    /// A predicate marked as an open concept: `open 重大`. The marker records
    /// that applying the concept (「重大」「合理」「善意」「情节严重」) needs a
    /// human judgement; it asserts nothing itself. The declaration is metadata:
    /// it seeds no derivation and blocks no `unless`. Consumers outside the
    /// kernel read it through [`Env::open_predicates`]: `:inspect` shows the
    /// marker, and a certificate records an `open_concept` obligation when a
    /// derivation depends on it.
    OpenConcept { pred: Name },
    /// A predicate marked as belonging to a risk theme:
    /// `risk 刑事 故意伤害`. The marker records that reasoning about this
    /// predicate's propositions is about that theme, so the CLI can warn about
    /// the case and `:labels` can name it as a second label. It is metadata:
    /// it asserts nothing, seeds no derivation and blocks no `unless`. The
    /// risk is never guessed from printed text: a predicate is only risky
    /// because a declaration says so, and `:inspect` shows the marker.
    Risk { theme: RiskTheme, pred: Name },
}

/// The largest number of branches one disjunctive premise may write.
///
/// The bound is a declaration-time constant, not a caller option: a 析取前提
/// with more branches than this is refused when the theory is loaded, so the
/// reasoner's branch enumeration has a fixed auditable ceiling.
pub const MAX_OR_BRANCHES: usize = 8;

/// One premise of a rule: a plain proposition, a disjunction of propositions,
/// or an existential proposition with one explicitly named witness binder.
///
/// A rule's premises are still conjoined with one another: multiple `premise`
/// lines of a rule are all required. Inside one premise, `P or Q` means at
/// least one of the branches must be proved; `exists x : T, P x` means some
/// concrete declared individual of type `T` must make `P x` true.
///
/// The kernel represents both compound forms by their impredicative encoding
/// (see [`or_type`] and [`exists_type`]), so a rule's declared type stays a
/// plain telescope and the kernel can check a step's proof term after the
/// certificate has recorded which branch / witness was used. The declaration
/// keeps the surface structure because the reasoner and the certificate checker
/// must know exactly which branches and which witness binder exist.
#[derive(Debug, Clone, PartialEq)]
pub struct PremiseDecl {
    /// The optional binder name; unnamed premises get `_p{i}`.
    pub name: Option<Name>,
    pub kind: PremiseKind,
}

/// The form of one rule premise.
#[derive(Debug, Clone, PartialEq)]
pub enum PremiseKind {
    /// A single proposition, as before.
    Plain(Expr),
    /// `P or Q [or R …]`: at least one branch, tried in written order.
    Or(Vec<Expr>),
    /// `exists x : T, P x`: `body` is written in the context of the telescope
    /// extended by the witness binder `binder`, exactly like a `Pi` codomain.
    Exists {
        binder: Name,
        domain: Expr,
        body: Expr,
    },
}

impl PremiseDecl {
    /// A plain premise with its optional surface name.
    pub fn plain(name: Option<Name>, ty: Expr) -> Self {
        PremiseDecl {
            name,
            kind: PremiseKind::Plain(ty),
        }
    }

    /// The binder name this premise contributes to the rule telescope.
    pub fn binder_or(&self, index: usize) -> Name {
        self.name
            .clone()
            .unwrap_or_else(|| crate::term::name(format!("_p{index}")))
    }

    /// The kernel type of this premise, written in the rule telescope prefix.
    ///
    /// Plain premises keep their written type. Compound premises use the
    /// impredicative encoding so the kernel can check the branch/witness
    /// introduction term as an ordinary proof.
    pub fn kernel_type(&self) -> Expr {
        match &self.kind {
            PremiseKind::Plain(ty) => ty.clone(),
            PremiseKind::Or(branches) => or_type(branches),
            PremiseKind::Exists { domain, body, .. } => exists_type(domain, body),
        }
    }
}

/// The impredicative encoding of `P or Q`: `∀ C : Prop, (P → C) → (Q → C) → C`.
///
/// The branches are written in the rule telescope prefix, so they are shifted
/// under the encoding's own binders exactly as a `Pi` codomain would be.
pub fn or_type(branches: &[Expr]) -> Expr {
    Expr::pi(Expr::Sort(0), or_arms(branches, 0))
}

fn or_arms(branches: &[Expr], index: usize) -> Expr {
    if index == branches.len() {
        // `C` is the outermost binder; after `index` arrow binders its de
        // Bruijn index is `index`.
        return Expr::var(index);
    }
    // `B → C`: the branch is placed under `C` and the earlier arrow binders,
    // and `C` itself sits outside the arrow binder, so its index inside the
    // arrow codomain is `index + 1`.
    let arrow = Expr::pi(
        crate::term::shift(&branches[index], (index as isize) + 1, 0),
        Expr::var(index + 1),
    );
    Expr::pi(arrow, or_arms(branches, index + 1))
}

/// The impredicative encoding of `exists x : T, P x`:
/// `∀ C : Prop, (∀ x : T, P x → C) → C`.
///
/// `domain` lives in the telescope prefix; `body` is written in the prefix
/// extended by the witness binder (so its `Var(0)` is that binder), exactly as
/// a `Pi` codomain is.
pub fn exists_type(domain: &Expr, body: &Expr) -> Expr {
    // Inside `C`: `Prop`. `Pi (x : T) (P x → C)`; the inner arrow introduces a
    // proof binder, so `C` has index 2 inside it (C, x, proof).
    let witness = Expr::pi(
        crate::term::shift(domain, 1, 0),
        Expr::pi(crate::term::shift(body, 1, 1), Expr::var(2)),
    );
    Expr::pi(Expr::Sort(0), Expr::pi(witness, Expr::var(1)))
}

/// One premise opened into the reasoner's pattern language.
///
/// Every rule-telescope binder becomes a `?name` constant. For an existential
/// premise the witness binder is a *local* `?name` constant: it is not a
/// telescope binder, so it cannot be used by later premises or the conclusion,
/// and it is recorded separately in the certificate's witness choice.
#[derive(Debug, Clone, PartialEq)]
pub enum OpenPremise {
    Plain(Expr),
    Or(Vec<Expr>),
    Exists {
        binder: Name,
        domain: Expr,
        body: Expr,
    },
}

/// A defeasible rule.
#[derive(Debug, Clone, PartialEq)]
pub struct RuleDecl {
    pub params: Vec<(Name, Expr)>,
    /// The rule's premises, conjoined with one another. A plain premise is one
    /// proposition; a disjunctive or existential premise is one premise with an
    /// internal choice (see [`PremiseDecl`]).
    pub premises: Vec<PremiseDecl>,
    pub conclusion: Expr,
    /// Conditions whose truth *blocks* the rule (the `unless` clauses).
    /// These are part of the telescope, so they may mention any parameter.
    pub unlesses: Vec<Expr>,
    /// Instance conditions that must *hold* for the rule to fire (the `guard`
    /// clauses), in declaration order.
    ///
    /// Each guard is a comparison (`less` or `le`) over the rule's parameters
    /// and, unlike an `unless`, it is not a proposition a fact could prove: it
    /// is evaluated arithmetically against the values the instance binds. All
    /// guards of one instance are conjunctive — every one of them must
    /// evaluate to `true`, and a `false` guard leaves the instance unfired.
    /// A guard must not mention a premise binder (those bind proofs, not
    /// values) and must not contain an unbound name; the loader refuses both.
    /// Guards are *not* binders, so the telescope and the rule's declared type
    /// are unchanged.
    pub guards: Vec<Expr>,
    /// Who must prove the rule's positive requirements (`burden …`), or
    /// `None` when the file declared no burden. An undeclared burden is not
    /// defaulted to the claimant and is not used by reasoning: the gap report
    /// reads it from the declaration (see [`RulePleading`]), and the calculus
    /// never does.
    pub burden: Option<Burden>,
    /// The standard for those requirements (`standard …`), or `None` when
    /// undeclared. Not defaulted to `preponderance`.
    pub standard: Option<Standard>,
    /// Who must prove the rule's exceptions (`exception_burden …`), i.e.
    /// every `unless` of this rule, or `None` when undeclared.
    pub exception_burden: Option<Burden>,
    /// The standard for those exceptions (`exception_standard …`), or `None`
    /// when undeclared.
    pub exception_standard: Option<Standard>,
    /// Rules that defeat this one.
    pub exceptions: Vec<Name>,
    /// Rules this one outranks, declared with `prefer R`. The reverse of
    /// `exceptions`, kept separately so the source of a priority is visible:
    /// `defeated_by` means "I lose to X", `prefer` means "I beat Y".
    pub prefers: Vec<Name>,
    /// The historical-version group this rule belongs to, written as
    /// `revision <id>`; `None` when the rule declared none.
    ///
    /// Rules that carry the same identifier under the same scope (a module
    /// namespace or, for a case file, the file's load identity) are versions of
    /// one provision ([`crate::meta::RevisionGroup`]). The reasoner never picks
    /// one of them: which version applies to an instance is the applicability
    /// judgement from the declared effective range, and which version wins a
    /// conflict is an explicitly declared priority. The field exists so reports
    /// can say that two rules are old and new versions of the same provision,
    /// and so the loader can require a group to have at least two versions.
    pub revision: Option<crate::meta::RevisionGroup>,
    pub sources: Vec<SourceRef>,
    /// Namespace of the module that declared the rule; `None` for a rule in a
    /// case file (a file without a namespace). Rule-internal `defeated_by` /
    /// `prefer` clauses may only order rules of the same namespace; a
    /// cross-package order is a [`DeclKind::Priority`] of its own.
    pub declared_in: Option<Name>,
}

/// A priority declared by a module: `priority winner over loser source …`.
///
/// The declaration's namespace travels with the relation because a priority
/// is asserted by a package about rules: who claims it is part of the claim.
#[derive(Debug, Clone, PartialEq)]
pub struct PriorityDecl {
    /// The synthetic ledger name of the declaration.
    pub name: Name,
    pub winner: Name,
    pub loser: Name,
    /// The namespace of the declaring module.
    pub declared_in: Name,
    pub sources: Vec<SourceRef>,
}

/// How an interpretation moves between the two propositions it relates.
///
/// The direction is declared data, not an inferred property: a legal
/// interpretation is a choice someone makes and must be able to audit. The
/// reasoner never derives behaviour from it; it is stored and copied into
/// `:inspect` and certificates.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum InterpretationDirection {
    /// The words are applied as written.
    Literal,
    /// The proposition is read more broadly than its wording.
    Expand,
    /// The proposition is read more narrowly than its wording.
    Narrow,
    /// The proposition is carried over to a similar case.
    Analogy,
}

impl InterpretationDirection {
    /// The surface keyword, or `None` for an unknown word.
    pub fn from_keyword(keyword: &str) -> Option<Self> {
        match keyword {
            "literal" => Some(Self::Literal),
            "expand" => Some(Self::Expand),
            "narrow" => Some(Self::Narrow),
            "analogy" => Some(Self::Analogy),
            _ => None,
        }
    }

    /// The canonical surface keyword, as `:inspect` prints it.
    pub fn keyword(self) -> &'static str {
        match self {
            Self::Literal => "literal",
            Self::Expand => "expand",
            Self::Narrow => "narrow",
            Self::Analogy => "analogy",
        }
    }
}

/// An interpretation before/after pair, with an explicit identity.
///
/// The point of making this a named object is auditability: a derivation can
/// cite which interpretation it applied, and another can cite a competing one.
#[derive(Debug, Clone, PartialEq)]
pub struct Interpretation {
    pub name: Name,
    pub from: Expr,
    pub to: Expr,
    /// The declared direction. It is declared data, not an inference: the
    /// reasoner applies the permission, while inspection and certificates
    /// copy the keyword verbatim.
    pub direction: InterpretationDirection,
    pub sources: Vec<SourceRef>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Decl {
    pub name: Name,
    pub kind: DeclKind,
    /// Declared type. For `Rule`, the telescope over params and premises
    /// ending in the conclusion, so the constant can be applied to its
    /// arguments to prove that conclusion.
    pub ty: Expr,
    pub sources: Vec<SourceRef>,
    /// Effective range and jurisdiction/territory recorded for the
    /// declaration. Rules may carry one; every other kind records
    /// [`Scope::default`]. The kernel stores the values and never filters on
    /// them: applicability is a later judgement.
    pub scope: Scope,
    /// First day the fact occurred (inclusive), `YYYY-MM-DD`. Only a
    /// [`DeclKind::Fact`] may carry one; the field is independent of any
    /// query date and is never defaulted from one.
    pub occurred_at: Option<String>,
    /// Jurisdiction or territory code of where the fact occurred. Only a
    /// [`DeclKind::Fact`] may carry one.
    pub occurred_in: Option<String>,
    /// Position in the ledger, assigned on insertion.
    pub index: u64,
}

/// The local context: a telescope. Each stored type is written in its own
/// prefix context, so a variable's type from depth `n` is lifted by `i`.
#[derive(Debug, Clone, Default)]
pub struct Ctx {
    bindings: Vec<(Option<Name>, Expr)>,
}

impl Ctx {
    pub fn new() -> Self {
        Ctx::default()
    }
    pub fn len(&self) -> usize {
        self.bindings.len()
    }
    pub fn is_empty(&self) -> bool {
        self.bindings.is_empty()
    }
    pub fn push(&mut self, n: Option<Name>, ty: Expr) {
        self.bindings.push((n, ty));
    }
    pub fn type_of(&self, i: usize) -> Result<Expr> {
        let n = self.bindings.len();
        if i >= n {
            return Err(Error::OutOfScope { index: i, bound: n });
        }
        let (_, ty) = &self.bindings[n - 1 - i];
        Ok(crate::term::shift(ty, i as isize, 0))
    }
    pub fn names(&self) -> impl Iterator<Item = &Option<Name>> {
        self.bindings.iter().map(|(n, _)| n)
    }
}

/// The declaration store.
#[derive(Debug, Clone, Default)]
pub struct Env {
    decls: BTreeMap<Name, Decl>,
    order: Vec<Name>,
    next_index: u64,
}

impl Env {
    pub fn new() -> Self {
        Env::default()
    }
    pub fn get(&self, n: &str) -> Option<&Decl> {
        self.decls.get(n)
    }
    pub fn contains(&self, n: &str) -> bool {
        self.decls.contains_key(n)
    }
    pub fn iter(&self) -> impl Iterator<Item = &Decl> {
        self.order.iter().filter_map(|n| self.decls.get(n))
    }
    pub fn decls_ordered(&self) -> &[Name] {
        &self.order
    }
    pub fn len(&self) -> usize {
        self.decls.len()
    }
    pub fn is_empty(&self) -> bool {
        self.decls.is_empty()
    }

    /// Add a declaration. The type is checked to live in a sort, so a typo
    /// in a predicate signature cannot enter the ledger.
    ///
    /// The declared type also decides which kind is admissible: a `Pred` is an
    /// atomic proposition once applied, so its declared type must be a
    /// telescope ending in `Prop`; a `Fact` asserts a proposition, so its
    /// declared type must be one (`Sort 0`); an `Axiom` only names a constant,
    /// so its declared type must not be a proposition. Accepting any of these
    /// mismatches would put a function or a claim into the ledger under the
    /// wrong kind.
    pub fn insert(&mut self, mut decl: Decl, ctx: &Ctx) -> Result<Name> {
        if self.decls.contains_key(&decl.name) {
            return Err(Error::DuplicateName(decl.name.to_string()));
        }
        // A built-in name means exactly what the kernel's evaluator says it
        // means. Shadowing it would make a record of a computation impossible
        // to recheck, so the declaration is refused rather than silently
        // overriding it.
        if crate::builtin::is_reserved(&decl.name) {
            return Err(Error::other(format!(
                "`{}` 是内核内建名称（{}），不能声明：内建运算的语义由内核固定",
                decl.name,
                crate::builtin::NAMES.join(" / ")
            )));
        }
        let ty_ty = check::infer(self, ctx, &decl.ty)?;
        match &ty_ty {
            Expr::Sort(_) => {}
            other => return Err(Error::NotASort(other.clone())),
        }
        // `Sort 0` is `Prop`. Conversion, not syntax, decides whether the
        // declared type is a proposition, so this agrees with the language
        // loader, which checks the same property definitionally.
        let is_proposition = crate::conv::convertible(self, ctx, &ty_ty, &Expr::Sort(0))?;
        match &decl.kind {
            DeclKind::Pred => self.check_pred_shape(ctx, &decl.name, &decl.ty)?,
            DeclKind::Fact { .. } if !is_proposition => {
                return Err(Error::other(format!(
                    "`{}` 被声明为事实，但它的类型不是命题：事实的类型必须是命题",
                    decl.name
                )))
            }
            DeclKind::Axiom if is_proposition => {
                return Err(Error::other(format!(
                    "`{}` 的类型是命题：断言命题必须用事实（Fact）并给出身份",
                    decl.name
                )))
            }
            _ => {}
        }
        if let DeclKind::Def { body } = &decl.kind {
            check::check(self, ctx, body, &decl.ty)?;
        }
        if let DeclKind::Rule(rule) = &decl.kind {
            rule.check(self, &Expr::Sort(0))?;
        }
        // Exact integer arithmetic reaching a closed literal expression is
        // evaluated here, so a declaration that would overflow fails when it is
        // loaded instead of becoming a term the normalizer refuses later. The
        // evaluated form is discarded: declarations keep the term the source
        // wrote, and only rule instances record their computed conclusion.
        crate::norm::evaluate_arithmetic(self, &decl.ty).map_err(|error| {
            Error::other(format!("`{}` 的声明里整数运算失败：{error}", decl.name))
        })?;
        if let DeclKind::Def { body } = &decl.kind {
            crate::norm::evaluate_arithmetic(self, body).map_err(|error| {
                Error::other(format!("`{}` 的定义体里整数运算失败：{error}", decl.name))
            })?;
        }
        decl.index = self.next_index;
        self.next_index += 1;
        self.order.push(decl.name.clone());
        let name = decl.name.clone();
        self.decls.insert(name.clone(), decl);
        Ok(name)
    }

    /// A predicate's declared type must be a telescope ending in `Prop`, i.e.
    /// `Π Δ, Prop`. The telescope may be empty (a nullary predicate is a
    /// proposition constant), domains may be any types, and the codomain is
    /// compared up to definitional equality, so a `def` alias of a predicate
    /// type is accepted.
    ///
    /// A function type such as `人 → 人` is a `Def`, not a `Pred`: the
    /// reasoner treats a predicate constant as an atomic proposition, so a
    /// function type would make every such occurrence claim a false thing.
    fn check_pred_shape(&self, ctx: &Ctx, name: &Name, ty: &Expr) -> Result<()> {
        let mut inner = ctx.clone();
        let mut head = ty.clone();
        loop {
            head = crate::norm::whnf(self, &head)?;
            match head {
                Expr::Pi {
                    name: binder,
                    domain,
                    codomain,
                } => {
                    inner.push(binder, *domain);
                    head = *codomain;
                }
                other => {
                    if crate::conv::convertible(self, &inner, &other, &Expr::Sort(0))? {
                        return Ok(());
                    }
                    return Err(Error::other(format!(
                        "`{}` 被声明为谓词，但它的类型 `{}` 不以 Prop 结尾：\
                         谓词必须形如 Π Δ, Prop（例如 `人 → Prop`）；返回 sort 的函数请用 `def` \
                         声明，不可展开的函数常量请用 `axiom` 声明",
                        escape_control(name),
                        crate::pretty::print_normalized(self, ctx, ty)
                    )));
                }
            }
        }
    }

    pub fn rules(&self) -> Vec<&Decl> {
        self.iter()
            .filter(|d| matches!(d.kind, DeclKind::Rule(_)))
            .collect()
    }

    /// The revision group one rule declares, or `None` when the declaration is
    /// not a rule or declared no `revision` clause.
    ///
    /// The group carries its own scope (a module namespace, or a case file's
    /// load identity) and identifier; see [`crate::meta::RevisionGroup`].
    pub fn revision_group_of(&self, rule: &Name) -> Option<crate::meta::RevisionGroup> {
        let decl = self.get(rule)?;
        let DeclKind::Rule(declared) = &decl.kind else {
            return None;
        };
        declared.revision.clone()
    }

    /// Every declared revision group, each with its member rules in ledger
    /// order. Groups are returned sorted by their identity.
    ///
    /// This is a view of the declarations only: the kernel never chooses a
    /// version, and a group with fewer than two rules is still reported (the
    /// loader, not the kernel, refuses a one-rule group).
    pub fn revision_groups(&self) -> Vec<(crate::meta::RevisionGroup, Vec<Name>)> {
        let mut groups: std::collections::BTreeMap<crate::meta::RevisionGroup, Vec<Name>> =
            std::collections::BTreeMap::new();
        for decl in self.iter() {
            let DeclKind::Rule(rule) = &decl.kind else {
                continue;
            };
            let Some(revision) = &rule.revision else {
                continue;
            };
            groups
                .entry(revision.clone())
                .or_default()
                .push(decl.name.clone());
        }
        groups.into_iter().collect()
    }
    pub fn interpretations(&self) -> Vec<&Decl> {
        self.iter()
            .filter(|d| matches!(d.kind, DeclKind::Interpretation(_)))
            .collect()
    }

    /// The declared contrary pairs, as written. The relation is symmetric;
    /// the reasoner closes it.
    pub fn contrary_pairs(&self) -> Vec<(Name, Name)> {
        self.iter()
            .filter_map(|d| match &d.kind {
                DeclKind::Contrary { left, right } => Some((left.clone(), right.clone())),
                _ => None,
            })
            .collect()
    }

    /// Declared single-valued argument positions, as `(predicate, index)`.
    pub fn unique_positions(&self) -> Vec<(Name, usize)> {
        self.iter()
            .filter_map(|d| match &d.kind {
                DeclKind::Unique { pred, index } => Some((pred.clone(), *index)),
                _ => None,
            })
            .collect()
    }

    /// Predicates marked as open concepts, in declaration order.
    ///
    /// A marker is metadata about how a predicate should be read. The kernel
    /// stores it and never lets it seed a derivation or block a rule. Readers
    /// use this list: `:inspect` shows the marker next to the predicate, and the
    /// certificate layer compares predicate heads against it so a derivation
    /// that concludes an open concept records an `open_concept` obligation
    /// instead of being reported as an unconditional proof.
    pub fn open_predicates(&self) -> Vec<Name> {
        self.iter()
            .filter_map(|d| match &d.kind {
                DeclKind::OpenConcept { pred } => Some(pred.clone()),
                _ => None,
            })
            .collect()
    }

    /// Predicates marked with a risk theme, in declaration order, together
    /// with the theme they were declared under.
    ///
    /// A marker is metadata about what a predicate is about. The kernel stores
    /// it and never lets it seed a derivation or block a rule. Readers use this
    /// list: `:inspect` shows the marker next to the predicate, and the
    /// certificate layer compares predicate heads against it so a derivation
    /// about a risk theme is reported with an explicit warning instead of
    /// being presented as an ordinary conclusion. The mapping is a declared
    /// decision: a predicate is risky only when a `risk` declaration says so.
    pub fn risk_markers(&self) -> Vec<(Name, RiskTheme)> {
        self.iter()
            .filter_map(|d| match &d.kind {
                DeclKind::Risk { theme, pred } => Some((pred.clone(), *theme)),
                _ => None,
            })
            .collect()
    }

    /// Declared rule priorities, in insertion order. Each one keeps the
    /// namespace that declared it; the relation is directed, `winner` outranks
    /// `loser`.
    pub fn priorities(&self) -> Vec<PriorityDecl> {
        self.iter()
            .filter_map(|d| match &d.kind {
                DeclKind::Priority {
                    winner,
                    loser,
                    declared_in,
                } => Some(PriorityDecl {
                    name: d.name.clone(),
                    winner: winner.clone(),
                    loser: loser.clone(),
                    declared_in: declared_in.clone(),
                    sources: d.sources.clone(),
                }),
                _ => None,
            })
            .collect()
    }
}

/// The named universal binders of a declared type, outermost first, and the
/// body those binders scope.
///
/// The type is weak-head normalized, then every leading *named* `Pi` is
/// stripped. An anonymous `Pi` ends the telescope: `A → B` binds no variable a
/// caller could name, so it stays part of the body. `None` means the type has
/// no named universal binder at all.
///
/// The binder names must be usable as the value names of an instantiation: a
/// repeated name cannot be distinguished in a recorded binding, and a name
/// starting with `?` would collide with the reasoner's open-pattern encoding.
/// Such a declaration is refused (`None`) rather than renamed silently. The
/// same holds for an empty name.
///
/// This is a syntactic view of the declaration for universal elimination; it
/// performs no type checking of its own.
pub fn named_binders(env: &Env, ty: &Expr) -> Result<Option<(Vec<Name>, Expr)>> {
    let mut binders = Vec::new();
    let mut head = ty.clone();
    loop {
        head = crate::norm::whnf(env, &head)?;
        match head {
            Expr::Pi {
                name: Some(binder),
                codomain,
                ..
            } => {
                if binder.is_empty() || binder.starts_with('?') || binders.contains(&binder) {
                    return Ok(None);
                }
                binders.push(binder);
                head = *codomain;
            }
            other => {
                if binders.is_empty() {
                    return Ok(None);
                }
                return Ok(Some((binders, other)));
            }
        }
    }
}

/// Build `∀ (p1 : t1) ... (pn : tn), body` from a telescope, outermost first.
pub fn telescope(params: &[(Name, Expr)], body: Expr) -> Expr {
    params
        .iter()
        .rev()
        .fold(body, |acc, (n, ty)| Expr::forall(n, ty.clone(), acc))
}

/// A rule's declared type: telescope over params and premises, ending in the
/// conclusion. Applying the constant to a parameter and a proof of every
/// premise therefore yields a proof of the conclusion.
///
/// Premise types are written relative to the telescope prefix, and later
/// premises may mention earlier named ones. The conclusion is checked in the
/// *full* telescope, which is what makes dependency between premises usable.
pub fn rule_type(rule: &RuleDecl) -> Expr {
    let params = rule.telescope();
    telescope(&params, rule.conclusion.clone())
}

/// Refuse a telescope whose binder names are not pairwise distinct.
///
/// Opening a rule replaces each telescope binder by the constant `?<binder>`
/// (see `open_vars`), so two binders with the same name become one constant:
/// a premise proof could be taken for a parameter value, or the other way
/// round. The collision is reported instead of silently renamed, because only
/// the author knows which binding the rule meant.
pub fn check_unique_binders(binders: &[Name]) -> Result<()> {
    let mut seen = BTreeSet::new();
    for binder in binders {
        if !seen.insert(binder) {
            return Err(Error::other(format!(
                "参数/前提 binder `{binder}` 重名：重名会让推理器把不同的绑定打开成同一个 \
                 `?{binder}` 常量，从而把前提证明当成参数值（或反过来）。必须改名。"
            )));
        }
    }
    Ok(())
}

impl RuleDecl {
    /// The kernel telescope: the parameters followed by the **plain**
    /// premises.
    ///
    /// Disjunctive and existential premises are not kernel arguments: their
    /// proofs are side conditions of the logical certificate layer, because the
    /// kernel's context types are prefix-relative and cannot express the
    /// impredicative encoding those compound proofs would need. Their
    /// well-formedness is still checked here; only the proof term is not part
    /// of the rule constant's type. `unless`, guards and applicability are
    /// outside the kernel for the same reason.
    pub fn telescope(&self) -> Vec<(Name, Expr)> {
        let mut out = self.params.clone();
        for (i, premise) in self.premises.iter().enumerate() {
            if !matches!(premise.kind, PremiseKind::Plain(_)) {
                continue;
            }
            out.push((premise.binder_or(i), premise.kernel_type()));
        }
        out
    }

    /// How many plain premises precede premise `index`.
    pub fn plain_premises_before(&self, index: usize) -> usize {
        self.premises[..index]
            .iter()
            .filter(|premise| matches!(premise.kind, PremiseKind::Plain(_)))
            .count()
    }

    /// How many plain premises the rule has in total.
    pub fn plain_premise_count(&self) -> usize {
        self.premises
            .iter()
            .filter(|premise| matches!(premise.kind, PremiseKind::Plain(_)))
            .count()
    }

    /// Names of the telescope binders, outermost first.
    pub fn binder_names(&self) -> Vec<Name> {
        self.telescope().into_iter().map(|(n, _)| n).collect()
    }

    /// Check a rule's internal consistency: every premise, every `unless`
    /// condition and the conclusion must be well-typed in the rule's
    /// telescope, and the conclusion must be a proposition.
    ///
    /// Scoping, which is the subtle part: premise `i` is written in the scope
    /// of *the params and the premises before it*, not of all premises. The
    /// conclusion is written in the scope of the whole telescope. Getting
    /// this wrong silently reinterprets de Bruijn indices, so it is spelled
    /// out step by step.
    pub fn check(&self, env: &Env, conclusion_ty: &Expr) -> Result<()> {
        // A binder name must be unique across params and premises. Opening
        // the rule replaces every binder by the constant `?<binder>`, so two
        // different bindings with the same name become the same constant: a
        // premise proof could be taken for a parameter value, or the other
        // way round. Renaming silently would hide which binding the source
        // meant, so it is refused before anything else.
        check_unique_binders(&self.binder_names())?;
        // The witness binder of an existential premise is opened as a local
        // `?name` constant while that premise is matched. It is not a telescope
        // binder, so it must not collide with one (or with another existential
        // binder): a collision would let a parameter value, a premise proof or
        // another witness impersonate this witness.
        let telescope_binders = self.binder_names();
        let mut exists_binders: Vec<Name> = Vec::new();
        for (i, premise) in self.premises.iter().enumerate() {
            let PremiseKind::Exists { binder, .. } = &premise.kind else {
                continue;
            };
            if telescope_binders.contains(binder) || exists_binders.contains(binder) {
                return Err(Error::other(format!(
                    "前提 {} 的存在见证变量 `{binder}` 与参数、前提绑定或另一存在见证重名：\
                     见证变量会与规则绑定混为一个 `?{binder}` 常量，必须改名",
                    i + 1
                )));
            }
            exists_binders.push(binder.clone());
        }
        let mut ctx = Ctx::new();
        for (i, (n, ty)) in self.params.iter().enumerate() {
            check::check_is_type(env, &ctx, ty)
                .map_err(|e| Error::other(format!("规则第 {} 个参数无法成立：{e}", i + 1)))?;
            // The stored type is relative to its own prefix, which is exactly
            // `ctx` before the push.
            ctx.push(Some(n.clone()), ty.clone());
        }
        for (i, premise) in self.premises.iter().enumerate() {
            match &premise.kind {
                PremiseKind::Plain(ty) => {
                    check::check_is_type(env, &ctx, ty)
                        .map_err(|e| Error::other(format!("前提 {} 不成立：{e}", i + 1)))?;
                    if let Some(op) = crate::builtin::comparison_head(&self.open_premise_plain(i)) {
                        return Err(Error::other(comparison_premise_error(i + 1, op.name())));
                    }
                }
                PremiseKind::Or(branches) => {
                    if branches.len() < 2 {
                        return Err(Error::other(format!(
                            "前提 {} 是析取，但只写了 {} 个分支：`premise P or Q` 至少要有两个分支",
                            i + 1,
                            branches.len()
                        )));
                    }
                    if branches.len() > MAX_OR_BRANCHES {
                        return Err(Error::other(format!(
                            "前提 {} 的析取有 {} 个分支，超过每个析取前提 {MAX_OR_BRANCHES} 个分支的上限",
                            i + 1,
                            branches.len()
                        )));
                    }
                    for (j, branch) in branches.iter().enumerate() {
                        check::check(env, &ctx, branch, &Expr::Sort(0)).map_err(|e| {
                            Error::other(format!(
                                "前提 {} 的第 {} 个析取分支不是命题：{e}",
                                i + 1,
                                j + 1
                            ))
                        })?;
                        if let Some(op) = crate::builtin::comparison_head(&self.open_branch(i, j)) {
                            return Err(Error::other(format!(
                                "前提 {number} 的第 {branch} 个析取分支是以 `{name}` 打头的比较：\
                                 比较不参与规则触发，不能作为一个可证明的析取分支",
                                number = i + 1,
                                branch = j + 1,
                                name = op.name()
                            )));
                        }
                    }
                }
                PremiseKind::Exists {
                    binder,
                    domain,
                    body,
                } => {
                    check::check_is_type(env, &ctx, domain).map_err(|e| {
                        Error::other(format!("前提 {} 的存在量词类型不成立：{e}", i + 1))
                    })?;
                    let mut inner = ctx.clone();
                    inner.push(Some(binder.clone()), domain.clone());
                    check::check(env, &inner, body, &Expr::Sort(0)).map_err(|e| {
                        Error::other(format!("前提 {} 的存在量词体内不是命题：{e}", i + 1))
                    })?;
                    if let Some(op) = crate::builtin::comparison_head(&self.open_exists_body(i)) {
                        return Err(Error::other(format!(
                            "前提 {number} 的存在量词体是以 `{name}` 打头的比较：\
                             比较不参与规则触发，不能作为存在见证要满足的命题",
                            number = i + 1,
                            name = op.name()
                        )));
                    }
                }
            }
            let bind = premise.binder_or(i);
            if matches!(premise.kind, PremiseKind::Plain(_)) {
                ctx.push(Some(bind), premise.kernel_type());
            }
        }
        for (i, u) in self.unlesses.iter().enumerate() {
            check::check(env, &ctx, u, &Expr::Sort(0))
                .map_err(|e| Error::other(format!("unless {} 不是命题：{e}", i + 1)))?;
            if let Some(op) = crate::builtin::comparison_head(&self.open_unless_text(u)) {
                return Err(Error::other(format!(
                    "unless {number} 是以 `{name}` 打头的比较（`{name} a b`）：比较目前不参与规则触发，\
                     不能靠“求值成 True 再当作阻断条件已成立”来阻断规则",
                    name = op.name(),
                    number = i + 1
                )));
            }
        }
        // Guards are the explicit place where a comparison decides one instance.
        // Each one must be a comparison and a proposition, and it may only
        // judge the rule's parameters: a premise binder is a proof term, not a
        // value, so a guard that mentioned one could never close by the
        // instance's bindings.
        let premise_binders: Vec<Name> = (0..self.premises.len())
            .filter(|i| matches!(self.premises[*i].kind, PremiseKind::Plain(_)))
            .map(|i| self.premises[i].binder_or(i))
            .collect();
        for (i, g) in self.guards.iter().enumerate() {
            let opened = self.open_guard(i);
            let Some(op) = crate::builtin::comparison_head(&opened) else {
                return Err(Error::other(format!(
                    "守卫 {number} 不是比较：`guard` 只能判定 `less` / `le` 比较（例如 `(le a 5000)`）；\
                     其它表达式（如 `guard 3000`）既不产生真值，也不能决定规则是否触发",
                    number = i + 1
                )));
            };
            check::check(env, &ctx, g, &Expr::Sort(0)).map_err(|e| {
                Error::other(format!(
                    "守卫 {number} 不是命题（`{kind}` 比较要写成 `({kind} a b)`）：{e}",
                    number = i + 1,
                    kind = op.name()
                ))
            })?;
            if let Some(binder) = premise_binders
                .iter()
                .find(|binder| mentions_pattern(&opened, binder))
            {
                return Err(Error::other(format!(
                    "守卫 {number} 引用了前提绑定 `?{binder}`：守卫只能判定规则参数的值，\
                     不能判定前提的证明",
                    number = i + 1
                )));
            }
        }
        let t = check::infer(env, &ctx, &self.conclusion)
            .map_err(|e| Error::other(format!("结论不成立：{e}")))?;
        if !crate::conv::convertible(env, &ctx, &t, conclusion_ty)? {
            return Err(Error::TypeMismatch {
                expected: conclusion_ty.clone(),
                actual: t,
            });
        }

        // Every parameter must be fixed by a premise at instantiation time.
        // If one appears in the conclusion or in an `unless` condition but in
        // no premise, the reasoner would leave it as a `?name` constant, so
        // the conclusion or the blocker never closes, and a certificate could
        // invent a binding to dodge the blocker. If it appears nowhere at all,
        // the reasoner never binds it, while the certificate checker demands a
        // binding for every parameter: the two disagree about what a complete
        // instance is. Both are silent holes, so they are refused at load time.
        for (binder, _) in &self.params {
            // A parameter must be *guaranteed* a value by some premise. A
            // plain premise binds it whatever fact matches; an existential
            // premise binds it through its body (the witness search matches the
            // body against facts); a disjunctive premise binds it only when
            // every branch mentions it, because the branch actually chosen must
            // bind it. A parameter that appears in only some branches of every
            // premise mentioning it could stay open, so it is refused rather
            // than silently producing a non-closed instance for one choice.
            let in_premise =
                (0..self.premises.len()).any(|i| self.premise_constrains_param(i, binder));
            if in_premise {
                continue;
            }
            let in_conclusion = mentions_pattern(&self.open_conclusion(), binder);
            let in_unless = self
                .unlesses
                .iter()
                .any(|u| mentions_pattern(&self.open_unless_text(u), binder));
            let in_guard =
                (0..self.guards.len()).any(|i| mentions_pattern(&self.open_guard(i), binder));
            if in_conclusion || in_unless || in_guard {
                return Err(Error::other(format!(
                    "参数 `{binder}` 出现在结论、unless 阻断条件或 guard 守卫里，\
                     但没有出现在任何前提里（或没有一条前提保证绑定它）：\
                     它必须出现在普通前提里、出现在某条析取前提的每个分支里，或出现在某条存在前提的体内；\
                     只出现在部分析取分支里时，选了另一个分支的实例无法给出它的值。"
                )));
            }
            return Err(Error::other(format!(
                "参数 `{binder}` 没有出现在任何前提里，也没有出现在结论、unless 或 guard 里：\
                 它是一个无法被实例化的空参数。请把它纳入某条前提，或删掉这个参数。"
            )));
        }
        Ok(())
    }

    /// Open a term of the rule telescope into a *pattern*: every bound
    /// variable is replaced by a constant named `?<binder>`. The reasoner
    /// matches grounded facts against these patterns, and the kernel never
    /// sees them, so no soundness claim rests on this translation.
    fn open(&self, e: &Expr, in_scope: usize) -> Expr {
        let names = self.binder_names();
        open_vars(e, &names, 0, in_scope)
    }

    pub fn open_param_type(&self, i: usize) -> Expr {
        self.open(&self.params[i].1, i)
    }

    /// The plain form of premise `i`. Only valid for [`PremiseKind::Plain`];
    /// compound premises are opened by [`RuleDecl::open_premise`] instead.
    pub fn open_premise_plain(&self, i: usize) -> Expr {
        match &self.premises[i].kind {
            PremiseKind::Plain(ty) => {
                self.open(ty, self.params.len() + self.plain_premises_before(i))
            }
            _ => Expr::Sort(0),
        }
    }

    /// Open one premise into the reasoner's pattern language.
    pub fn open_premise(&self, i: usize) -> OpenPremise {
        let in_scope = self.params.len() + self.plain_premises_before(i);
        match &self.premises[i].kind {
            PremiseKind::Plain(ty) => OpenPremise::Plain(self.open(ty, in_scope)),
            PremiseKind::Or(branches) => {
                OpenPremise::Or(branches.iter().map(|b| self.open(b, in_scope)).collect())
            }
            PremiseKind::Exists {
                binder,
                domain,
                body,
            } => {
                // The witness binder is appended to the *visible* telescope
                // prefix: `Var(0)` of the body is the witness, `Var(1 + k)` is
                // the prefix binder `k` away. The prefix contains params and
                // plain premises before this one; later plain premise binders
                // are not in scope here.
                let mut names: Vec<Name> = self.binder_names().into_iter().take(in_scope).collect();
                names.push(binder.clone());
                OpenPremise::Exists {
                    binder: binder.clone(),
                    domain: self.open(domain, in_scope),
                    body: open_vars(body, &names, 0, in_scope + 1),
                }
            }
        }
    }

    /// Open branch `j` of the disjunctive premise `i`.
    pub fn open_branch(&self, i: usize, j: usize) -> Expr {
        match &self.premises[i].kind {
            PremiseKind::Or(branches) => self.open(
                &branches[j],
                self.params.len() + self.plain_premises_before(i),
            ),
            _ => Expr::Sort(0),
        }
    }

    /// Open the body of the existential premise `i`, with the witness binder
    /// as the `?<binder>` placeholder and the telescope prefix opened too.
    pub fn open_exists_body(&self, i: usize) -> Expr {
        match &self.premises[i].kind {
            PremiseKind::Exists { binder, body, .. } => {
                let prefix = self.params.len() + self.plain_premises_before(i);
                let mut names: Vec<Name> = self.binder_names().into_iter().take(prefix).collect();
                names.push(binder.clone());
                open_vars(body, &names, 0, prefix + 1)
            }
            _ => Expr::Sort(0),
        }
    }

    /// Does premise `i` guarantee a value for `binder` regardless of which
    /// fact matches or which branch is chosen?
    fn premise_constrains_param(&self, i: usize, binder: &Name) -> bool {
        match self.open_premise(i) {
            OpenPremise::Plain(pattern) => mentions_pattern(&pattern, binder),
            OpenPremise::Or(branches) => branches
                .iter()
                .all(|branch| mentions_pattern(branch, binder)),
            OpenPremise::Exists { body, .. } => mentions_pattern(&body, binder),
        }
    }

    pub fn open_conclusion(&self) -> Expr {
        self.open(
            &self.conclusion,
            self.params.len() + self.plain_premise_count(),
        )
    }

    pub fn open_unless(&self, i: usize) -> Expr {
        self.open(
            &self.unlesses[i],
            self.params.len() + self.plain_premise_count(),
        )
    }

    /// Open a `guard` into a pattern: its parameters become `?<binder>`.
    ///
    /// A guard may only mention the rule's parameters, so opening it at the
    /// whole-telescope depth is the same as opening it over the parameters
    /// alone. The reasoner closes this pattern with the instance's bindings and
    /// evaluates it; the certificate checker rebuilds it the same way.
    pub fn open_guard(&self, i: usize) -> Expr {
        self.open(
            &self.guards[i],
            self.params.len() + self.plain_premise_count(),
        )
    }

    /// Open an [`unless`] expression that has already been unpacked.
    pub fn open_unless_text(&self, e: &Expr) -> Expr {
        self.open(e, self.params.len() + self.plain_premise_count())
    }
}

/// Replace free de Bruijn variables with `?name` constants.
fn open_vars(e: &Expr, names: &[Name], depth: usize, in_scope: usize) -> Expr {
    match e {
        Expr::Var(j) => {
            // `j - depth` is the index relative to the in-scope telescope.
            if *j < depth {
                Expr::Var(*j)
            } else {
                let rel = *j - depth;
                if rel < in_scope && in_scope <= names.len() {
                    // The innermost visible binder is `names[in_scope-1]`.
                    let binder = in_scope - 1 - rel;
                    Expr::constant(format!("?{}", names[binder]))
                } else {
                    Expr::Var(*j)
                }
            }
        }
        Expr::Sort(_) | Expr::Const(_) | Expr::Num(_) | Expr::Date(_) => e.clone(),
        Expr::Pi {
            name,
            domain,
            codomain,
        } => Expr::Pi {
            name: name.clone(),
            domain: Box::new(open_vars(domain, names, depth, in_scope)),
            codomain: Box::new(open_vars(codomain, names, depth + 1, in_scope)),
        },
        Expr::Lam { name, domain, body } => Expr::Lam {
            name: name.clone(),
            domain: Box::new(open_vars(domain, names, depth, in_scope)),
            body: Box::new(open_vars(body, names, depth + 1, in_scope)),
        },
        Expr::App { func, arg } => Expr::App {
            func: Box::new(open_vars(func, names, depth, in_scope)),
            arg: Box::new(open_vars(arg, names, depth, in_scope)),
        },
        Expr::Let { name, value, body } => Expr::Let {
            name: name.clone(),
            value: Box::new(open_vars(value, names, depth, in_scope)),
            body: Box::new(open_vars(body, names, depth + 1, in_scope)),
        },
    }
}

/// Is this a pattern variable, i.e. a constant produced by `open`?
pub fn is_pattern_var(e: &Expr) -> Option<&str> {
    match e {
        Expr::Const(n) => n.strip_prefix('?'),
        _ => None,
    }
}

/// Does an opened expression mention the pattern constant `?binder`?
fn mentions_pattern(e: &Expr, binder: &Name) -> bool {
    match is_pattern_var(e) {
        Some(pv) => pv == binder.as_ref(),
        None => match e {
            Expr::Sort(_) | Expr::Var(_) | Expr::Const(_) | Expr::Num(_) | Expr::Date(_) => false,
            Expr::Pi {
                domain, codomain, ..
            } => mentions_pattern(domain, binder) || mentions_pattern(codomain, binder),
            Expr::Lam { domain, body, .. } => {
                mentions_pattern(domain, binder) || mentions_pattern(body, binder)
            }
            Expr::App { func, arg } => {
                mentions_pattern(func, binder) || mentions_pattern(arg, binder)
            }
            Expr::Let { value, body, .. } => {
                mentions_pattern(value, binder) || mentions_pattern(body, binder)
            }
        },
    }
}

/// Replace every `?name` pattern constant in `expression` by the value the
/// substitution gives for it. A name without a value stays as the constant,
//      which lets a caller detect an incomplete instantiation instead of
/// silently turning it into an open term.
pub fn substitute_pattern_constants(expression: &Expr, values: &[(Name, Expr)]) -> Expr {
    match expression {
        Expr::Const(name) => match name.strip_prefix('?') {
            Some(parameter) => values
                .iter()
                .rev()
                .find(|(key, _)| key.as_ref() == parameter)
                .map(|(_, value)| value.clone())
                .unwrap_or_else(|| expression.clone()),
            None => expression.clone(),
        },
        Expr::Sort(_) | Expr::Var(_) | Expr::Num(_) | Expr::Date(_) => expression.clone(),
        Expr::Pi {
            name,
            domain,
            codomain,
        } => Expr::Pi {
            name: name.clone(),
            domain: Box::new(substitute_pattern_constants(domain, values)),
            codomain: Box::new(substitute_pattern_constants(codomain, values)),
        },
        Expr::Lam { name, domain, body } => Expr::Lam {
            name: name.clone(),
            domain: Box::new(substitute_pattern_constants(domain, values)),
            body: Box::new(substitute_pattern_constants(body, values)),
        },
        Expr::App { func, arg } => Expr::App {
            func: Box::new(substitute_pattern_constants(func, values)),
            arg: Box::new(substitute_pattern_constants(arg, values)),
        },
        Expr::Let { name, value, body } => Expr::Let {
            name: name.clone(),
            value: Box::new(substitute_pattern_constants(value, values)),
            body: Box::new(substitute_pattern_constants(body, values)),
        },
    }
}

/// The message for a premise written as a bare comparison.
fn comparison_premise_error(number: usize, operation: &str) -> String {
    format!(
        "前提 {number} 是以 `{operation}` 打头的比较（`{operation} a b`）：比较目前不参与规则触发，\
         不能靠“求值成 True 再当作前提已成立”来让规则开火；\
         数字比较请写在结论的计算里，或先作为事实登记"
    )
}
