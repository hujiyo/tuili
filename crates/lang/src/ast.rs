//! AST for the surface language, before elaboration.

use std::fmt;

use std_deduce_kernel::{FactIdentity, InterpretationDirection};

#[derive(Debug, Clone, PartialEq)]
pub enum Term {
    /// `Prop`
    Prop,
    /// `Type` or `Type n`
    Type(Option<u32>),
    /// A variable or constant, resolved later.
    Ident(String),
    /// `∀ (x : A), B` or `A → B`
    Pi {
        name: Option<String>,
        domain: Box<Term>,
        codomain: Box<Term>,
    },
    /// `fun (x : A) => body`
    Lam {
        name: String,
        domain: Box<Term>,
        body: Box<Term>,
    },
    /// `f a`
    App(Box<Term>, Box<Term>),
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

/// A top-level declaration.
#[derive(Debug, Clone, PartialEq)]
pub enum Item {
    /// `import cn.constitution` — the named namespace must already be loaded.
    /// Imports appear before the namespace and every declaration. The import
    /// carries no version: the lock file fixes versions.
    Import(String),
    /// `namespace cn.constitution` — the first non-import item of a module
    /// file. Every declaration name and every reference to a declaration in
    /// that file is then required to carry the namespace prefix.
    Namespace(String),
    /// `sort 公民`
    Sort {
        name: String,
        source: Option<SourceSpec>,
    },
    /// `obj 张三 : 公民` — an individual. Individuals are constants of a
    /// declared sort, kept distinct from predicates so that a typo cannot
    /// quietly become a new individual.
    Obj {
        name: String,
        ty: Term,
        source: Option<SourceSpec>,
    },
    /// `pred 侵害 : 公民 → 行为 → Prop`
    Pred {
        name: String,
        ty: Term,
        source: Option<SourceSpec>,
    },
    /// `axiom 张三是公民 : 公民 张三`
    ///
    /// The elaborated type decides what the declaration is: a proposition is
    /// a fact and carries an identity (written `identity <keyword>` or
    /// defaulted from the file); anything else only names a constant.
    Axiom {
        name: String,
        ty: Term,
        source: Option<SourceSpec>,
        identity: Option<FactIdentity>,
        /// `occurred_at <YYYY-MM-DD>`: the day the fact occurred. Only an
        /// `axiom` that elaborates to a proposition (a fact) may carry one.
        occurred_at: Option<String>,
        /// `occurred_in <CODE>`: where the fact occurred.
        occurred_in: Option<String>,
    },
    /// `def 合法搜查 := ... : T`
    Def {
        name: String,
        ty: Term,
        body: Term,
        source: Option<SourceSpec>,
    },
    /// A defeasible rule, the centre of the system.
    Rule {
        name: String,
        params: Vec<(String, Term)>,
        premises: Vec<Premise>,
        conclusion: Term,
        defeaters: Vec<Defeater>,
        sources: Vec<SourceSpec>,
        /// The scope clauses written on this rule. Missing fields are filled
        /// from the containing pack's manifest by the loader; the parser only
        /// records what was written.
        scope: ScopeSpec,
    },
    /// `interpret 解释A : P → Q` followed by a required `direction` line and
    /// at least one `source` line. Both sides must be propositions; the
    /// declaration is recorded as a constant that the reasoner applies only
    /// when the query explicitly enables it.
    Interpretation {
        name: String,
        from: Term,
        to: Term,
        direction: InterpretationDirection,
        sources: Vec<SourceSpec>,
    },
    /// `contrary 该批准 不该批准` — a declared incompatibility between two
    /// predicates. The system does not infer it from the names.
    Contrary {
        left: String,
        right: String,
        source: Option<SourceSpec>,
    },
    /// `unique 应适用 1` — argument 1 (one-based) is single-valued: two facts
    /// that differ there and agree elsewhere cannot both hold.
    Unique {
        pred: String,
        index: usize,
        source: Option<SourceSpec>,
    },
    /// `priority a.r over b.r source …` — a provenance-carrying priority: the
    /// winner outranks the loser. A module (a file with a namespace) is the
    /// only place that may assert one; the declaring namespace is part of the
    /// claim.
    Priority {
        winner: String,
        loser: String,
        sources: Vec<SourceSpec>,
    },
    /// `#check term`
    Check(Term),
    /// `#why prop` — derive it and show the tree.
    Why(Term),
    /// `#gap prop` — derive it and show what is missing.
    Gap(Term),
    /// `#proposition prop` — check that the term is a proposition. This does
    /// not prove the proposition.
    Proposition(Term),
    /// `#show name` — print a declaration.
    Show(String),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Premise {
    pub name: Option<String>,
    pub ty: Term,
}

/// The scope clauses written on one rule:
/// `effective <YYYY-MM-DD>`, `repealed <YYYY-MM-DD>`, `jurisdiction <CODE>`,
/// `territory <CODE>`.
///
/// The parser only records the raw values; dates and codes are validated when
/// the theory is loaded. `repealed` maps to the exclusive end of the range.
/// This is metadata, not applicability: nothing filters rules by it here.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct ScopeSpec {
    /// First day the rule is in force (inclusive).
    pub effective_from: Option<String>,
    /// First day the rule is no longer in force (exclusive).
    pub effective_to: Option<String>,
    pub jurisdiction: Option<String>,
    pub territory: Option<String>,
}

impl ScopeSpec {
    /// Whether any scope clause was written.
    pub fn is_empty(&self) -> bool {
        self.effective_from.is_none()
            && self.effective_to.is_none()
            && self.jurisdiction.is_none()
            && self.territory.is_none()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum Defeater {
    /// `unless P` — the rule cannot fire when P holds.
    Unless(Term),
    /// `defeated_by 规则名` — explicit rule-vs-rule conflict resolution.
    By(String),
    /// `prefer 规则名` — this rule wins over a competitor.
    Prefer(String),
}

/// A provenance annotation, parsed from
/// `source text "宪法" locator "第三十九条"`.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct SourceSpec {
    /// The file or instrument name.
    pub text: String,
    /// The article or section within `text`.
    pub locator: String,
    pub version: String,
    pub effective: Option<String>,
    /// The quoted wording of the provision.
    pub quote: String,
    pub url: String,
    pub jurisdiction: String,
    pub retrieved_at: String,
    pub hash: String,
    /// Why we formalised the source this way, when that is not obvious.
    pub note: String,
}
