//! AST for the surface language, before elaboration.

use std::fmt;

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
    Axiom {
        name: String,
        ty: Term,
        source: Option<SourceSpec>,
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
    },
    /// `interpret 解释A : 概念 -> 概念`
    Interpretation {
        name: String,
        from: Term,
        to: Term,
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
    /// `#check term`
    Check(Term),
    /// `#why prop` — derive it and show the tree.
    Why(Term),
    /// `#gap prop` — derive it and show what is missing.
    Gap(Term),
    /// `#assert prop`
    Assert(Term),
    /// `#show name` — print a declaration.
    Show(String),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Premise {
    pub name: Option<String>,
    pub ty: Term,
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

/// A provenance annotation, parsed from `source "宪法" "第三十九条"`.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct SourceSpec {
    pub text: String,
    pub locator: String,
    pub version: String,
    pub effective: Option<String>,
    pub note: String,
}
