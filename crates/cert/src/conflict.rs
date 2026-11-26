//! The declared conflict relation over kernel propositions.
//!
//! Two propositions conflict when either
//!
//! * their predicate heads are declared `contrary` and every argument is the
//!   same, or
//! * they share a head and differ at exactly one argument position that head
//!   declares `unique`.
//!
//! Both sides are read after kernel normalization (beta, `def` delta, zeta),
//! so a proposition written through a `def` alias reaches the predicate its
//! declaration names: `夫妻 张三 李四` and `非配偶 张三 李四` conflict when
//! `配偶` and `非配偶` are contrary and `夫妻` is defined as `配偶`. A
//! universal fact's substituted conclusion is read the same way, because
//! [`view`] normalizes the expression it is given.
//!
//! Arguments are compared by the structural key of the normalized term
//! ([`crate::expression_key`]), never by printed text: two alpha-variant
//! arguments denote the same term, and a constant that happens to print like a
//! bound variable cannot alias it. A proposition without a constant head (a
//! quantified or opaque statement) has no declared `contrary`/`unique`
//! relation, so it cannot conflict this way; [`view`] reports it as `None`
//! instead of guessing a head.
//!
//! [`in_conflict`] is the one judgement. The reasoner calls it to detect the
//! conflicts it records, and [`crate::check`] calls it to refuse a certificate
//! that omits a conflict with an environment fact. There is no second
//! implementation, so a certificate can never be judged by a relation the
//! producer does not use.

use std::collections::{BTreeMap, BTreeSet};

use std_deduce_kernel::norm::{normalize, spine};
use std_deduce_kernel::pretty::print_expr;
use std_deduce_kernel::{Ctx, Env, Expr, Name};

use crate::key::expression_key;
use crate::model::MAX_CERT_EXPR_NODES;

/// A proposition as the conflict relation reads it: the predicate head and its
/// arguments after kernel normalization.
///
/// The fields are private: a view is only ever produced by [`view`], so every
/// caller reads both sides under the same normalization.
#[derive(Debug, Clone)]
pub struct ConflictView {
    head: Name,
    /// Structural keys of the normalized arguments, in order. The key is
    /// computed once per view, so a pair is compared without re-walking the
    /// terms.
    arguments: Vec<String>,
}

/// The environment's declared conflict relation: `contrary` pairs and `unique`
/// argument positions.
///
/// The `contrary` relation is symmetric, so both directions are stored. The
/// declarations are read from the kernel ledger by [`Declarations::from_env`];
/// no declaration is guessed from a predicate's spelling.
#[derive(Debug, Clone, Default)]
pub struct Declarations {
    /// predicate -> predicates declared contrary to it, in both directions
    contraries: BTreeMap<Name, BTreeSet<Name>>,
    /// predicate -> argument positions declared single-valued
    uniques: BTreeMap<Name, BTreeSet<usize>>,
}

impl Declarations {
    /// Read every `contrary` and `unique` declaration of the environment.
    pub fn from_env(env: &Env) -> Self {
        let mut contraries: BTreeMap<Name, BTreeSet<Name>> = BTreeMap::new();
        for (left, right) in env.contrary_pairs() {
            contraries
                .entry(left.clone())
                .or_default()
                .insert(right.clone());
            contraries.entry(right).or_default().insert(left);
        }
        let mut uniques: BTreeMap<Name, BTreeSet<usize>> = BTreeMap::new();
        for (pred, index) in env.unique_positions() {
            uniques.entry(pred).or_default().insert(index);
        }
        Declarations {
            contraries,
            uniques,
        }
    }
}

/// Are two propositions in conflict under `declarations`?
///
/// Arity must match. A contrary pair requires every argument to be
/// structurally equal after normalization; a `unique` conflict requires the
/// same head and exactly one differing argument, at a position declared
/// single-valued. The relation is symmetric.
pub fn in_conflict(declarations: &Declarations, left: &ConflictView, right: &ConflictView) -> bool {
    if left.arguments.len() != right.arguments.len() {
        return false;
    }
    if left.head != right.head {
        return declarations
            .contraries
            .get(&left.head)
            .is_some_and(|contradicts| contradicts.contains(&right.head))
            && left
                .arguments
                .iter()
                .zip(right.arguments.iter())
                .all(|(a, b)| a == b);
    }
    let Some(positions) = declarations.uniques.get(&left.head) else {
        return false;
    };
    let differing: Vec<usize> = (0..left.arguments.len())
        .filter(|index| left.arguments[*index] != right.arguments[*index])
        .collect();
    differing.len() == 1 && positions.contains(&differing[0])
}

/// The kernel's view of one proposition for the conflict relation.
///
/// `None` means the proposition has no constant head (a quantified or opaque
/// statement): `contrary`/`unique` are declared over predicates, so such a
/// proposition cannot take part in one. A term beyond the certificate's
/// expression bound, or a normalization that fails, is an error rather than a
/// silent `None`: either would hide a conflict the caller declared.
pub fn view(env: &Env, expression: &Expr) -> Result<Option<ConflictView>, String> {
    if !within_term_limit(expression) {
        return Err(format!(
            "无法判定冲突：命题超过 {MAX_CERT_EXPR_NODES} 个节点上限：{}",
            print_expr(expression)
        ));
    }
    let normalized = normalize(env, &Ctx::new(), expression).map_err(|error| {
        format!(
            "无法归约命题「{}」以判定冲突：{error}",
            print_expr(expression)
        )
    })?;
    if !within_term_limit(&normalized) {
        return Err(format!(
            "无法判定冲突：归约后的命题超过 {MAX_CERT_EXPR_NODES} 个节点上限：{}",
            print_expr(&normalized)
        ));
    }
    let (head, args) = spine(&normalized);
    let Expr::Const(head) = head else {
        return Ok(None);
    };
    Ok(Some(ConflictView {
        head: head.clone(),
        arguments: args.iter().map(|arg| expression_key(arg)).collect(),
    }))
}

/// Whether the expression is within the certificate's single-term bound.
///
/// Conflict detection and premise matching both walk the whole term, so both
/// need the same size bound before doing so.
pub fn within_term_limit(expression: &Expr) -> bool {
    fn count(expression: &Expr, nodes: &mut usize) -> bool {
        *nodes += 1;
        if *nodes > MAX_CERT_EXPR_NODES {
            return false;
        }
        match expression {
            Expr::Sort(_) | Expr::Var(_) | Expr::Const(_) | Expr::Num(_) | Expr::Date(_) => true,
            Expr::Pi {
                domain, codomain, ..
            } => count(domain, nodes) && count(codomain, nodes),
            Expr::Lam { domain, body, .. } => count(domain, nodes) && count(body, nodes),
            Expr::App { func, arg } => count(func, nodes) && count(arg, nodes),
            Expr::Let { value, body, .. } => count(value, nodes) && count(body, nodes),
        }
    }
    count(expression, &mut 0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std_deduce_kernel::env::Env;
    use std_deduce_lang::Library;

    fn env(src: &str) -> Env {
        let mut lib = Library::new();
        lib.load("test", src).expect("the fixture loads");
        lib.env
    }

    fn atom(head: &str, args: &[&str]) -> Expr {
        Expr::apps(
            Expr::constant(head),
            args.iter().map(|arg| Expr::constant(*arg)),
        )
    }

    fn view_of(env: &Env, expression: &Expr) -> ConflictView {
        view(env, expression)
            .expect("the proposition normalizes")
            .expect("the proposition has a predicate head")
    }

    #[test]
    fn a_contrary_pair_conflicts_when_every_argument_agrees() {
        let env = env(
            "sort 人\npred 有罪 : 人 → Prop\npred 无罪 : 人 → Prop\ncontrary 有罪 无罪\nobj 张三 : 人\n",
        );
        let declarations = Declarations::from_env(&env);
        let left = view_of(&env, &atom("有罪", &["张三"]));
        let right = view_of(&env, &atom("无罪", &["张三"]));
        assert!(in_conflict(&declarations, &left, &right));
        assert!(in_conflict(&declarations, &right, &left));
    }

    #[test]
    fn a_contrary_pair_does_not_conflict_when_an_argument_differs() {
        let env = env(
            "sort 人\npred 有罪 : 人 → Prop\npred 无罪 : 人 → Prop\ncontrary 有罪 无罪\n\
             obj 张三 : 人\nobj 李四 : 人\n",
        );
        let declarations = Declarations::from_env(&env);
        let left = view_of(&env, &atom("有罪", &["张三"]));
        let right = view_of(&env, &atom("无罪", &["李四"]));
        assert!(!in_conflict(&declarations, &left, &right));
    }

    #[test]
    fn a_def_alias_is_read_as_the_predicate_it_names() {
        let env = env(
            "sort 人\npred 配偶 : 人 → 人 → Prop\npred 非配偶 : 人 → 人 → Prop\n\
             contrary 配偶 非配偶\ndef 夫妻 : 人 → 人 → Prop := 配偶\n\
             obj 张三 : 人\nobj 李四 : 人\n",
        );
        let declarations = Declarations::from_env(&env);
        let alias = view_of(&env, &atom("夫妻", &["张三", "李四"]));
        let claim = view_of(&env, &atom("非配偶", &["张三", "李四"]));
        assert!(in_conflict(&declarations, &alias, &claim));
    }

    #[test]
    fn a_unique_position_conflicts_only_at_that_position_and_only_once() {
        let env = env(
            "sort 规范\nsort 案件\npred 应适用 : 规范 → 案件 → Prop\nunique 应适用 1\n\
             obj 种子法 : 规范\nobj 条例 : 规范\nobj 案 : 案件\n",
        );
        let declarations = Declarations::from_env(&env);
        let left = view_of(&env, &atom("应适用", &["种子法", "案"]));
        let right = view_of(&env, &atom("应适用", &["条例", "案"]));
        assert!(in_conflict(&declarations, &left, &right));
        // The same head with identical arguments is not a conflict.
        assert!(!in_conflict(&declarations, &left, &left));
    }

    #[test]
    fn a_quantified_proposition_has_no_conflict_view() {
        let env = env("sort 人\npred 有罪 : 人 → Prop\nobj 张三 : 人\n");
        let quantified = Expr::Pi {
            name: Some(std_deduce_kernel::name("x")),
            domain: Box::new(Expr::constant("人")),
            codomain: Box::new(Expr::apps(Expr::constant("有罪"), [Expr::Var(0)])),
        };
        assert!(view(&env, &quantified).expect("normalizes").is_none());
    }
}
