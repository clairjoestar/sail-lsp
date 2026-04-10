//! Pattern exhaustiveness and redundancy checking.
//!
//! This is a Maranget-style matrix algorithm (the "useful" predicate from
//! Luc Maranget's 2008 "Warnings for pattern matching" paper) adapted for
//! Sail's pattern subset. We mirror the design rust-analyzer uses around
//! `rustc_pattern_analysis`: a separate post-inference pass with a clean
//! `Cx`-style trait so the algorithm itself stays language-agnostic.
//!
//! Compared to upstream Sail's `pattern_completeness.ml` we deliberately
//! handle a much smaller language:
//!
//! - **Wild / binding** — bare identifier-as-binding is treated as wildcard.
//! - **Constructor** — `Some(x)`, `Privilege::Machine`, etc. Both Sail's
//!   `App` patterns and bare uppercase `Ident` patterns lower to this.
//! - **Tuple** — `(x, y)` against `(_, A | B)`.
//! - **Or** — `A | B` patterns inside an arm.
//! - **Literal** — bool/number/string/bits/hex literals. The integer
//!   universe is treated as infinite, so a literal-only match is never
//!   certified as exhaustive (matching upstream's conservative posture).
//! - **Typed / AsType / AsBinding / Attribute** — recurse through the
//!   wrapper to the inner pattern.
//!
//! Patterns we don't yet model (vector, list, struct, vector subrange,
//! infix) lower to wildcard so they're treated as covering everything —
//! conservative, no false positives, no false negatives on the supported
//! subset.
//!
//! Guards make completeness undecidable, so a guarded arm doesn't
//! contribute to exhaustiveness coverage (matches both upstream Sail and
//! rust-analyzer).

use std::collections::HashMap;

use sail_parser::core_ast::{Literal, Pattern, Spanned};
use sail_parser::Span;

/// Lightweight pattern form used by the matrix algorithm. Lowered from
/// `core_ast::Pattern` via `lower_pattern`.
#[derive(Clone, Debug)]
pub(crate) enum MatchPat {
    /// `_`, bare lowercase identifier, or any pattern we don't model.
    Wild,
    /// Constructor application: `Some(x)`, `None`, `Privilege::Machine`.
    /// `name` is the constructor name; `args` are the (possibly nested)
    /// sub-patterns. Nullary constructors have an empty `args` vector.
    Ctor { name: String, args: Vec<MatchPat> },
    /// `(p1, p2, ...)`.
    Tuple(Vec<MatchPat>),
    /// Numeric/string/bits/hex/bool literal.
    Literal(LiteralKey),
    /// `p1 | p2 | ...`. Or-patterns are expanded into multiple matrix
    /// rows during lowering, so the algorithm itself never sees this
    /// variant directly.
    Or(Vec<MatchPat>),
}

/// Hashable, equatable form of a literal pattern. We don't try to evaluate
/// integer ranges; the algorithm treats the universe of literals of a
/// given kind as infinite.
#[derive(Clone, Debug, Hash, PartialEq, Eq)]
pub(crate) enum LiteralKey {
    Bool(bool),
    Unit,
    Number(String),
    String(String),
    Binary(String),
    Hex(String),
    Undefined,
}

/// Type abstraction passed to the algorithm. The typechecker fills this
/// in with whatever shape it inferred for the scrutinee.
#[derive(Clone, Debug)]
pub(crate) enum MatchTy {
    /// Concrete enum or union, identified by type name. The type's
    /// constructor list is fetched from the `Ctx` at check time.
    Named(String),
    /// Tuple of N positional types.
    Tuple(Vec<MatchTy>),
    /// Bool — closed universe of `{ true, false }`.
    Bool,
    /// Type we couldn't classify. Treated as having an unlistable
    /// constructor set, so the algorithm only certifies a match
    /// exhaustive when a wildcard arm is present.
    Unknown,
}

/// Constructor universe for a given type. The algorithm uses this to
/// decide whether a wildcard arm is required for exhaustiveness.
#[derive(Clone, Debug)]
pub(crate) enum CtorSet {
    /// Closed set of constructors, each with a fixed arity. The algorithm
    /// can list missing constructors precisely.
    Closed(Vec<CtorInfo>),
    /// Type has a constructor universe but we don't know its members
    /// (e.g. cross-file enum we couldn't aggregate). Conservatively treat
    /// as unlistable.
    Unknown,
    /// Universe is infinite (numeric literals, strings). A wildcard is
    /// the only way to be exhaustive.
    Unlistable,
}

#[derive(Clone, Debug)]
pub(crate) struct CtorInfo {
    pub name: String,
    pub arity: usize,
}

/// Context the algorithm queries to enumerate constructors.
pub(crate) trait Cx {
    /// Return the constructor set for `ty`.
    fn ctors_for(&self, ty: &MatchTy) -> CtorSet;
    /// For a constructor named `name` appearing in a pattern, look up the
    /// types of its sub-patterns. Used to specialise the matrix when we
    /// step into a constructor row.
    fn ctor_sub_tys(&self, name: &str, scrutinee: &MatchTy) -> Vec<MatchTy>;
}

/// One row of the match matrix. Each row holds the lowered pattern of
/// one (un-guarded) arm plus its source location for diagnostic ranges.
#[derive(Clone, Debug)]
pub(crate) struct Row {
    pub pats: Vec<MatchPat>,
    pub arm_span: Span,
    pub has_guard: bool,
}

/// Per-arm input to the algorithm.
#[derive(Clone, Debug)]
pub(crate) struct Arm {
    pub pat: MatchPat,
    pub guard_span: Option<Span>,
    pub arm_span: Span,
}

/// Result of an exhaustiveness analysis.
#[derive(Clone, Debug, Default)]
pub(crate) struct UsefulnessReport {
    /// Witnesses (concrete patterns) that aren't covered by any arm.
    /// Empty if the match is exhaustive.
    pub missing_witnesses: Vec<MatchPat>,
    /// Arms whose pattern was completely subsumed by an earlier arm.
    pub redundant: Vec<Span>,
}

// =============================================================================
// Lowering: core_ast::Pattern -> MatchPat
// =============================================================================

/// Lower a single core_ast pattern. Or-patterns produce a single
/// `MatchPat::Or` whose components have been recursively lowered; the
/// caller flattens this into matrix rows.
pub(crate) fn lower_pattern(pat: &Pattern, pattern_constants: &impl PatternConstants) -> MatchPat {
    match pat {
        Pattern::Wild => MatchPat::Wild,
        Pattern::Ident(name) => {
            // Sail's pattern grammar doesn't distinguish bare-name
            // bindings from nullary constructor matches at the syntactic
            // level: `Foo` may be either `let Foo = ...` (a binding) or
            // `match x { Foo => ... }` (a constructor match). The
            // typechecker resolves this via `pattern_constants` — names
            // that are known constructors are treated as such, everything
            // else is a binder.
            if pattern_constants.contains(name) {
                MatchPat::Ctor {
                    name: name.clone(),
                    args: Vec::new(),
                }
            } else {
                MatchPat::Wild
            }
        }
        Pattern::Literal(lit) => MatchPat::Literal(literal_key(lit)),
        Pattern::Tuple(items) => MatchPat::Tuple(
            items
                .iter()
                .map(|item| lower_pattern(&item.0, pattern_constants))
                .collect(),
        ),
        Pattern::App { callee, args } => MatchPat::Ctor {
            name: callee.0.clone(),
            args: args
                .iter()
                .map(|item| lower_pattern(&item.0, pattern_constants))
                .collect(),
        },
        Pattern::Typed(inner, _)
        | Pattern::AsType(inner, _)
        | Pattern::Attribute { pattern: inner, .. } => {
            lower_pattern(&inner.0, pattern_constants)
        }
        Pattern::AsBinding { pattern, .. } => lower_pattern(&pattern.0, pattern_constants),
        Pattern::Infix { lhs, op, rhs } if op.0 == "|" => MatchPat::Or(vec![
            lower_pattern(&lhs.0, pattern_constants),
            lower_pattern(&rhs.0, pattern_constants),
        ]),
        // Patterns we don't model exhaustively yet — treat as wildcard
        // so they cover everything (no false positives).
        Pattern::TypeVar(_)
        | Pattern::List(_)
        | Pattern::Vector(_)
        | Pattern::Index { .. }
        | Pattern::RangeIndex { .. }
        | Pattern::Struct { .. }
        | Pattern::Infix { .. }
        | Pattern::Error(_) => MatchPat::Wild,
    }
}

fn literal_key(lit: &Literal) -> LiteralKey {
    match lit {
        Literal::Bool(b) => LiteralKey::Bool(*b),
        Literal::Unit => LiteralKey::Unit,
        Literal::Number(s) => LiteralKey::Number(s.clone()),
        Literal::String(s) => LiteralKey::String(s.clone()),
        Literal::Binary(s) => LiteralKey::Binary(s.clone()),
        Literal::Hex(s) => LiteralKey::Hex(s.clone()),
        Literal::BitZero => LiteralKey::Binary("0b0".to_string()),
        Literal::BitOne => LiteralKey::Binary("0b1".to_string()),
        Literal::Undefined => LiteralKey::Undefined,
    }
}

/// Trait the lowerer uses to ask "is this bare-name pattern actually a
/// constructor?". Concrete typechecker passes a closure or its own set.
pub(crate) trait PatternConstants {
    fn contains(&self, name: &str) -> bool;
}

impl<F> PatternConstants for F
where
    F: Fn(&str) -> bool,
{
    fn contains(&self, name: &str) -> bool {
        (self)(name)
    }
}

/// Expand or-patterns inside an arm into multiple rows. The matrix
/// algorithm doesn't see `Or` directly — each branch becomes its own row
/// pointing back at the original arm span.
fn expand_arm_to_rows(arm: &Arm) -> Vec<Row> {
    let mut out = Vec::new();
    expand_one(&arm.pat, arm.arm_span, arm.guard_span.is_some(), &mut out);
    out
}

fn expand_one(pat: &MatchPat, arm_span: Span, has_guard: bool, out: &mut Vec<Row>) {
    match pat {
        MatchPat::Or(branches) => {
            for branch in branches {
                expand_one(branch, arm_span, has_guard, out);
            }
        }
        other => out.push(Row {
            pats: vec![other.clone()],
            arm_span,
            has_guard,
        }),
    }
}

// =============================================================================
// Matrix algorithm
// =============================================================================

/// The driver. Returns missing witnesses + redundant-arm spans for the
/// given match against `scrutinee_ty`.
pub(crate) fn compute_match_usefulness(
    arms: &[Arm],
    scrutinee_ty: &MatchTy,
    cx: &impl Cx,
) -> UsefulnessReport {
    let mut report = UsefulnessReport::default();

    // Phase 1 — redundancy. For each arm, check whether its row is
    // useful relative to all earlier (un-guarded) rows. If it's not,
    // the arm is unreachable. We treat guarded arms as never
    // contributing AND never redundant (the guard might subsume them).
    let mut prefix: Vec<Row> = Vec::new();
    for arm in arms {
        let arm_rows = expand_arm_to_rows(arm);
        // Useless arm = no row in `arm_rows` extends the prefix.
        let any_useful = arm_rows.iter().any(|row| {
            is_useful(&prefix, row.pats.as_slice(), &[scrutinee_ty.clone()], cx)
        });
        if !any_useful && !arm.guard_span.is_some() {
            report.redundant.push(arm.arm_span);
        }
        // Only un-guarded rows go into the prefix; guarded rows might
        // not actually fire even if they syntactically match.
        for row in arm_rows {
            if !row.has_guard {
                prefix.push(row);
            }
        }
    }

    // Phase 2 — exhaustiveness. Synthesize a "wildcard" probe row of
    // length 1 (matching the single-column scrutinee). If the probe is
    // useful, the match is non-exhaustive — we extract concrete witnesses
    // from the failing constructors.
    let probe = vec![MatchPat::Wild];
    let witnesses = collect_witnesses(&prefix, &probe, &[scrutinee_ty.clone()], cx);
    report.missing_witnesses = witnesses;
    report
}

/// `is_useful(M, p)` — does pattern stack `p` cover any value not
/// already covered by some row of `M`?
fn is_useful(matrix: &[Row], pats: &[MatchPat], tys: &[MatchTy], cx: &impl Cx) -> bool {
    if pats.is_empty() {
        // Empty pattern stack: useful iff the matrix has no rows.
        return matrix.is_empty();
    }
    let head = &pats[0];
    let tail = &pats[1..];
    let head_ty = &tys[0];
    let tail_tys = &tys[1..];

    match head {
        MatchPat::Wild => is_useful_wild(matrix, tail, head_ty, tail_tys, cx),
        MatchPat::Ctor { name, args } => {
            let mut new_pats = args.clone();
            new_pats.extend_from_slice(tail);
            // We don't model variant payload types yet — just claim every
            // sub-position is Unknown. The vector length must match the
            // pattern's arg count or the matrix algorithm gets out of sync.
            let _ = head_ty;
            let mut new_tys: Vec<MatchTy> =
                std::iter::repeat(MatchTy::Unknown).take(args.len()).collect();
            new_tys.extend_from_slice(tail_tys);
            let specialized = specialize_ctor(matrix, name, args.len());
            is_useful(&specialized, &new_pats, &new_tys, cx)
        }
        MatchPat::Tuple(items) => {
            let mut new_pats = items.clone();
            new_pats.extend_from_slice(tail);
            // For tuples we ask the cx for sub-types via Tuple shape.
            let sub_tys = match head_ty {
                MatchTy::Tuple(sub) => sub.clone(),
                _ => vec![MatchTy::Unknown; items.len()],
            };
            let mut new_tys = sub_tys;
            new_tys.extend_from_slice(tail_tys);
            let specialized = specialize_tuple(matrix, items.len());
            is_useful(&specialized, &new_pats, &new_tys, cx)
        }
        MatchPat::Literal(key) => {
            let specialized = specialize_literal(matrix, key);
            is_useful(&specialized, tail, tail_tys, cx)
        }
        MatchPat::Or(_) => {
            // Or-patterns should have been expanded by `expand_arm_to_rows`
            // before we hit the matrix. Defensive fallback: split here.
            let mut found = false;
            if let MatchPat::Or(branches) = head {
                for branch in branches {
                    let mut alt = vec![branch.clone()];
                    alt.extend_from_slice(tail);
                    if is_useful(matrix, &alt, tys, cx) {
                        found = true;
                        break;
                    }
                }
            }
            found
        }
    }
}

/// Wildcard case of `is_useful`. Tries every constructor in the column
/// type. If the constructor set is closed and finite, we recurse into
/// each constructor and report useful iff at least one is uncovered.
fn is_useful_wild(
    matrix: &[Row],
    tail: &[MatchPat],
    head_ty: &MatchTy,
    tail_tys: &[MatchTy],
    cx: &impl Cx,
) -> bool {
    let ctors = cx.ctors_for(head_ty);
    match ctors {
        CtorSet::Closed(infos) => {
            for info in &infos {
                let sub_tys = cx.ctor_sub_tys(&info.name, head_ty);
                let new_pats = {
                    let mut v: Vec<MatchPat> =
                        std::iter::repeat(MatchPat::Wild).take(info.arity).collect();
                    v.extend_from_slice(tail);
                    v
                };
                let new_tys = {
                    let mut v = sub_tys;
                    v.extend_from_slice(tail_tys);
                    v
                };
                let specialized = specialize_ctor(matrix, &info.name, info.arity);
                if is_useful(&specialized, &new_pats, &new_tys, cx) {
                    return true;
                }
            }
            false
        }
        CtorSet::Unlistable => {
            // Universe of literals (int / string / bits). The only way
            // to certify exhaustiveness is an explicit wildcard arm.
            let default = default_matrix(matrix);
            if matrix.is_empty() {
                return true;
            }
            if default.is_empty() && !matrix.iter().any(|r| matches!(&r.pats[0], MatchPat::Wild)) {
                return true;
            }
            is_useful(&default, tail, tail_tys, cx)
        }
        CtorSet::Unknown => {
            // We don't know the type at this column at all (typically a
            // constructor sub-position whose payload type we didn't
            // track). Be conservative: any non-empty matrix counts as
            // covering the universe — we can't honestly claim a
            // specific witness on a type we couldn't classify.
            if matrix.is_empty() {
                return true;
            }
            // Still recurse into the tail through the default matrix so
            // multi-column matches with a known column further right
            // still get checked. If the default is empty, treat as
            // covered.
            let default = default_matrix(matrix);
            if default.is_empty() {
                return false;
            }
            is_useful(&default, tail, tail_tys, cx)
        }
    }
}

/// Specialize the matrix by constructor `name`/`arity`: keep rows whose
/// head pattern is either that constructor (extracting its sub-patterns)
/// or a wildcard (which becomes `arity` wildcards).
///
/// Sail unions accept both `Foo(tuple)` (1-arg) and `Foo(a, b, c)`
/// (flattened) forms for the same constructor. Rather than tracking
/// multiple arities per constructor, we accept rows whose name matches
/// regardless of args.len() and pad or truncate to the canonical arity
/// with wildcards. This is conservative — it errs on the side of
/// covering — and eliminates the false positives the strict equality
/// check produced on the sail-riscv corpus.
fn specialize_ctor(matrix: &[Row], name: &str, arity: usize) -> Vec<Row> {
    let mut out = Vec::new();
    for row in matrix {
        match &row.pats[0] {
            MatchPat::Wild => {
                let mut pats: Vec<MatchPat> =
                    std::iter::repeat(MatchPat::Wild).take(arity).collect();
                pats.extend_from_slice(&row.pats[1..]);
                out.push(Row {
                    pats,
                    arm_span: row.arm_span,
                    has_guard: row.has_guard,
                });
            }
            MatchPat::Ctor { name: n, args } if n == name => {
                let mut row_args: Vec<MatchPat> = args.clone();
                row_args.resize(arity, MatchPat::Wild);
                row_args.extend_from_slice(&row.pats[1..]);
                out.push(Row {
                    pats: row_args,
                    arm_span: row.arm_span,
                    has_guard: row.has_guard,
                });
            }
            // Other shapes (Literal, Tuple, mismatched Ctor name) don't
            // specialize — they cover a different part of the universe.
            _ => {}
        }
    }
    out
}

/// Specialize for a Tuple pattern: rows with a tuple head get their
/// elements unpacked into the column; wildcard rows expand to N
/// wildcards. Rows with a non-tuple non-wildcard head are dropped.
fn specialize_tuple(matrix: &[Row], arity: usize) -> Vec<Row> {
    let mut out = Vec::new();
    for row in matrix {
        match &row.pats[0] {
            MatchPat::Wild => {
                let mut pats: Vec<MatchPat> =
                    std::iter::repeat(MatchPat::Wild).take(arity).collect();
                pats.extend_from_slice(&row.pats[1..]);
                out.push(Row {
                    pats,
                    arm_span: row.arm_span,
                    has_guard: row.has_guard,
                });
            }
            MatchPat::Tuple(items) if items.len() == arity => {
                let mut pats = items.clone();
                pats.extend_from_slice(&row.pats[1..]);
                out.push(Row {
                    pats,
                    arm_span: row.arm_span,
                    has_guard: row.has_guard,
                });
            }
            _ => {}
        }
    }
    out
}

/// Specialize for a literal pattern: keep rows whose head is the same
/// literal or a wildcard.
fn specialize_literal(matrix: &[Row], lit: &LiteralKey) -> Vec<Row> {
    let mut out = Vec::new();
    for row in matrix {
        match &row.pats[0] {
            MatchPat::Wild => {
                out.push(Row {
                    pats: row.pats[1..].to_vec(),
                    arm_span: row.arm_span,
                    has_guard: row.has_guard,
                });
            }
            MatchPat::Literal(other) if other == lit => {
                out.push(Row {
                    pats: row.pats[1..].to_vec(),
                    arm_span: row.arm_span,
                    has_guard: row.has_guard,
                });
            }
            _ => {}
        }
    }
    out
}

/// "Default" matrix from Maranget: keep only rows whose head is a
/// wildcard, dropping the head column.
fn default_matrix(matrix: &[Row]) -> Vec<Row> {
    matrix
        .iter()
        .filter_map(|row| match &row.pats[0] {
            MatchPat::Wild => Some(Row {
                pats: row.pats[1..].to_vec(),
                arm_span: row.arm_span,
                has_guard: row.has_guard,
            }),
            _ => None,
        })
        .collect()
}

// =============================================================================
// Witness construction
// =============================================================================

/// Walk the matrix and synthesize concrete patterns that witness each
/// uncovered branch. Mirrors the wildcard probe in `compute_match_usefulness`
/// but recursively builds the missing pattern shape on the way.
fn collect_witnesses(
    matrix: &[Row],
    pats: &[MatchPat],
    tys: &[MatchTy],
    cx: &impl Cx,
) -> Vec<MatchPat> {
    if pats.is_empty() {
        return if matrix.is_empty() {
            vec![]
        } else {
            vec![]
        };
    }
    let head = &pats[0];
    let head_ty = &tys[0];
    let tail = &pats[1..];
    let tail_tys = &tys[1..];
    if !matches!(head, MatchPat::Wild) {
        // We only synthesise witnesses from the wildcard probe, so the
        // initial call always sees Wild. Defensive: if not, just return
        // empty.
        return vec![];
    }
    let ctors = cx.ctors_for(head_ty);
    match ctors {
        CtorSet::Closed(infos) => {
            let mut witnesses = Vec::new();
            for info in &infos {
                let sub_tys = cx.ctor_sub_tys(&info.name, head_ty);
                let new_pats = {
                    let mut v: Vec<MatchPat> =
                        std::iter::repeat(MatchPat::Wild).take(info.arity).collect();
                    v.extend_from_slice(tail);
                    v
                };
                let new_tys = {
                    let mut v = sub_tys.clone();
                    v.extend_from_slice(tail_tys);
                    v
                };
                let specialized = specialize_ctor(matrix, &info.name, info.arity);
                if is_useful(&specialized, &new_pats, &new_tys, cx) {
                    // This constructor is uncovered. Build a witness:
                    // `Ctor(_, _, ..., _)` with `arity` wildcards.
                    witnesses.push(MatchPat::Ctor {
                        name: info.name.clone(),
                        args: std::iter::repeat(MatchPat::Wild).take(info.arity).collect(),
                    });
                }
            }
            witnesses
        }
        CtorSet::Unlistable => {
            // Open universe of literals — we can't enumerate concrete
            // witnesses. If there's no wildcard arm, surface a single
            // `_` witness so the diagnostic emission layer can decide
            // whether to suppress it.
            if matrix.is_empty() {
                return vec![MatchPat::Wild];
            }
            if !matrix.iter().any(|r| matches!(&r.pats[0], MatchPat::Wild)) {
                return vec![MatchPat::Wild];
            }
            let default = default_matrix(matrix);
            collect_witnesses(&default, tail, tail_tys, cx)
        }
        CtorSet::Unknown => {
            // Type unknown at this column — refuse to invent a witness.
            // The matching `is_useful_wild` branch already prevents the
            // probe from being marked useful in this case, but we still
            // need a no-op fallback here for safety.
            if matrix.is_empty() {
                vec![MatchPat::Wild]
            } else {
                Vec::new()
            }
        }
    }
}

// =============================================================================
// Pretty-printing for diagnostics
// =============================================================================

impl MatchPat {
    /// Render a witness pattern as a short string for the user-facing
    /// diagnostic. Wildcards become `_`, constructors `Foo` or `Foo(_)`,
    /// tuples `(a, b, c)`, literals their textual form.
    pub(crate) fn display_text(&self) -> String {
        match self {
            MatchPat::Wild => "_".to_string(),
            MatchPat::Ctor { name, args } if args.is_empty() => name.clone(),
            MatchPat::Ctor { name, args } => {
                let inner = args
                    .iter()
                    .map(MatchPat::display_text)
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{name}({inner})")
            }
            MatchPat::Tuple(items) => {
                let inner = items
                    .iter()
                    .map(MatchPat::display_text)
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("({inner})")
            }
            MatchPat::Literal(key) => match key {
                LiteralKey::Bool(true) => "true".to_string(),
                LiteralKey::Bool(false) => "false".to_string(),
                LiteralKey::Unit => "()".to_string(),
                LiteralKey::Number(s)
                | LiteralKey::String(s)
                | LiteralKey::Binary(s)
                | LiteralKey::Hex(s) => s.clone(),
                LiteralKey::Undefined => "undefined".to_string(),
            },
            MatchPat::Or(branches) => branches
                .iter()
                .map(MatchPat::display_text)
                .collect::<Vec<_>>()
                .join(" | "),
        }
    }
}

// =============================================================================
// Convenience constructor adapters used by typecheck.rs
// =============================================================================

/// Lower a list of `MatchCase`s into matched `Arm`s. The caller threads
/// in a `pattern_constants` lookup so bare names get classified correctly.
pub(crate) fn lower_arms<P>(
    cases: &[Spanned<sail_parser::core_ast::MatchCase>],
    pattern_constants: &P,
) -> Vec<Arm>
where
    P: PatternConstants,
{
    cases
        .iter()
        .map(|(case, span)| Arm {
            pat: lower_pattern(&case.pattern.0, pattern_constants),
            guard_span: case.guard.as_ref().map(|g| g.1),
            arm_span: *span,
        })
        .collect()
}

/// Build a small `Cx` impl backed by hashmaps the typechecker provides.
pub(crate) struct EnvCx<'a> {
    pub enums: &'a HashMap<String, Vec<String>>,
    pub unions: &'a HashMap<String, Vec<String>>,
    pub constructor_arity: &'a HashMap<String, usize>,
}

impl<'a> Cx for EnvCx<'a> {
    fn ctors_for(&self, ty: &MatchTy) -> CtorSet {
        match ty {
            MatchTy::Bool => CtorSet::Closed(vec![
                CtorInfo {
                    name: "true".to_string(),
                    arity: 0,
                },
                CtorInfo {
                    name: "false".to_string(),
                    arity: 0,
                },
            ]),
            MatchTy::Named(name) => {
                if let Some(members) = self.enums.get(name) {
                    CtorSet::Closed(
                        members
                            .iter()
                            .map(|m| CtorInfo {
                                name: m.clone(),
                                arity: 0,
                            })
                            .collect(),
                    )
                } else if let Some(variants) = self.unions.get(name) {
                    CtorSet::Closed(
                        variants
                            .iter()
                            .map(|v| CtorInfo {
                                name: v.clone(),
                                arity: self.constructor_arity.get(v).copied().unwrap_or(0),
                            })
                            .collect(),
                    )
                } else {
                    CtorSet::Unknown
                }
            }
            MatchTy::Tuple(_) => CtorSet::Unlistable, // tuples are handled via specialize_tuple
            MatchTy::Unknown => CtorSet::Unknown,
        }
    }

    fn ctor_sub_tys(&self, name: &str, _scrutinee: &MatchTy) -> Vec<MatchTy> {
        // For the MVP we don't track variant payload types, so each
        // sub-position is Unknown. The vector length still has to match
        // the constructor arity, otherwise the pattern stack and type
        // stack go out of sync inside the matrix algorithm.
        let arity = self.constructor_arity.get(name).copied().unwrap_or(0);
        std::iter::repeat(MatchTy::Unknown).take(arity).collect()
    }
}
