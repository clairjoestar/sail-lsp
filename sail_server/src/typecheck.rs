use std::collections::{HashMap, HashSet};
use std::hash::{Hash, Hasher};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex, OnceLock};

use smallvec::SmallVec;

use crate::diagnostics::reporting::{diagnostic_for_error, Error as ReportingError};
use crate::diagnostics::type_error::{TypeError, VectorOrder};
use crate::diagnostics::{Diagnostic, DiagnosticCode, Severity};
use crate::match_check::{self, EnvCx, MatchTy};
use crate::state::File;
use crate::symbols::collect_callable_signatures;

/// Cooperative cancellation token threaded through the type checker.
///
/// The worker that schedules a typecheck can flip this to `true` when a
/// newer typecheck is queued for the same file; the in-flight checker
/// notices at the next per-definition checkpoint and bails out early
/// instead of burning CPU on a result that will be discarded.
///
/// This is a much weaker analogue of salsa's `Cancelled` exception, but
/// it's enough to keep typing latency from piling up doomed work.
#[derive(Clone, Debug, Default)]
pub struct CancellationToken {
    inner: Arc<AtomicBool>,
}

impl CancellationToken {
    pub fn new() -> Self {
        Self {
            inner: Arc::new(AtomicBool::new(false)),
        }
    }

    /// Returns a token that can never be cancelled. Tests and one-shot
    /// callers use this so they don't have to thread a real token.
    pub fn never() -> Self {
        Self::default()
    }

    pub fn cancel(&self) {
        self.inner.store(true, Ordering::Release);
    }

    pub fn is_cancelled(&self) -> bool {
        self.inner.load(Ordering::Acquire)
    }
}
use sail_parser::{
    core_ast::{
        BitfieldField, Call, CallableClause, CallableDefKind, DefinitionKind, Expr, FieldExpr,
        FieldPattern, Lexp, MappingArmDirection, MappingBody, MatchCase, NamedDefDetail,
        NamedDefKind, Pattern, SourceFile, Spanned, TypeExpr, VectorUpdate,
    },
    Literal, Span,
};

type SpanKey = (usize, usize);

/// Nullary/unary constructors from the upstream Sail standard library
/// (`sail/lib/option.sail`, `sail/lib/result.sail`). We whitelist them so
/// pattern-binding disambiguation and the unresolved-identifier check
/// don't misclassify legitimate uses just because the upstream prelude
/// isn't in the parsed corpus.
const PRELUDE_CONSTRUCTORS: &[&str] = &["None", "Some", "Ok", "Err"];

/// Compiler intrinsics handled in `sail/src/lib/initial_check.ml`; they
/// parse as bare `Expr::Ident` but are always resolved by the frontend.
const PRELUDE_INTRINSICS: &[&str] = &["__FILE__", "__LINE__"];

/// Enum members defined in upstream Sail library files that projects
/// rely on without explicitly including them. Currently just the
/// concurrency interface (`sail/lib/concurrency_interface/read_write_v1.sail`),
/// which sail-riscv references via its `phys_mem_interface.sail`.
const PRELUDE_ENUM_MEMBERS: &[&str] = &[
    // enum Access_variety
    "AV_plain",
    "AV_exclusive",
    "AV_atomic_rmw",
    // enum Access_strength
    "AS_normal",
    "AS_rel_or_acq",
    "AS_acq_rcpc",
];

/// Names that should count as defined for the workspace-aware
/// unresolved-identifier check.
fn is_prelude_value(name: &str) -> bool {
    PRELUDE_CONSTRUCTORS.contains(&name)
        || PRELUDE_INTRINSICS.contains(&name)
        || PRELUDE_ENUM_MEMBERS.contains(&name)
}

/// Type representation. The outer `Ty` is a thin newtype wrapping
/// `Arc<TyData>`, so cloning is one refcount bump regardless of how
/// large the type tree is. This is the C1 (interning) refactor: it
/// gives us cheap clones along the substitution / unification hot path
/// AND a fast-path for equality (`Arc::ptr_eq`) when two `Ty` values
/// happen to share the same allocation.
///
/// We deliberately use `kind()` instead of `Deref` so callers see the
/// indirection and can't accidentally turn `ty.clone()` into a deep
/// clone of `TyData`.
///
/// Note that `Function::ret` and `TyArg::Type` previously held
/// `Box<Ty>`. With the newtype `Ty` already containing an `Arc`,
/// the extra `Box` is redundant and has been removed.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum TyData {
    Unknown,
    Text(String),
    Var(String),
    Tuple(Vec<Ty>),
    Function {
        params: Vec<Ty>,
        ret: Ty,
    },
    App {
        name: String,
        args: Vec<TyArg>,
        text: String,
    },
}

#[derive(Clone, Debug, Eq)]
struct Ty(Arc<TyData>);

impl PartialEq for Ty {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0) || *self.0 == *other.0
    }
}

impl std::hash::Hash for Ty {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.hash(state);
    }
}

/// Tiny intern pool for the primitives every Sail program uses dozens of
/// times. Returning a shared `Arc` for these names means `Ty == Ty` on
/// `int` / `bool` / `unit` / etc. hits the `Arc::ptr_eq` fast path.
struct PrimitiveTyPool {
    unknown: Ty,
    int: Ty,
    nat: Ty,
    bool_: Ty,
    unit: Ty,
    bit: Ty,
    string: Ty,
    real: Ty,
}

fn primitive_pool() -> &'static PrimitiveTyPool {
    static POOL: OnceLock<PrimitiveTyPool> = OnceLock::new();
    POOL.get_or_init(|| PrimitiveTyPool {
        unknown: Ty(Arc::new(TyData::Unknown)),
        int: Ty(Arc::new(TyData::Text("int".to_string()))),
        nat: Ty(Arc::new(TyData::Text("nat".to_string()))),
        bool_: Ty(Arc::new(TyData::Text("bool".to_string()))),
        unit: Ty(Arc::new(TyData::Text("unit".to_string()))),
        bit: Ty(Arc::new(TyData::Text("bit".to_string()))),
        string: Ty(Arc::new(TyData::Text("string".to_string()))),
        real: Ty(Arc::new(TyData::Text("real".to_string()))),
    })
}

impl Ty {
    fn kind(&self) -> &TyData {
        &self.0
    }

    fn unknown() -> Self {
        primitive_pool().unknown.clone()
    }

    fn text<S: Into<String>>(s: S) -> Self {
        let s = s.into();
        // Hot-path interning for the seven primitives.
        let pool = primitive_pool();
        match s.as_str() {
            "int" => pool.int.clone(),
            "nat" => pool.nat.clone(),
            "bool" => pool.bool_.clone(),
            "unit" => pool.unit.clone(),
            "bit" => pool.bit.clone(),
            "string" => pool.string.clone(),
            "real" => pool.real.clone(),
            _ => Ty(Arc::new(TyData::Text(s))),
        }
    }

    fn var<S: Into<String>>(s: S) -> Self {
        Ty(Arc::new(TyData::Var(s.into())))
    }

    fn tuple(items: Vec<Ty>) -> Self {
        Ty(Arc::new(TyData::Tuple(items)))
    }

    fn function(params: Vec<Ty>, ret: Ty) -> Self {
        Ty(Arc::new(TyData::Function { params, ret }))
    }

    fn app<N: Into<String>, T: Into<String>>(name: N, args: Vec<TyArg>, text: T) -> Self {
        Ty(Arc::new(TyData::App {
            name: name.into(),
            args,
            text: text.into(),
        }))
    }
}

// Compatibility shim: `Ty::unknown()`, `Ty::text(...)`, etc. were the old
// constructor namespaces. The atomic cutover replaces them with
// `Ty::unknown()` / `Ty::text(...)` / `Ty::tuple(...)` / etc. and replaces
// every match arm with `match ty.kind() { TyData::... }`.

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum TyArg {
    // `Ty` already contains an `Arc`, so the previous `Box<Ty>` was
    // double-indirection. Folded the box.
    Type(Ty),
    Value(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct TypeScheme {
    quantifiers: Vec<String>,
    constraints: Vec<QuantConstraint>,
    params: Vec<Ty>,
    implicit_params: Vec<bool>,
    ret: Ty,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct MappingScheme {
    quantifiers: Vec<String>,
    constraints: Vec<QuantConstraint>,
    lhs: Ty,
    rhs: Ty,
}

#[derive(Clone, Debug)]
struct TopLevelEnv {
    // Schemes are stored as `Arc<Scheme>` so `lookup_*` can return cheap
    // refcount-bumped owned handles. This avoids the borrow-vs-mutate
    // dance you otherwise hit when iterating candidates while needing
    // `&mut self` to push diagnostics, and it makes per-call lookup
    // allocation-free in the common (non-overload) case.
    functions: HashMap<String, Vec<Arc<TypeScheme>>>,
    mappings: HashMap<String, Vec<Arc<MappingScheme>>>,
    overloads: HashMap<String, Vec<String>>,
    values: HashMap<String, Ty>,
    registers: HashMap<String, Ty>,
    records: HashMap<String, RecordInfo>,
    bitfields: HashMap<String, BitfieldInfo>,
    constructors: HashMap<String, Vec<Arc<TypeScheme>>>,
    /// Type-name → enum member list. `Privilege → [Machine, Supervisor, User]`.
    /// Populated from `NamedDefKind::Enum` definitions and merged with
    /// cross-file enums via `WorkspaceContext::apply_to`. Used by the
    /// pattern-exhaustiveness check to enumerate constructors per type.
    enums: HashMap<String, Vec<String>>,
    /// Type-name → union variant list. `option → [Some, None]`. Populated
    /// the same way as `enums`.
    unions: HashMap<String, Vec<String>>,
    /// Map from type alias name to its underlying type. Used to resolve
    /// cross-file aliases like `xlenbits = bits(64)` so the unify function
    /// can compare textually-different but semantically-equal types.
    type_aliases: HashMap<String, Ty>,
    /// Names of functions defined in OTHER workspace files (no schemes).
    /// Used by `infer_call` to suppress "function not found" errors when
    /// the callee exists somewhere in the workspace.
    cross_file_function_names: HashSet<String>,
    /// Names of union/enum constructors defined in other files. Used to
    /// recognize bare-identifier patterns as constructors.
    cross_file_constructor_names: HashSet<String>,
    /// Names of top-level `let`/`var`/register/enum-member bindings
    /// defined in other workspace files. Used by the unresolved-identifier
    /// check to decide whether a bare `Expr::Ident` is plausibly defined
    /// elsewhere.
    cross_file_value_names: HashSet<String>,
    /// Names of registers defined in other workspace files. Used by the
    /// unresolved-identifier check for `Expr::Ref`.
    cross_file_register_names: HashSet<String>,
    /// Cross-file callable arities: `name → [(required, total), ...]`
    /// for each `val`-declared overload variant we've seen workspace-
    /// wide. Populated by `WorkspaceContext::apply_to`. `infer_call`
    /// uses this to do *arity-only* checking on cross-file calls
    /// without invoking the unifier (which would recurse on quantified
    /// types and overflow the stack — see B1 history). Each entry is
    /// `(required_args, total_args_including_implicits)`, matching the
    /// shape of the local `count_mismatch` check.
    cross_file_function_arity: HashMap<String, Vec<(usize, usize)>>,
    /// Names of bitfield/struct fields visible in the current workspace.
    /// These appear as bare `Expr::Ident`s inside the synthetic
    /// `vector_access#(base, field)` call that lowered `v[field]`, so the
    /// unresolved-identifier check would otherwise flag them. Populated
    /// from both the local file and the workspace pass.
    known_field_names: HashSet<String>,
    /// True iff this env was built with `check_file_with_workspace`, i.e.
    /// the cross_file_* sets reflect the full workspace. The strict
    /// unresolved-identifier check only runs when this is true, so that
    /// single-file mode (which has no cross-file knowledge) stays lenient.
    has_workspace_context: bool,
    global_constraints: Vec<ConstraintExpr>,
    vector_order: VectorOrder,
}

#[derive(Clone, Debug, Default)]
struct RecordInfo {
    params: Vec<String>,
    fields: HashMap<String, Ty>,
}

#[derive(Clone, Debug)]
struct BitfieldInfo {
    underlying: Ty,
    fields: HashMap<String, Ty>,
}

#[derive(Clone, Debug, Default)]
struct LocalEnv {
    /// Flat binding map — single HashMap for O(1) lookup instead of O(scope_depth).
    bindings: HashMap<String, Ty>,
    expected_return: Option<Ty>,
    constraints: Vec<ConstraintExpr>,
    undo_log: Vec<LocalEnvUndo>,
}

#[derive(Clone, Debug)]
enum LocalEnvUndo {
    PushScope,
    Define {
        name: String,
        previous: Option<Ty>,
    },
    AddConstraint,
}

/// Substitution maps generated by `unify` and consumed by `apply_subst`.
///
/// Sail substitutions almost always have ≤ 4 entries (a function takes a
/// handful of type / numeric parameters), so a hashmap is the wrong data
/// structure: it dwarfs the actual content with hash state and pays
/// allocator cost on every `Subst::default()` call. We back the maps with
/// `SmallVec<[_; 8]>` so the common case never touches the heap; the
/// linear search is faster than `HashMap::get` for those sizes anyway.
///
/// The two inner fields are kept as named structs (`SubstTypes`,
/// `SubstValues`) so existing call sites that use `subst.types.insert(...)`
/// / `subst.values.get(...)` keep working unchanged — only the underlying
/// representation changed, not the surface API.
#[derive(Clone, Debug, Default)]
struct Subst {
    types: SubstTypes,
    values: SubstValues,
}

#[derive(Clone, Debug, Default)]
struct SubstTypes {
    entries: SmallVec<[(String, Ty); 8]>,
}

impl SubstTypes {
    fn insert(&mut self, key: String, value: Ty) -> Option<Ty> {
        for entry in &mut self.entries {
            if entry.0 == key {
                let old = std::mem::replace(&mut entry.1, value);
                return Some(old);
            }
        }
        self.entries.push((key, value));
        None
    }

    fn get(&self, key: &str) -> Option<&Ty> {
        self.entries
            .iter()
            .find_map(|(k, v)| if k == key { Some(v) } else { None })
    }

    fn contains_key(&self, key: &str) -> bool {
        self.entries.iter().any(|(k, _)| k == key)
    }
}

#[derive(Clone, Debug, Default)]
struct SubstValues {
    entries: SmallVec<[(String, String); 8]>,
}

impl SubstValues {
    fn insert(&mut self, key: String, value: String) -> Option<String> {
        for entry in &mut self.entries {
            if entry.0 == key {
                let old = std::mem::replace(&mut entry.1, value);
                return Some(old);
            }
        }
        self.entries.push((key, value));
        None
    }

    fn get(&self, key: &str) -> Option<&String> {
        self.entries
            .iter()
            .find_map(|(k, v)| if k == key { Some(v) } else { None })
    }

    fn contains_key(&self, key: &str) -> bool {
        self.entries.iter().any(|(k, _)| k == key)
    }

    #[cfg(test)]
    fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TargetAssignmentKind {
    Declaration,
    Update,
    Mixed,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct QuantConstraint {
    text: String,
    mentions: Vec<String>,
    expr: ConstraintExpr,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum ConstraintExpr {
    Bool(bool),
    Compare {
        lhs: NumericExpr,
        op: CompareOp,
        rhs: NumericExpr,
    },
    InSet {
        value: NumericExpr,
        items: Vec<NumericExpr>,
    },
    And(Vec<ConstraintExpr>),
    Or(Vec<ConstraintExpr>),
    Not(Box<ConstraintExpr>),
    Unsupported,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CompareOp {
    Eq,
    Neq,
    Lt,
    Lte,
    Gt,
    Gte,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum NumericExpr {
    Const(i64),
    Var(String),
    Symbol(String),
    Neg(Box<NumericExpr>),
    Add(Box<NumericExpr>, Box<NumericExpr>),
    Sub(Box<NumericExpr>, Box<NumericExpr>),
    Mul(Box<NumericExpr>, Box<NumericExpr>),
    Div(Box<NumericExpr>, Box<NumericExpr>),
    Mod(Box<NumericExpr>, Box<NumericExpr>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ConstraintStatus {
    Satisfied,
    Failed,
    Unknown,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct NumericBound {
    value: i64,
    inclusive: bool,
}

#[derive(Clone, Debug, Default)]
struct ConstraintFacts {
    lower: Option<NumericBound>,
    upper: Option<NumericBound>,
    exact_values: Option<HashSet<i64>>,
    excluded_values: HashSet<i64>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ArithmeticOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
}

impl Default for TopLevelEnv {
    fn default() -> Self {
        Self {
            functions: HashMap::new(),
            mappings: HashMap::new(),
            overloads: HashMap::new(),
            values: HashMap::new(),
            registers: HashMap::new(),
            records: HashMap::new(),
            bitfields: HashMap::new(),
            constructors: HashMap::new(),
            enums: HashMap::new(),
            unions: HashMap::new(),
            type_aliases: HashMap::new(),
            cross_file_function_names: HashSet::new(),
            cross_file_constructor_names: HashSet::new(),
            cross_file_value_names: HashSet::new(),
            cross_file_register_names: HashSet::new(),
            cross_file_function_arity: HashMap::new(),
            known_field_names: HashSet::new(),
            has_workspace_context: false,
            global_constraints: Vec::new(),
            vector_order: VectorOrder::Dec,
        }
    }
}

#[derive(Clone, Debug, Default)]
pub(crate) struct TypeCheckResult {
    diagnostics: Vec<Diagnostic>,
    expr_types: HashMap<SpanKey, String>,
    binding_types: HashMap<SpanKey, String>,
}

impl TypeCheckResult {
    pub(crate) fn diagnostics(&self) -> &[Diagnostic] {
        &self.diagnostics
    }

    pub(crate) fn expr_type_text(&self, span: Span) -> Option<&str> {
        self.expr_types
            .get(&(span.start, span.end))
            .map(String::as_str)
    }

    pub(crate) fn binding_type_text(&self, span: Span) -> Option<&str> {
        self.binding_types
            .get(&(span.start, span.end))
            .map(String::as_str)
    }
}

impl Ty {
    /// Render this type as a textual form for diagnostics.
    fn display_text(&self) -> String {
        match self.kind() {
            TyData::Unknown => "_".to_string(),
            TyData::Text(text) => text.clone(),
            TyData::Var(name) => name.clone(),
            TyData::Tuple(items) => format!(
                "({})",
                items
                    .iter()
                    .map(Ty::display_text)
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            TyData::Function { params, ret } => {
                let params = if params.len() == 1 {
                    params[0].display_text()
                } else {
                    format!(
                        "({})",
                        params
                            .iter()
                            .map(Ty::display_text)
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                };
                format!("{params} -> {}", ret.display_text())
            }
            TyData::App { text, .. } => text.clone(),
        }
    }

    fn is_unknown(&self) -> bool {
        matches!(self.kind(), TyData::Unknown)
    }
}

fn expr_kind_name(expr: &Expr) -> &'static str {
    match expr {
        Expr::Attribute { .. } => "attribute",
        Expr::Assign { .. } => "assign",
        Expr::Let { .. } => "let",
        Expr::Var { .. } => "var",
        Expr::Block(_) => "block",
        Expr::Return(_) => "return",
        Expr::Throw(_) => "throw",
        Expr::Assert { .. } => "assert",
        Expr::Exit(_) => "exit",
        Expr::If { .. } => "if",
        Expr::Match { .. } => "match",
        Expr::Try { .. } => "try",
        Expr::Foreach(_) => "foreach",
        Expr::Repeat { .. } => "repeat",
        Expr::While { .. } => "while",
        Expr::Infix { .. } => "infix",
        Expr::Prefix { .. } => "prefix",
        Expr::Cast { .. } => "cast",
        Expr::Config(_) => "config",
        Expr::Literal(_) => "literal",
        Expr::Ident(_) => "ident",
        Expr::TypeVar(_) => "type-var",
        Expr::Ref(_) => "ref",
        Expr::Call(_) => "call",
        Expr::Field { .. } => "field",
        Expr::SizeOf(_) => "sizeof",
        Expr::Constraint(_) => "constraint",
        Expr::Struct { .. } => "struct",
        Expr::Update { .. } => "update",
        Expr::List(_) => "list",
        Expr::Vector(_) => "vector",
        Expr::Tuple(_) => "tuple",
        Expr::Error(_) => "error",
    }
}

impl LocalEnv {
    fn new(expected_return: Option<Ty>) -> Self {
        Self {
            bindings: HashMap::new(),
            expected_return,
            constraints: Vec::new(),
            undo_log: Vec::new(),
        }
    }

    fn snapshot(&self) -> usize {
        self.undo_log.len()
    }

    fn restore(&mut self, mark: usize) {
        while self.undo_log.len() > mark {
            match self.undo_log.pop().expect("undo log length checked") {
                LocalEnvUndo::PushScope => {}
                LocalEnvUndo::Define { name, previous } => {
                    if let Some(previous) = previous {
                        self.bindings.insert(name, previous);
                    } else {
                        self.bindings.remove(&name);
                    }
                }
                LocalEnvUndo::AddConstraint => {
                    self.constraints.pop();
                }
            }
        }
    }

    fn push_scope(&mut self) {
        self.undo_log.push(LocalEnvUndo::PushScope);
    }

    fn pop_scope(&mut self) {
        if let Some(mark) = self
            .undo_log
            .iter()
            .rposition(|entry| matches!(entry, LocalEnvUndo::PushScope))
        {
            self.restore(mark);
        }
    }

    fn define(&mut self, name: &str, ty: Ty) {
        let name = name.to_string();
        let previous = self.bindings.insert(name.clone(), ty);
        self.undo_log.push(LocalEnvUndo::Define { name, previous });
    }

    fn add_constraint(&mut self, constraint: ConstraintExpr) {
        self.constraints.push(constraint);
        self.undo_log.push(LocalEnvUndo::AddConstraint);
    }

    fn lookup(&self, name: &str) -> Option<&Ty> {
        self.bindings.get(name)
    }
}

fn span_text<'a>(source: &'a str, span: Span) -> &'a str {
    source[span.start..span.end].trim()
}

fn type_arg_from_type_expr(source: &str, ty: &Spanned<TypeExpr>) -> TyArg {
    match &ty.0 {
        TypeExpr::Named(_)
        | TypeExpr::TypeVar(_)
        | TypeExpr::App { .. }
        | TypeExpr::Tuple(_)
        | TypeExpr::Arrow { .. }
        | TypeExpr::Register(_)
        | TypeExpr::Effect { .. }
        | TypeExpr::Forall { .. }
        | TypeExpr::Existential { .. } => TyArg::Type(type_from_type_expr(source, ty)),
        _ => TyArg::Value(span_text(source, ty.1).to_string()),
    }
}

fn type_from_type_expr(source: &str, ty: &Spanned<TypeExpr>) -> Ty {
    match &ty.0 {
        TypeExpr::Named(name) => Ty::text(name.clone()),
        TypeExpr::TypeVar(name) => Ty::var(name.clone()),
        TypeExpr::Tuple(items) => Ty::tuple(
            items
                .iter()
                .map(|item| type_from_type_expr(source, item))
                .collect(),
        ),
        TypeExpr::Arrow { params, ret, .. } => Ty::function(
            params
                .iter()
                .map(|item| type_from_type_expr(source, item))
                .collect(),
            type_from_type_expr(source, ret),
        ),
        TypeExpr::App { callee, args } => Ty::app(
            callee.0.clone(),
            args.iter()
                .map(|arg| type_arg_from_type_expr(source, arg))
                .collect(),
            span_text(source, ty.1).to_string(),
        ),
        TypeExpr::Register(inner) => Ty::app(
            "register",
            vec![TyArg::Type(type_from_type_expr(source, inner))],
            span_text(source, ty.1).to_string(),
        ),
        TypeExpr::Effect { ty: inner, .. } => type_from_type_expr(source, inner),
        TypeExpr::Forall { body, .. } => type_from_type_expr(source, body),
        TypeExpr::Existential { body, .. } => type_from_type_expr(source, body),
        _ => Ty::text(span_text(source, ty.1).to_string()),
    }
}

fn collect_type_vars_in_type_expr(ty: &Spanned<TypeExpr>, out: &mut HashSet<String>) {
    match &ty.0 {
        TypeExpr::TypeVar(name) => {
            out.insert(name.clone());
        }
        TypeExpr::Forall {
            vars,
            constraint,
            body,
        } => {
            for var in vars {
                out.insert(var.name.0.clone());
            }
            if let Some(constraint) = constraint {
                collect_type_vars_in_type_expr(constraint, out);
            }
            collect_type_vars_in_type_expr(body, out);
        }
        TypeExpr::Existential {
            binder,
            constraint,
            body,
        } => {
            out.insert(binder.name.0.clone());
            if let Some(constraint) = constraint {
                collect_type_vars_in_type_expr(constraint, out);
            }
            collect_type_vars_in_type_expr(body, out);
        }
        TypeExpr::Effect { ty, .. } | TypeExpr::Register(ty) | TypeExpr::Prefix { ty, .. } => {
            collect_type_vars_in_type_expr(ty, out)
        }
        TypeExpr::App { args, .. } | TypeExpr::Tuple(args) | TypeExpr::Set(args) => {
            for arg in args {
                collect_type_vars_in_type_expr(arg, out);
            }
        }
        TypeExpr::Infix { lhs, rhs, .. } => {
            collect_type_vars_in_type_expr(lhs, out);
            collect_type_vars_in_type_expr(rhs, out);
        }
        TypeExpr::Conditional {
            cond,
            then_ty,
            else_ty,
        } => {
            collect_type_vars_in_type_expr(cond, out);
            collect_type_vars_in_type_expr(then_ty, out);
            collect_type_vars_in_type_expr(else_ty, out);
        }
        TypeExpr::Arrow { params, ret, .. } => {
            for param in params {
                collect_type_vars_in_type_expr(param, out);
            }
            collect_type_vars_in_type_expr(ret, out);
        }
        TypeExpr::Wild
        | TypeExpr::Named(_)
        | TypeExpr::Literal(_)
        | TypeExpr::Dec
        | TypeExpr::Inc
        | TypeExpr::Config(_)
        | TypeExpr::Error(_) => {}
    }
}

fn compare_op_from_str(op: &str) -> Option<CompareOp> {
    match op {
        "=" | "==" => Some(CompareOp::Eq),
        "!=" | "<>" => Some(CompareOp::Neq),
        "<" => Some(CompareOp::Lt),
        "<=" => Some(CompareOp::Lte),
        ">" => Some(CompareOp::Gt),
        ">=" => Some(CompareOp::Gte),
        _ => None,
    }
}

fn arithmetic_op_from_str(op: &str) -> Option<ArithmeticOp> {
    match op {
        "+" => Some(ArithmeticOp::Add),
        "-" => Some(ArithmeticOp::Sub),
        "*" => Some(ArithmeticOp::Mul),
        "/" => Some(ArithmeticOp::Div),
        "%" => Some(ArithmeticOp::Mod),
        _ => None,
    }
}

fn numeric_expr_from_type_expr(source: &str, ty: &Spanned<TypeExpr>) -> Option<NumericExpr> {
    match &ty.0 {
        TypeExpr::TypeVar(name) => Some(NumericExpr::Var(name.clone())),
        TypeExpr::Literal(text) | TypeExpr::Named(text) => parse_int_literal(text)
            .map(NumericExpr::Const)
            .or_else(|| Some(NumericExpr::Symbol(text.clone()))),
        TypeExpr::Prefix { op, ty } if op.0 == "-" => Some(NumericExpr::Neg(Box::new(
            numeric_expr_from_type_expr(source, ty)?,
        ))),
        TypeExpr::Infix { lhs, op, rhs } => {
            let op = arithmetic_op_from_str(&op.0)?;
            let lhs = numeric_expr_from_type_expr(source, lhs)?;
            let rhs = numeric_expr_from_type_expr(source, rhs)?;
            Some(match op {
                ArithmeticOp::Add => NumericExpr::Add(Box::new(lhs), Box::new(rhs)),
                ArithmeticOp::Sub => NumericExpr::Sub(Box::new(lhs), Box::new(rhs)),
                ArithmeticOp::Mul => NumericExpr::Mul(Box::new(lhs), Box::new(rhs)),
                ArithmeticOp::Div => NumericExpr::Div(Box::new(lhs), Box::new(rhs)),
                ArithmeticOp::Mod => NumericExpr::Mod(Box::new(lhs), Box::new(rhs)),
            })
        }
        TypeExpr::Error(_) => None,
        _ => Some(NumericExpr::Symbol(span_text(source, ty.1).to_string())),
    }
}

fn comparison_constraint(
    source: &str,
    lhs: &Spanned<TypeExpr>,
    op: &str,
    rhs: &Spanned<TypeExpr>,
) -> Option<ConstraintExpr> {
    let op = compare_op_from_str(op)?;
    Some(ConstraintExpr::Compare {
        lhs: numeric_expr_from_type_expr(source, lhs)?,
        op,
        rhs: numeric_expr_from_type_expr(source, rhs)?,
    })
}

fn chained_comparison_constraint(
    source: &str,
    lhs: &Spanned<TypeExpr>,
    op: &str,
    rhs: &Spanned<TypeExpr>,
) -> Option<ConstraintExpr> {
    let TypeExpr::Infix {
        lhs: chain_lhs,
        op: chain_op,
        rhs: chain_rhs,
    } = &lhs.0
    else {
        return None;
    };
    let first = comparison_constraint(source, chain_lhs, &chain_op.0, chain_rhs)?;
    let second = comparison_constraint(source, chain_rhs, op, rhs)?;
    Some(ConstraintExpr::And(vec![first, second]))
}

fn constraint_expr_from_type_expr(source: &str, ty: &Spanned<TypeExpr>) -> ConstraintExpr {
    match &ty.0 {
        TypeExpr::Literal(text) | TypeExpr::Named(text) if text == "true" => {
            ConstraintExpr::Bool(true)
        }
        TypeExpr::Literal(text) | TypeExpr::Named(text) if text == "false" => {
            ConstraintExpr::Bool(false)
        }
        TypeExpr::Prefix { op, ty } if op.0 == "not" => {
            ConstraintExpr::Not(Box::new(constraint_expr_from_type_expr(source, ty)))
        }
        TypeExpr::Infix { lhs, op, rhs } => match op.0.as_str() {
            "and" | "&" => ConstraintExpr::And(vec![
                constraint_expr_from_type_expr(source, lhs),
                constraint_expr_from_type_expr(source, rhs),
            ]),
            "or" | "|" => ConstraintExpr::Or(vec![
                constraint_expr_from_type_expr(source, lhs),
                constraint_expr_from_type_expr(source, rhs),
            ]),
            "in" => match &rhs.0 {
                TypeExpr::Set(items) => {
                    let value = numeric_expr_from_type_expr(source, lhs);
                    let items = items
                        .iter()
                        .map(|item| numeric_expr_from_type_expr(source, item))
                        .collect::<Option<Vec<_>>>();
                    match (value, items) {
                        (Some(value), Some(items)) => ConstraintExpr::InSet { value, items },
                        _ => ConstraintExpr::Unsupported,
                    }
                }
                _ => ConstraintExpr::Unsupported,
            },
            op if compare_op_from_str(op).is_some() => {
                chained_comparison_constraint(source, lhs, op, rhs)
                    .or_else(|| comparison_constraint(source, lhs, op, rhs))
                    .unwrap_or(ConstraintExpr::Unsupported)
            }
            _ => ConstraintExpr::Unsupported,
        },
        _ => ConstraintExpr::Unsupported,
    }
}

fn quant_constraint_from_type_expr(source: &str, ty: &Spanned<TypeExpr>) -> QuantConstraint {
    let mut mentions = HashSet::new();
    collect_type_vars_in_type_expr(ty, &mut mentions);
    let mut mentions = mentions.into_iter().collect::<Vec<_>>();
    mentions.sort();
    QuantConstraint {
        text: span_text(source, ty.1).to_string(),
        mentions,
        expr: constraint_expr_from_type_expr(source, ty),
    }
}

fn collect_forall_quantifiers_and_constraints<'a>(
    source: &str,
    ty: &'a Spanned<TypeExpr>,
) -> (Vec<String>, Vec<QuantConstraint>, &'a Spanned<TypeExpr>) {
    let mut quantifiers = Vec::new();
    let mut constraints = Vec::new();
    let mut current = ty;
    loop {
        match &current.0 {
            TypeExpr::Forall {
                vars,
                constraint,
                body,
            } => {
                quantifiers.extend(vars.iter().map(|var| var.name.0.clone()));
                if let Some(constraint) = constraint {
                    constraints.push(quant_constraint_from_type_expr(source, constraint));
                }
                current = body;
            }
            TypeExpr::Effect { ty, .. } => current = ty,
            _ => break,
        }
    }
    (quantifiers, constraints, current)
}

fn type_param_spec_quantifiers_and_constraints(
    source: &str,
    params: Option<&Spanned<sail_parser::core_ast::TypeParamSpec>>,
) -> (Vec<String>, Vec<QuantConstraint>) {
    let Some(params) = params else {
        return (Vec::new(), Vec::new());
    };
    let quantifiers = params
        .0
        .params
        .iter()
        .map(|param| param.name.0.clone())
        .collect::<Vec<_>>();
    let constraints = match &params.0.tail {
        Some(sail_parser::core_ast::TypeParamTail::Constraint(ty)) => {
            vec![quant_constraint_from_type_expr(source, ty)]
        }
        _ => Vec::new(),
    };
    (quantifiers, constraints)
}

/// Detect Sail's `implicit('n)` parameter marker. The parser represents
/// this as `Ty::App { name: "implicit", .. }`.
fn ty_is_implicit(ty: &Ty) -> bool {
    matches!(ty.kind(), TyData::App { name, .. } if name == "implicit")
}

fn scheme_from_type_expr(source: &str, ty: &Spanned<TypeExpr>) -> TypeScheme {
    let (quantifiers, constraints, current) =
        collect_forall_quantifiers_and_constraints(source, ty);
    let parsed = type_from_type_expr(source, current);
    match parsed.kind() {
        TyData::Function { params, ret } => {
            // A Sail signature like `(implicit('n), bits('n)) -> bits('n)`
            // is parsed as a single tuple param. Flatten it so that
            // arity-checking and per-element unification work the same
            // way the local-file path does. Also flag the implicit
            // positions so the call-site filter can drop them when the
            // caller doesn't pass them explicitly.
            let ret = ret.clone();
            let (params, implicit_params) = if params.len() == 1 {
                if let TyData::Tuple(items) = params[0].kind() {
                    let implicit = items.iter().map(ty_is_implicit).collect::<Vec<_>>();
                    (items.clone(), implicit)
                } else {
                    let implicit = params.iter().map(ty_is_implicit).collect::<Vec<_>>();
                    (params.clone(), implicit)
                }
            } else {
                let implicit = params.iter().map(ty_is_implicit).collect::<Vec<_>>();
                (params.clone(), implicit)
            };
            TypeScheme {
                quantifiers,
                constraints,
                params,
                implicit_params,
                ret,
            }
        }
        _ => TypeScheme {
            quantifiers,
            constraints,
            params: Vec::new(),
            implicit_params: Vec::new(),
            ret: parsed,
        },
    }
}

fn mapping_from_type_expr(source: &str, ty: &Spanned<TypeExpr>) -> Option<MappingScheme> {
    let (quantifiers, constraints, current) =
        collect_forall_quantifiers_and_constraints(source, ty);

    match &current.0 {
        TypeExpr::Arrow {
            params, ret, kind, ..
        } if matches!(kind, sail_parser::TypeArrowKind::Mapping) => {
            let lhs = match params.as_slice() {
                [param] => type_from_type_expr(source, param),
                _ => Ty::tuple(
                    params
                        .iter()
                        .map(|param| type_from_type_expr(source, param))
                        .collect(),
                ),
            };
            Some(MappingScheme {
                quantifiers,
                constraints,
                lhs,
                rhs: type_from_type_expr(source, ret),
            })
        }
        _ => None,
    }
}

/// Returns true only if `ty` is something we KNOW cannot be a record/bitfield
/// (e.g. int, bool, bits(N), etc.). Returns false for cross-file type
/// aliases or otherwise-unknown type names — those should NOT be flagged as
/// "not a record" because we can't tell.
fn is_known_non_record(ty: &Ty) -> bool {
    match ty.kind() {
        TyData::Unknown | TyData::Var(_) => false,
        TyData::Function { .. } => true,
        TyData::Tuple(_) => true,
        TyData::Text(name) => matches!(
            name.as_str(),
            "int" | "nat" | "bool" | "string" | "unit" | "real" | "bit"
        ),
        TyData::App { name, .. } => matches!(
            name.as_str(),
            "bits" | "vector" | "list" | "range" | "atom"
        ),
    }
}

/// Decides whether `name` in a pattern position should be treated as a
/// variable binding (`true`) or as a nullary constructor match (`false`).
///
/// When `workspace_known_constructors` is true, `pattern_constants` is the
/// authoritative list of every constructor visible to the current file
/// (local + cross-file + upstream prelude), so we trust it completely: if
/// the name isn't in the set, it must be a binding. Without that guarantee
/// we fall back on the uppercase-is-constructor convention to avoid
/// spurious "Duplicate binding for Data" errors from upstream constructors
/// the single-file checker can't see.
fn is_pattern_binding(
    name: &str,
    pattern_constants: &HashSet<String>,
    workspace_known_constructors: bool,
) -> bool {
    if pattern_constants.contains(name) {
        return false;
    }
    if PRELUDE_CONSTRUCTORS.contains(&name) {
        return false;
    }
    if !workspace_known_constructors
        && name.chars().next().is_some_and(|c| c.is_ascii_uppercase())
    {
        return false;
    }
    true
}

impl TopLevelEnv {
    fn from_ast(source: &str, ast: &SourceFile) -> (Self, HashSet<String>) {
        let mut env = Self::default();
        let mut pattern_constants = HashSet::new();

        for (item, _) in &ast.defs {
            match &item.kind {
                DefinitionKind::CallableSpec(spec) => match spec.kind {
                    sail_parser::CallableSpecKind::Mapping => {
                        if let Some(mapping) = mapping_from_type_expr(source, &spec.signature) {
                            env.mappings
                                .entry(spec.name.0.clone())
                                .or_default()
                                .push(Arc::new(mapping));
                        }
                    }
                    _ => {
                        env.functions
                            .entry(spec.name.0.clone())
                            .or_default()
                            .push(Arc::new(scheme_from_type_expr(source, &spec.signature)));
                    }
                },
                DefinitionKind::Callable(def) => match def.kind {
                    CallableDefKind::Mapping | CallableDefKind::MappingClause => {
                        if let Some(signature) = &def.signature {
                            if let Some(mapping) = mapping_from_type_expr(source, signature) {
                                env.mappings
                                    .entry(def.name.0.clone())
                                    .or_default()
                                    .push(Arc::new(mapping));
                            }
                        }
                    }
                    _ => {
                        if let Some(signature) = &def.signature {
                            env.functions
                                .entry(def.name.0.clone())
                                .or_default()
                                .push(Arc::new(scheme_from_type_expr(source, signature)));
                        } else if !env.functions.contains_key(&def.name.0) {
                            if let Some(scheme) = scheme_from_callable_head(source, def) {
                                env.functions
                                    .entry(def.name.0.clone())
                                    .or_default()
                                    .push(Arc::new(scheme));
                            }
                        }
                    }
                },
                DefinitionKind::Named(def) => match def.kind {
                    NamedDefKind::Overload => {
                        env.overloads
                            .entry(def.name.0.clone())
                            .or_default()
                            .extend(def.members.iter().map(|member| member.0.clone()));
                    }
                    NamedDefKind::Struct => {
                        if let Some(NamedDefDetail::Struct { fields }) = &def.detail {
                            for field in fields {
                                env.known_field_names.insert(field.0.name.0.clone());
                            }
                            env.records.insert(
                                def.name.0.clone(),
                                RecordInfo {
                                    params: def
                                        .params
                                        .as_ref()
                                        .map(|params| {
                                            params
                                                .0
                                                .params
                                                .iter()
                                                .map(|param| param.name.0.clone())
                                                .collect()
                                        })
                                        .unwrap_or_default(),
                                    fields: fields
                                        .iter()
                                        .map(|field| {
                                            (
                                                field.0.name.0.clone(),
                                                type_from_type_expr(source, &field.0.ty),
                                            )
                                        })
                                        .collect(),
                                },
                            );
                        }
                    }
                    NamedDefKind::Bitfield => {
                        if let Some(info) = bitfield_info_from_definition(source, def) {
                            let field_entries = info
                                .fields
                                .iter()
                                .map(|(name, ty)| (name.clone(), ty.clone()))
                                .collect::<Vec<_>>();
                            for (field_name, _) in &field_entries {
                                env.known_field_names.insert(field_name.clone());
                            }
                            env.bitfields.insert(def.name.0.clone(), info.clone());
                            for (field_name, field_ty) in field_entries {
                                synthesize_bitfield_accessors(
                                    &mut env,
                                    &def.name.0,
                                    &field_name,
                                    field_ty,
                                );
                            }
                            synthesize_bitfield_accessors(
                                &mut env,
                                &def.name.0,
                                "bits",
                                info.underlying,
                            );
                        }
                    }
                    NamedDefKind::Union => {
                        if let Some(NamedDefDetail::Union { variants }) = &def.detail {
                            let mut variant_names = Vec::with_capacity(variants.len());
                            for variant in variants {
                                env.constructors
                                    .entry(variant.0.name.0.clone())
                                    .or_default()
                                    .push(Arc::new(scheme_from_union_variant(
                                        source, def, &variant.0,
                                    )));
                                variant_names.push(variant.0.name.0.clone());
                            }
                            env.unions
                                .entry(def.name.0.clone())
                                .or_default()
                                .extend(variant_names);
                        }
                    }
                    NamedDefKind::Enum => {
                        let enum_entry = env
                            .enums
                            .entry(def.name.0.clone())
                            .or_default();
                        for member in &def.members {
                            pattern_constants.insert(member.0.clone());
                            env.values
                                .insert(member.0.clone(), Ty::text(def.name.0.clone()));
                            if !enum_entry.contains(&member.0) {
                                enum_entry.push(member.0.clone());
                            }
                        }
                    }
                    NamedDefKind::Register => {
                        if let Some(ty) = &def.ty {
                            let ty = type_from_type_expr(source, ty);
                            env.values.insert(def.name.0.clone(), ty.clone());
                            env.registers.insert(def.name.0.clone(), ty);
                        }
                    }
                    NamedDefKind::Let | NamedDefKind::Var => {
                        // Record the binding even without a type annotation
                        // so `top_level_symbol_exists` (and `lookup_value`)
                        // knows it's a defined name. Common case: sail-riscv's
                        // `let xlen = sizeof(xlen)` in core/xlen.sail.
                        let ty = def
                            .ty
                            .as_ref()
                            .map(|t| type_from_type_expr(source, t))
                            .unwrap_or(Ty::unknown());
                        env.values.insert(def.name.0.clone(), ty);
                    }
                    _ => {}
                },
                DefinitionKind::ScatteredClause(def)
                    if matches!(def.kind, sail_parser::ScatteredClauseKind::Enum) =>
                {
                    pattern_constants.insert(def.member.0.clone());
                    env.values
                        .insert(def.member.0.clone(), Ty::text(def.name.0.clone()));
                    let entry = env.enums.entry(def.name.0.clone()).or_default();
                    if !entry.contains(&def.member.0) {
                        entry.push(def.member.0.clone());
                    }
                }
                DefinitionKind::Default(def)
                    if def.kind.0 == "Order" && def.direction.0.eq_ignore_ascii_case("inc") =>
                {
                    env.vector_order = VectorOrder::Inc;
                }
                DefinitionKind::Default(def)
                    if def.kind.0 == "Order" && def.direction.0.eq_ignore_ascii_case("dec") =>
                {
                    env.vector_order = VectorOrder::Dec;
                }
                DefinitionKind::Constraint(def) if !def.is_type_constraint => {
                    env.global_constraints
                        .push(constraint_expr_from_type_expr(source, &def.ty));
                }
                DefinitionKind::TypeAlias(def) => {
                    if let Some(target) = &def.target {
                        let underlying = type_from_type_expr(source, target);
                        env.type_aliases
                            .insert(def.name.0.clone(), underlying);
                    }
                }
                _ => {}
            }
        }

        (env, pattern_constants)
    }

    /// Resolve a type alias chain to its underlying type. Stops at the first
    /// non-alias type or when a cycle is detected. Returns the original type
    /// if it isn't an alias.
    fn resolve_alias(&self, ty: &Ty) -> Ty {
        let mut current = ty.clone();
        let mut seen: HashSet<String> = HashSet::new();
        loop {
            let name_to_resolve = match current.kind() {
                TyData::Text(name) => name.clone(),
                TyData::App { name, .. } => name.clone(),
                _ => return current,
            };
            if !seen.insert(name_to_resolve.clone()) {
                return current;
            }
            match self.type_aliases.get(&name_to_resolve) {
                Some(underlying) => current = underlying.clone(),
                None => return current,
            }
        }
    }

    /// Returns true if `name` is a plausible top-level symbol in the
    /// current env — local file definitions, aggregated cross-file names,
    /// or a well-known upstream prelude name. Used by the strict
    /// unresolved-identifier check; intentionally permissive (we'd rather
    /// miss a bug than emit a false positive).
    fn top_level_symbol_exists(&self, name: &str) -> bool {
        if is_prelude_value(name) {
            return true;
        }
        self.values.contains_key(name)
            || self.functions.contains_key(name)
            || self.constructors.contains_key(name)
            || self.registers.contains_key(name)
            || self.records.contains_key(name)
            || self.bitfields.contains_key(name)
            || self.type_aliases.contains_key(name)
            || self.overloads.contains_key(name)
            || self.cross_file_function_names.contains(name)
            || self.cross_file_constructor_names.contains(name)
            || self.cross_file_value_names.contains(name)
            || self.cross_file_register_names.contains(name)
            || self.known_field_names.contains(name)
    }

    fn lookup_value(&self, locals: &LocalEnv, name: &str) -> Option<Ty> {
        locals
            .lookup(name)
            .cloned()
            .or_else(|| self.values.get(name).cloned())
            .or_else(|| {
                let schemes = self.functions.get(name)?;
                if schemes.len() == 1 {
                    Some(Ty::function(
                        schemes[0].params.clone(),
                        schemes[0].ret.clone(),
                    ))
                } else {
                    None
                }
            })
            .or_else(|| {
                let schemes = self.constructors.get(name)?;
                if schemes.len() == 1 {
                    Some(Ty::function(
                        schemes[0].params.clone(),
                        schemes[0].ret.clone(),
                    ))
                } else {
                    None
                }
            })
    }

    /// Resolve every callable scheme matching `name` from this env. Each
    /// returned `Arc<TypeScheme>` is a refcount bump — no scheme data is
    /// copied. The SmallVec stays on the stack in the common single- or
    /// few-overload case, so the result is also allocation-free.
    fn lookup_functions(&self, name: &str) -> SmallVec<[Arc<TypeScheme>; 4]> {
        let mut out: SmallVec<[Arc<TypeScheme>; 4]> = SmallVec::new();
        if let Some(members) = self.overloads.get(name) {
            for member in members {
                if let Some(schemes) = self.functions.get(member) {
                    out.extend(schemes.iter().cloned());
                }
            }
            return out;
        }
        if let Some(schemes) = self.functions.get(name) {
            out.extend(schemes.iter().cloned());
        }
        if let Some(schemes) = self.constructors.get(name) {
            out.extend(schemes.iter().cloned());
        }
        out
    }

    fn lookup_constructors(&self, name: &str) -> SmallVec<[Arc<TypeScheme>; 4]> {
        let mut out: SmallVec<[Arc<TypeScheme>; 4]> = SmallVec::new();
        if let Some(schemes) = self.constructors.get(name) {
            out.extend(schemes.iter().cloned());
        }
        out
    }

    fn lookup_mappings(&self, name: &str) -> SmallVec<[Arc<MappingScheme>; 4]> {
        let mut out: SmallVec<[Arc<MappingScheme>; 4]> = SmallVec::new();
        if let Some(schemes) = self.mappings.get(name) {
            out.extend(schemes.iter().cloned());
        }
        out
    }
}

fn scheme_from_union_variant(
    source: &str,
    def: &sail_parser::core_ast::NamedDefinition,
    variant: &sail_parser::core_ast::UnionVariant,
) -> TypeScheme {
    let (quantifiers, constraints) =
        type_param_spec_quantifiers_and_constraints(source, def.params.as_ref());
    let params = def
        .params
        .as_ref()
        .map(|params| {
            params
                .0
                .params
                .iter()
                .map(|param| {
                    if param.is_constant {
                        TyArg::Value(param.name.0.clone())
                    } else {
                        TyArg::Type(Ty::var(param.name.0.clone()))
                    }
                })
                .collect::<Vec<_>>()
        })
        .unwrap_or_default();
    let ret = if params.is_empty() {
        Ty::text(def.name.0.clone())
    } else {
        let text = format!(
            "{}({})",
            def.name.0,
            params
                .iter()
                .map(|arg| match arg {
                    TyArg::Type(ty) => ty.display_text(),
                    TyArg::Value(value) => value.clone(),
                })
                .collect::<Vec<_>>()
                .join(", ")
        );
        Ty::app(def.name.0.clone(), params, text)
    };

    let payload_ty = match &variant.payload {
        sail_parser::core_ast::UnionPayload::Type(ty) => Some(type_from_type_expr(source, ty)),
        sail_parser::core_ast::UnionPayload::Struct { .. } => Some(Ty::unknown()),
    };
    // In Sail, ALL union constructors take an argument (even unit-payload
    // ones are invoked as `Name()` with the unit value). Don't drop the
    // param when payload is unit — that causes false-positive
    // "Constructor X expects 0 arguments, found 1" errors.
    let params = match payload_ty {
        Some(ty) => vec![ty],
        None => Vec::new(),
    };

    TypeScheme {
        quantifiers,
        constraints,
        implicit_params: vec![false; params.len()],
        params,
        ret,
    }
}

fn scheme_from_callable_head(
    source: &str,
    def: &sail_parser::core_ast::CallableDefinition,
) -> Option<TypeScheme> {
    let (quantifiers, constraints) = def
        .clauses
        .first()
        .and_then(|clause| clause.0.quantifier.as_ref())
        .map(|quantifier| {
            let constraints = quantifier
                .constraint
                .as_ref()
                .map(|constraint| vec![quant_constraint_from_type_expr(source, constraint)])
                .unwrap_or_default();
            (
                quantifier
                    .vars
                    .iter()
                    .map(|var| var.name.0.clone())
                    .collect::<Vec<_>>(),
                constraints,
            )
        })
        .unwrap_or_default();
    let (params, return_ty) = if def.params.is_empty() {
        if let Some(clause) = def.clauses.first() {
            (
                &clause.0.patterns,
                clause.0.return_ty.as_ref().or(def.return_ty.as_ref()),
            )
        } else {
            (&def.params, def.return_ty.as_ref())
        }
    } else {
        (&def.params, def.return_ty.as_ref())
    };

    if params.is_empty() && return_ty.is_none() {
        return None;
    }

    let params = params
        .iter()
        .map(|param| {
            pattern_annotation_type(source, param)
                .or_else(|| infer_pattern_head_type(source, param))
                .unwrap_or(Ty::unknown())
        })
        .collect::<Vec<_>>();
    let ret = return_ty
        .map(|ty| type_from_type_expr(source, ty))
        .unwrap_or(Ty::unknown());
    let param_count = params.len();

    Some(TypeScheme {
        quantifiers,
        constraints,
        params,
        implicit_params: vec![false; param_count],
        ret,
    })
}

fn bitfield_field_ty(source: &str, field: &BitfieldField) -> Ty {
    match field
        .low
        .as_ref()
        .and_then(|low| {
            type_expr_static_int(source, &field.high)
                .zip(type_expr_static_int(source, low))
                .map(|(high, low)| (high - low).abs() + 1)
        })
        .or_else(|| bitfield_range_width_from_text(&span_text(source, field.high.1)))
    {
        Some(1) if field.low.is_none() => Ty::text("bit".to_string()),
        Some(width) => bits_ty(width),
        None => Ty::unknown(),
    }
}

fn bitfield_info_from_definition(
    source: &str,
    def: &sail_parser::core_ast::NamedDefinition,
) -> Option<BitfieldInfo> {
    if !matches!(def.kind, NamedDefKind::Bitfield) {
        return None;
    }
    let underlying = type_from_type_expr(source, def.ty.as_ref()?);
    let fields = match &def.detail {
        Some(NamedDefDetail::Bitfield { fields }) => fields
            .iter()
            .map(|field| (field.0.name.0.clone(), bitfield_field_ty(source, &field.0)))
            .collect(),
        _ => HashMap::new(),
    };
    Some(BitfieldInfo { underlying, fields })
}

fn synthesize_bitfield_accessors(
    env: &mut TopLevelEnv,
    bitfield_name: &str,
    field_name: &str,
    field_ty: Ty,
) {
    let bitfield_ty = Ty::text(bitfield_name.to_string());
    let getter_name = format!("_get_{bitfield_name}_{field_name}");
    let setter_name = format!("_set_{bitfield_name}_{field_name}");
    let updater_name = format!("_update_{bitfield_name}_{field_name}");
    let overload_name = format!("_mod_{field_name}");

    env.functions
        .entry(getter_name.clone())
        .or_default()
        .push(Arc::new(plain_scheme(
            vec![bitfield_ty.clone()],
            field_ty.clone(),
        )));
    env.functions
        .entry(setter_name.clone())
        .or_default()
        .push(Arc::new(plain_scheme(
            vec![register_ty(bitfield_ty.clone()), field_ty.clone()],
            Ty::text("unit".to_string()),
        )));
    env.functions
        .entry(updater_name)
        .or_default()
        .push(Arc::new(plain_scheme(
            vec![bitfield_ty.clone(), field_ty.clone()],
            bitfield_ty,
        )));
    env.overloads
        .entry(overload_name)
        .or_default()
        .extend([getter_name, setter_name]);
}

fn apply_callable_signature_metadata(file: &File, env: &mut TopLevelEnv) {
    let mut best_signatures =
        HashMap::<(String, usize), (usize, Vec<bool>, Vec<Ty>, Option<String>)>::new();

    for signature in collect_callable_signatures(file) {
        let implicit_params = signature
            .params
            .iter()
            .map(|param| param.is_implicit)
            .collect::<Vec<_>>();
        let signature_params = signature
            .params
            .iter()
            .map(|param| {
                param
                    .name
                    .split_once(':')
                    .map(|(_, ty)| Ty::text(ty.trim().to_string()))
                    .unwrap_or(Ty::unknown())
            })
            .collect::<Vec<_>>();
        let score = signature
            .params
            .iter()
            .filter(|param| param.is_implicit || param.name.contains(':'))
            .count()
            + usize::from(signature.return_type.is_some());
        let key = (signature.name.clone(), signature.params.len());
        match best_signatures.get(&key) {
            Some((best_score, _, _, _)) if *best_score >= score => {}
            _ => {
                best_signatures.insert(
                    key,
                    (
                        score,
                        implicit_params,
                        signature_params,
                        signature.return_type,
                    ),
                );
            }
        }
    }

    // Sort by key so iteration order is stable — otherwise HashMap's
    // randomized hasher can cause `check_file_with_workspace` to observe
    // a different scheme shape on different runs (e.g. tuple-flattened
    // vs. not) and emit different `Unresolved identifier` diagnostics.
    let mut best_signatures: Vec<_> = best_signatures.into_iter().collect();
    best_signatures.sort_by(|a, b| a.0.cmp(&b.0));
    for ((name, _), (_, implicit_params, signature_params, return_type)) in best_signatures {
        let Some(schemes) = env.functions.get_mut(&name) else {
            continue;
        };
        // Find a matching scheme by index. We can't keep an `&mut Arc<...>`
        // borrow across `Arc::make_mut` (which needs exclusive access to
        // the slot), so we resolve the index first and mutate after.
        let matched_idx = schemes.iter().position(|scheme| {
            if scheme.params.len() == implicit_params.len() {
                return true;
            }
            if scheme.params.len() == 1 {
                if let TyData::Tuple(items) = scheme.params[0].kind() {
                    return items.len() == implicit_params.len();
                }
            }
            false
        });
        if let Some(idx) = matched_idx {
            let scheme = Arc::make_mut(&mut schemes[idx]);
            if scheme.params.len() == 1 {
                if let TyData::Tuple(items) = scheme.params[0].kind() {
                    if items.len() == implicit_params.len() {
                        let new_params = items.clone();
                        scheme.params = new_params;
                    }
                }
            }
            scheme.implicit_params = implicit_params.clone();
            if scheme.ret.is_unknown() {
                if let Some(ret) = return_type.as_deref() {
                    scheme.ret = Ty::text(ret.to_string());
                }
            }
            continue;
        }

        if schemes.len() == 1 {
            let scheme = Arc::make_mut(&mut schemes[0]);
            scheme.params = signature_params;
            scheme.implicit_params = implicit_params;
            if scheme.ret.is_unknown() {
                if let Some(ret) = return_type.as_deref() {
                    scheme.ret = Ty::text(ret.to_string());
                }
            }
        }
    }
}

fn pattern_annotation_type(source: &str, pattern: &Spanned<Pattern>) -> Option<Ty> {
    match &pattern.0 {
        Pattern::Typed(_, ty) | Pattern::AsType(_, ty) => Some(type_from_type_expr(source, ty)),
        Pattern::Attribute { pattern, .. } => pattern_annotation_type(source, pattern),
        Pattern::AsBinding { pattern, .. } => pattern_annotation_type(source, pattern),
        _ => None,
    }
}

fn infer_pattern_head_type(source: &str, pattern: &Spanned<Pattern>) -> Option<Ty> {
    match &pattern.0 {
        Pattern::Attribute { pattern, .. } => infer_pattern_head_type(source, pattern),
        Pattern::Typed(_, ty) | Pattern::AsType(_, ty) => Some(type_from_type_expr(source, ty)),
        Pattern::AsBinding { pattern, .. } => infer_pattern_head_type(source, pattern),
        Pattern::Literal(literal) => Some(infer_literal_type(literal)),
        Pattern::Tuple(items) => items
            .iter()
            .map(|item| infer_pattern_head_type(source, item))
            .collect::<Option<Vec<_>>>()
            .map(Ty::tuple),
        Pattern::Vector(items) => {
            let elem_tys = items
                .iter()
                .map(|item| infer_pattern_head_type(source, item))
                .collect::<Option<Vec<_>>>()?;
            let first = elem_tys.first()?.clone();
            if elem_tys.iter().all(|item| *item == first) {
                Some(vector_ty(items.len(), first))
            } else {
                None
            }
        }
        Pattern::List(items) => {
            let elem_tys = items
                .iter()
                .map(|item| infer_pattern_head_type(source, item))
                .collect::<Option<Vec<_>>>()?;
            let first = elem_tys.first()?.clone();
            if elem_tys.iter().all(|item| *item == first) {
                let text = format!("list({})", first.display_text());
                Some(Ty::app("list", vec![TyArg::Type(first.clone())], text))
            } else {
                None
            }
        }
        _ => None,
    }
}

fn infer_literal_type(literal: &Literal) -> Ty {
    match literal {
        Literal::Bool(_) => Ty::text("bool".to_string()),
        Literal::Unit => Ty::text("unit".to_string()),
        Literal::Number(text) => {
            if text.contains('.') {
                Ty::text("real".to_string())
            } else {
                Ty::text("int".to_string())
            }
        }
        Literal::Binary(text) => {
            let bits = text
                .trim_start_matches("0b")
                .chars()
                .filter(|ch| *ch != '_')
                .count();
            Ty::app(
                "bits",
                vec![TyArg::Value(bits.to_string())],
                format!("bits({bits})"),
            )
        }
        Literal::Hex(text) => {
            let bits = text
                .trim_start_matches("0x")
                .chars()
                .filter(|ch| *ch != '_')
                .count()
                * 4;
            Ty::app(
                "bits",
                vec![TyArg::Value(bits.to_string())],
                format!("bits({bits})"),
            )
        }
        Literal::String(_) => Ty::text("string".to_string()),
        Literal::BitZero | Literal::BitOne => Ty::text("bit".to_string()),
        Literal::Undefined => Ty::unknown(),
    }
}

fn bits_ty(width: impl ToString) -> Ty {
    let width = width.to_string();
    Ty::app(
        "bits",
        vec![TyArg::Value(width.clone())],
        format!("bits({width})"),
    )
}

fn register_ty(inner: Ty) -> Ty {
    let inner_text = inner.display_text();
    Ty::app(
        "register",
        vec![TyArg::Type(inner)],
        format!("register({inner_text})"),
    )
}

fn vector_ty(width: impl ToString, elem: Ty) -> Ty {
    let width = width.to_string();
    let elem_text = elem.display_text();
    Ty::app(
        "vector",
        vec![TyArg::Value(width.clone()), TyArg::Type(elem)],
        format!("vector({width}, {elem_text})"),
    )
}

fn plain_scheme(params: Vec<Ty>, ret: Ty) -> TypeScheme {
    let param_count = params.len();
    TypeScheme {
        quantifiers: Vec::new(),
        constraints: Vec::new(),
        params,
        implicit_params: vec![false; param_count],
        ret,
    }
}

fn parse_int_literal(text: &str) -> Option<i64> {
    let text = text.trim().replace('_', "");
    if let Some(rest) = text.strip_prefix("0b") {
        i64::from_str_radix(rest, 2).ok()
    } else if let Some(rest) = text.strip_prefix("0x") {
        i64::from_str_radix(rest, 16).ok()
    } else {
        text.parse().ok()
    }
}

struct NumericTextParser<'a> {
    input: &'a str,
    pos: usize,
}

impl<'a> NumericTextParser<'a> {
    fn new(input: &'a str) -> Self {
        Self { input, pos: 0 }
    }

    fn parse(mut self) -> Option<NumericExpr> {
        let expr = self.parse_add_sub()?;
        self.skip_ws();
        (self.pos == self.input.len()).then_some(expr)
    }

    fn parse_add_sub(&mut self) -> Option<NumericExpr> {
        let mut expr = self.parse_mul_div()?;
        loop {
            self.skip_ws();
            let op = if self.consume_char('+') {
                Some(ArithmeticOp::Add)
            } else if self.consume_char('-') {
                Some(ArithmeticOp::Sub)
            } else {
                None
            };
            let Some(op) = op else {
                break;
            };
            let rhs = self.parse_mul_div()?;
            expr = match op {
                ArithmeticOp::Add => NumericExpr::Add(Box::new(expr), Box::new(rhs)),
                ArithmeticOp::Sub => NumericExpr::Sub(Box::new(expr), Box::new(rhs)),
                _ => unreachable!(),
            };
        }
        Some(expr)
    }

    fn parse_mul_div(&mut self) -> Option<NumericExpr> {
        let mut expr = self.parse_unary()?;
        loop {
            self.skip_ws();
            let op = if self.consume_char('*') {
                Some(ArithmeticOp::Mul)
            } else if self.consume_char('/') {
                Some(ArithmeticOp::Div)
            } else if self.consume_char('%') {
                Some(ArithmeticOp::Mod)
            } else {
                None
            };
            let Some(op) = op else {
                break;
            };
            let rhs = self.parse_unary()?;
            expr = match op {
                ArithmeticOp::Mul => NumericExpr::Mul(Box::new(expr), Box::new(rhs)),
                ArithmeticOp::Div => NumericExpr::Div(Box::new(expr), Box::new(rhs)),
                ArithmeticOp::Mod => NumericExpr::Mod(Box::new(expr), Box::new(rhs)),
                _ => unreachable!(),
            };
        }
        Some(expr)
    }

    fn parse_unary(&mut self) -> Option<NumericExpr> {
        self.skip_ws();
        if self.consume_char('-') {
            Some(NumericExpr::Neg(Box::new(self.parse_unary()?)))
        } else {
            self.parse_primary()
        }
    }

    fn parse_primary(&mut self) -> Option<NumericExpr> {
        self.skip_ws();
        if self.consume_char('(') {
            let expr = self.parse_add_sub()?;
            self.skip_ws();
            self.consume_char(')').then_some(expr)
        } else {
            let token = self.consume_token()?;
            parse_int_literal(&token)
                .map(NumericExpr::Const)
                .or_else(|| {
                    Some(if token.starts_with('\'') {
                        NumericExpr::Var(token)
                    } else {
                        NumericExpr::Symbol(token)
                    })
                })
        }
    }

    fn consume_token(&mut self) -> Option<String> {
        self.skip_ws();
        let rest = &self.input[self.pos..];
        let mut len = 0;
        for ch in rest.chars() {
            if ch.is_ascii_alphanumeric() || matches!(ch, '_' | '\'' | '#') {
                len += ch.len_utf8();
            } else {
                break;
            }
        }
        if len == 0 {
            None
        } else {
            let token = rest[..len].to_string();
            self.pos += len;
            Some(token)
        }
    }

    fn consume_char(&mut self, expected: char) -> bool {
        self.skip_ws();
        let mut chars = self.input[self.pos..].chars();
        match chars.next() {
            Some(ch) if ch == expected => {
                self.pos += ch.len_utf8();
                true
            }
            _ => false,
        }
    }

    fn skip_ws(&mut self) {
        while let Some(ch) = self.input[self.pos..].chars().next() {
            if ch.is_whitespace() {
                self.pos += ch.len_utf8();
            } else {
                break;
            }
        }
    }
}

fn parse_numeric_expr_text(text: &str) -> Option<NumericExpr> {
    NumericTextParser::new(text).parse()
}

fn negate_constraint(expr: ConstraintExpr) -> ConstraintExpr {
    match expr {
        ConstraintExpr::Bool(value) => ConstraintExpr::Bool(!value),
        ConstraintExpr::Not(inner) => *inner,
        other => ConstraintExpr::Not(Box::new(other)),
    }
}

fn combine_constraint_expr(
    require_both: bool,
    op: impl FnOnce(Vec<ConstraintExpr>) -> ConstraintExpr,
    left: Option<ConstraintExpr>,
    right: Option<ConstraintExpr>,
) -> Option<ConstraintExpr> {
    match (require_both, left, right) {
        (_, Some(left), Some(right)) => Some(op(vec![left, right])),
        (true, Some(left), None) | (true, None, Some(left)) => Some(left),
        (false, Some(_), None) | (false, None, Some(_)) | (_, None, None) => None,
    }
}

fn numeric_expr_from_expr(expr: &Spanned<Expr>) -> Option<NumericExpr> {
    match &expr.0 {
        Expr::Attribute { expr, .. } => numeric_expr_from_expr(expr),
        Expr::Literal(Literal::Number(text))
        | Expr::Literal(Literal::Binary(text))
        | Expr::Literal(Literal::Hex(text)) => parse_int_literal(text).map(NumericExpr::Const),
        Expr::Ident(name) => Some(NumericExpr::Symbol(name.clone())),
        Expr::TypeVar(name) => Some(NumericExpr::Var(name.clone())),
        Expr::Prefix { op, expr } if op.0 == "-" => {
            Some(NumericExpr::Neg(Box::new(numeric_expr_from_expr(expr)?)))
        }
        Expr::Infix { lhs, op, rhs } => {
            let lhs = numeric_expr_from_expr(lhs)?;
            let rhs = numeric_expr_from_expr(rhs)?;
            Some(match arithmetic_op_from_str(&op.0)? {
                ArithmeticOp::Add => NumericExpr::Add(Box::new(lhs), Box::new(rhs)),
                ArithmeticOp::Sub => NumericExpr::Sub(Box::new(lhs), Box::new(rhs)),
                ArithmeticOp::Mul => NumericExpr::Mul(Box::new(lhs), Box::new(rhs)),
                ArithmeticOp::Div => NumericExpr::Div(Box::new(lhs), Box::new(rhs)),
                ArithmeticOp::Mod => NumericExpr::Mod(Box::new(lhs), Box::new(rhs)),
            })
        }
        _ => None,
    }
}

fn constraint_expr_from_expr(
    source: &str,
    expr: &Spanned<Expr>,
    positive: bool,
) -> Option<ConstraintExpr> {
    let constraint = match &expr.0 {
        Expr::Attribute { expr, .. } => return constraint_expr_from_expr(source, expr, positive),
        Expr::Constraint(ty) => constraint_expr_from_type_expr(source, ty),
        Expr::Literal(Literal::Bool(value)) => ConstraintExpr::Bool(*value),
        Expr::Let { body, .. } => return constraint_expr_from_expr(source, body, positive),
        Expr::Prefix { op, expr } if op.0 == "not" => {
            return constraint_expr_from_expr(source, expr, !positive);
        }
        Expr::Infix { lhs, op, rhs } => match op.0.as_str() {
            "and" | "&" if positive => combine_constraint_expr(
                true,
                ConstraintExpr::And,
                constraint_expr_from_expr(source, lhs, true),
                constraint_expr_from_expr(source, rhs, true),
            )?,
            "and" | "&" => combine_constraint_expr(
                false,
                ConstraintExpr::Or,
                constraint_expr_from_expr(source, lhs, false),
                constraint_expr_from_expr(source, rhs, false),
            )?,
            "or" | "|" if positive => combine_constraint_expr(
                false,
                ConstraintExpr::Or,
                constraint_expr_from_expr(source, lhs, true),
                constraint_expr_from_expr(source, rhs, true),
            )?,
            "or" | "|" => combine_constraint_expr(
                true,
                ConstraintExpr::And,
                constraint_expr_from_expr(source, lhs, false),
                constraint_expr_from_expr(source, rhs, false),
            )?,
            "==" | "!=" | "<" | "<=" | ">" | ">=" => ConstraintExpr::Compare {
                lhs: numeric_expr_from_expr(lhs)?,
                op: compare_op_from_str(op.0.as_str())?,
                rhs: numeric_expr_from_expr(rhs)?,
            },
            _ => return None,
        },
        _ => return None,
    };

    if positive {
        Some(constraint)
    } else {
        Some(negate_constraint(constraint))
    }
}

fn numeric_expr_collect_vars(expr: &NumericExpr, out: &mut HashSet<String>) {
    match expr {
        NumericExpr::Var(name) => {
            out.insert(name.clone());
        }
        NumericExpr::Neg(inner) => numeric_expr_collect_vars(inner, out),
        NumericExpr::Add(lhs, rhs)
        | NumericExpr::Sub(lhs, rhs)
        | NumericExpr::Mul(lhs, rhs)
        | NumericExpr::Div(lhs, rhs)
        | NumericExpr::Mod(lhs, rhs) => {
            numeric_expr_collect_vars(lhs, out);
            numeric_expr_collect_vars(rhs, out);
        }
        NumericExpr::Const(_) | NumericExpr::Symbol(_) => {}
    }
}

fn numeric_symbol_assumption(
    name: &str,
    subst: &Subst,
    assumptions: &[ConstraintExpr],
    visited: &mut HashSet<String>,
) -> Option<i64> {
    if !visited.insert(name.to_string()) {
        return None;
    }
    for assumption in assumptions {
        match assumption {
            ConstraintExpr::Compare {
                lhs: NumericExpr::Symbol(symbol),
                op: CompareOp::Eq,
                rhs,
            } if symbol == name => {
                if let Some(value) =
                    eval_numeric_expr_with_assumptions(rhs, subst, assumptions, visited)
                {
                    visited.remove(name);
                    return Some(value);
                }
            }
            ConstraintExpr::Compare {
                lhs,
                op: CompareOp::Eq,
                rhs: NumericExpr::Symbol(symbol),
            } if symbol == name => {
                if let Some(value) =
                    eval_numeric_expr_with_assumptions(lhs, subst, assumptions, visited)
                {
                    visited.remove(name);
                    return Some(value);
                }
            }
            ConstraintExpr::InSet {
                value: NumericExpr::Symbol(symbol),
                items,
            } if symbol == name && items.len() == 1 => {
                if let Some(value) =
                    eval_numeric_expr_with_assumptions(&items[0], subst, assumptions, visited)
                {
                    visited.remove(name);
                    return Some(value);
                }
            }
            _ => {}
        }
    }
    visited.remove(name);
    None
}

fn eval_numeric_expr_with_assumptions(
    expr: &NumericExpr,
    subst: &Subst,
    assumptions: &[ConstraintExpr],
    visited: &mut HashSet<String>,
) -> Option<i64> {
    fn numeric_var_expr(name: &str, subst: &Subst) -> Option<NumericExpr> {
        let expr = subst
            .values
            .get(name)
            .and_then(|value| parse_numeric_expr_text(value))
            .or_else(|| {
                subst.types.get(name).and_then(|ty| {
                    let text = ty.display_text();
                    parse_numeric_expr_text(&text)
                })
            });
        match expr {
            Some(NumericExpr::Var(bound)) if bound == name => None,
            other => other,
        }
    }

    match expr {
        NumericExpr::Const(value) => Some(*value),
        NumericExpr::Var(name) => numeric_var_expr(name, subst).and_then(|expr| {
            eval_numeric_expr_with_assumptions(&expr, subst, assumptions, visited)
        }),
        NumericExpr::Symbol(name) => parse_int_literal(name)
            .or_else(|| numeric_symbol_assumption(name, subst, assumptions, visited)),
        NumericExpr::Neg(inner) => Some(-eval_numeric_expr_with_assumptions(
            inner,
            subst,
            assumptions,
            visited,
        )?),
        NumericExpr::Add(lhs, rhs) => Some(
            eval_numeric_expr_with_assumptions(lhs, subst, assumptions, visited)?
                + eval_numeric_expr_with_assumptions(rhs, subst, assumptions, visited)?,
        ),
        NumericExpr::Sub(lhs, rhs) => Some(
            eval_numeric_expr_with_assumptions(lhs, subst, assumptions, visited)?
                - eval_numeric_expr_with_assumptions(rhs, subst, assumptions, visited)?,
        ),
        NumericExpr::Mul(lhs, rhs) => Some(
            eval_numeric_expr_with_assumptions(lhs, subst, assumptions, visited)?
                * eval_numeric_expr_with_assumptions(rhs, subst, assumptions, visited)?,
        ),
        NumericExpr::Div(lhs, rhs) => {
            let rhs = eval_numeric_expr_with_assumptions(rhs, subst, assumptions, visited)?;
            (rhs != 0).then_some(
                eval_numeric_expr_with_assumptions(lhs, subst, assumptions, visited)? / rhs,
            )
        }
        NumericExpr::Mod(lhs, rhs) => {
            let rhs = eval_numeric_expr_with_assumptions(rhs, subst, assumptions, visited)?;
            (rhs != 0).then_some(
                eval_numeric_expr_with_assumptions(lhs, subst, assumptions, visited)? % rhs,
            )
        }
    }
}

fn eval_numeric_expr(
    expr: &NumericExpr,
    subst: &Subst,
    assumptions: &[ConstraintExpr],
) -> Option<i64> {
    eval_numeric_expr_with_assumptions(expr, subst, assumptions, &mut HashSet::new())
}

fn linear_numeric_expr(
    expr: &NumericExpr,
    target: &str,
    subst: &Subst,
    assumptions: &[ConstraintExpr],
) -> Option<(i64, i64)> {
    match expr {
        NumericExpr::Const(value) => Some((0, *value)),
        NumericExpr::Var(name) if name == target => Some((1, 0)),
        NumericExpr::Var(name) => subst
            .values
            .get(name)
            .and_then(|value| parse_numeric_expr_text(value))
            .or_else(|| {
                subst.types.get(name).and_then(|ty| {
                    let text = ty.display_text();
                    parse_numeric_expr_text(&text)
                })
            })
            .and_then(|expr| linear_numeric_expr(&expr, target, subst, assumptions)),
        NumericExpr::Symbol(name) => {
            eval_numeric_expr(&NumericExpr::Symbol(name.clone()), subst, assumptions)
                .map(|value| (0, value))
        }
        NumericExpr::Neg(inner) => {
            let (coeff, constant) = linear_numeric_expr(inner, target, subst, assumptions)?;
            Some((-coeff, -constant))
        }
        NumericExpr::Add(lhs, rhs) => {
            let (left_coeff, left_const) = linear_numeric_expr(lhs, target, subst, assumptions)?;
            let (right_coeff, right_const) = linear_numeric_expr(rhs, target, subst, assumptions)?;
            Some((left_coeff + right_coeff, left_const + right_const))
        }
        NumericExpr::Sub(lhs, rhs) => {
            let (left_coeff, left_const) = linear_numeric_expr(lhs, target, subst, assumptions)?;
            let (right_coeff, right_const) = linear_numeric_expr(rhs, target, subst, assumptions)?;
            Some((left_coeff - right_coeff, left_const - right_const))
        }
        NumericExpr::Mul(lhs, rhs) => match (
            linear_numeric_expr(lhs, target, subst, assumptions),
            linear_numeric_expr(rhs, target, subst, assumptions),
        ) {
            (Some((0, left_const)), Some((right_coeff, right_const))) => {
                Some((left_const * right_coeff, left_const * right_const))
            }
            (Some((left_coeff, left_const)), Some((0, right_const))) => {
                Some((left_coeff * right_const, left_const * right_const))
            }
            _ => None,
        },
        NumericExpr::Div(lhs, rhs) => {
            let (left_coeff, left_const) = linear_numeric_expr(lhs, target, subst, assumptions)?;
            let rhs = eval_numeric_expr(rhs, subst, assumptions)?;
            (rhs != 0 && left_coeff % rhs == 0 && left_const % rhs == 0)
                .then_some((left_coeff / rhs, left_const / rhs))
        }
        NumericExpr::Mod(_, _) => None,
    }
}

fn type_expr_static_int(source: &str, ty: &Spanned<TypeExpr>) -> Option<i64> {
    match &ty.0 {
        TypeExpr::Literal(text) | TypeExpr::Named(text) => parse_int_literal(text),
        _ => parse_int_literal(&span_text(source, ty.1)),
    }
}

fn split_top_level_text<'a>(text: &'a str, pat: &str) -> Option<Vec<&'a str>> {
    let mut depth = 0_i32;
    let mut start = 0_usize;
    let mut parts = Vec::new();
    let bytes = text.as_bytes();
    let pat_bytes = pat.as_bytes();
    let mut idx = 0_usize;
    while idx < bytes.len() {
        match bytes[idx] {
            b'(' | b'[' | b'{' => depth += 1,
            b')' | b']' | b'}' => depth -= 1,
            _ => {}
        }
        if depth == 0
            && idx + pat_bytes.len() <= bytes.len()
            && &bytes[idx..idx + pat_bytes.len()] == pat_bytes
        {
            parts.push(text[start..idx].trim());
            idx += pat_bytes.len();
            start = idx;
            continue;
        }
        idx += 1;
    }
    if parts.is_empty() {
        None
    } else {
        parts.push(text[start..].trim());
        Some(parts)
    }
}

fn trim_wrapping_parens_text(text: &str) -> &str {
    let mut text = text.trim();
    loop {
        if !(text.starts_with('(') && text.ends_with(')')) {
            return text;
        }
        let mut depth = 0_i32;
        let mut wraps = true;
        for (idx, ch) in text.char_indices() {
            match ch {
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth == 0 && idx + ch.len_utf8() != text.len() {
                        wraps = false;
                        break;
                    }
                }
                _ => {}
            }
        }
        if !wraps {
            return text;
        }
        text = text[1..text.len() - 1].trim();
    }
}

fn bitfield_range_width_from_text(text: &str) -> Option<i64> {
    let text = trim_wrapping_parens_text(text);
    if let Some(parts) = split_top_level_text(text, "@") {
        let mut total = 0_i64;
        for part in parts {
            total += bitfield_range_width_from_text(part)?;
        }
        return Some(total);
    }
    if let Some(parts) =
        split_top_level_text(text, "..").or_else(|| split_top_level_text(text, "..."))
    {
        if parts.len() == 2 {
            let high = parse_numeric_expr_text(parts[0])
                .and_then(|expr| eval_numeric_expr(&expr, &Subst::default(), &[]))?;
            let low = parse_numeric_expr_text(parts[1])
                .and_then(|expr| eval_numeric_expr(&expr, &Subst::default(), &[]))?;
            return Some((high - low).abs() + 1);
        }
    }
    parse_numeric_expr_text(text)
        .and_then(|expr| eval_numeric_expr(&expr, &Subst::default(), &[]))
        .map(|_| 1)
}

fn pattern_static_bit_width(source: &str, pattern: &Spanned<Pattern>) -> Option<i64> {
    match &pattern.0 {
        Pattern::Attribute { pattern, .. } => pattern_static_bit_width(source, pattern),
        Pattern::Typed(inner, ty) | Pattern::AsType(inner, ty) => {
            pattern_static_bit_width(source, inner).or_else(|| {
                let parsed = type_from_type_expr(source, ty);
                match parsed.kind() {
                    TyData::App { name, args, .. } if name == "bits" => {
                        args.first().and_then(|arg| {
                            if let TyArg::Value(value) = arg {
                                parse_int_literal(value)
                            } else {
                                None
                            }
                        })
                    }
                    _ => None,
                }
            })
        }
        Pattern::Literal(Literal::Binary(text)) => Some(
            text.trim_start_matches("0b")
                .chars()
                .filter(|ch| *ch != '_')
                .count() as i64,
        ),
        Pattern::Literal(Literal::Hex(text)) => Some(
            (text
                .trim_start_matches("0x")
                .chars()
                .filter(|ch| *ch != '_')
                .count()
                * 4) as i64,
        ),
        Pattern::Literal(Literal::BitZero | Literal::BitOne) => Some(1),
        Pattern::Vector(items) => Some(items.len() as i64),
        Pattern::Index { .. } => Some(1),
        Pattern::RangeIndex { start, end, .. } => {
            let start = type_expr_static_int(source, start)?;
            let end = type_expr_static_int(source, end)?;
            Some((start - end).abs() + 1)
        }
        Pattern::Infix { lhs, op, rhs } if op.0 == "@" => {
            Some(pattern_static_bit_width(source, lhs)? + pattern_static_bit_width(source, rhs)?)
        }
        _ => None,
    }
}

fn insert_subrange(ranges: &mut Vec<(i64, i64)>, hi: i64, lo: i64) {
    let mut pending = Some((hi, lo));
    let mut index = 0;
    while index < ranges.len() {
        let (pending_hi, pending_lo) = pending.expect("pending range must exist");
        let (current_hi, current_lo) = ranges[index];
        if pending_lo == current_hi + 1 {
            ranges[index] = (pending_hi, current_lo);
            pending = None;
            break;
        }
        if pending_lo > current_hi {
            ranges.insert(index, (pending_hi, pending_lo));
            pending = None;
            break;
        }
        if current_lo == pending_hi + 1 {
            pending = Some((current_hi, pending_lo));
            ranges.remove(index);
            continue;
        }
        index += 1;
    }
    if let Some((pending_hi, pending_lo)) = pending {
        ranges.push((pending_hi, pending_lo));
    }
}

fn app_text(name: &str, args: &[TyArg]) -> String {
    if args.is_empty() {
        name.to_string()
    } else {
        format!(
            "{}({})",
            name,
            args.iter()
                .map(|arg| match arg {
                    TyArg::Type(ty) => ty.display_text(),
                    TyArg::Value(value) => value.clone(),
                })
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

fn normalized_value_text(text: &str) -> String {
    text.chars().filter(|ch| !ch.is_whitespace()).collect()
}

fn ty_contains_var(ty: &Ty, name: &str) -> bool {
    match ty.kind() {
        TyData::Unknown | TyData::Text(_) => false,
        TyData::Var(var) => var == name,
        TyData::Tuple(items) => items.iter().any(|item| ty_contains_var(item, name)),
        TyData::Function { params, ret } => {
            params.iter().any(|param| ty_contains_var(param, name))
                || ty_contains_var(ret, name)
        }
        TyData::App { args, .. } => args.iter().any(|arg| match arg {
            TyArg::Type(ty) => ty_contains_var(ty, name),
            TyArg::Value(_) => false,
        }),
    }
}

fn unify_numeric_expr(expected: &NumericExpr, actual: &NumericExpr, subst: &mut Subst) -> bool {
    if let (Some(expected), Some(actual)) = (
        eval_numeric_expr(expected, subst, &[]),
        eval_numeric_expr(actual, subst, &[]),
    ) {
        return expected == actual;
    }

    // Polynomial-form equivalence: convert each side to a canonical sum of
    // terms `coefficient * variable_product + constant`. Two expressions
    // unify if their canonical polynomials are identical after substitution.
    // This handles cases like:
    //   `('m - i - 1) - ('m - i - 8) + 1` == 8
    //   `(i + 7) - i + 1` == 8
    // which require constant-folding across multiple variables.
    let expected_subst = subst_numeric_expr(expected, subst);
    let actual_subst = subst_numeric_expr(actual, subst);
    if let (Some(expected_poly), Some(actual_poly)) = (
        polynomial_from_numeric_expr(&expected_subst),
        polynomial_from_numeric_expr(&actual_subst),
    ) {
        if expected_poly == actual_poly {
            return true;
        }
    }

    let mut unresolved = HashSet::new();
    numeric_expr_collect_vars(expected, &mut unresolved);
    unresolved.retain(|name| !subst.values.contains_key(name) && !subst.types.contains_key(name));
    if unresolved.len() == 1 {
        let variable = unresolved
            .into_iter()
            .next()
            .expect("single unresolved variable");
        if let Some(actual_value) = eval_numeric_expr(actual, subst, &[]) {
            if let Some((coeff, constant)) = linear_numeric_expr(expected, &variable, subst, &[]) {
                let delta = actual_value - constant;
                if coeff != 0 && delta % coeff == 0 {
                    subst.values.insert(variable, (delta / coeff).to_string());
                    return true;
                }
            }
        }
    }

    false
}

/// A polynomial in canonical form: a sorted list of (variable_product, coeff)
/// terms plus a constant. Used for algebraic equivalence checking of
/// numeric expressions over multiple type variables.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Polynomial {
    /// Map from sorted variable product (e.g. ["i", "n"]) to coefficient.
    /// An empty Vec key represents the constant term.
    terms: std::collections::BTreeMap<Vec<String>, i64>,
}

impl Polynomial {
    fn constant(c: i64) -> Self {
        let mut terms = std::collections::BTreeMap::new();
        if c != 0 {
            terms.insert(Vec::new(), c);
        }
        Self { terms }
    }

    fn variable(name: String) -> Self {
        let mut terms = std::collections::BTreeMap::new();
        terms.insert(vec![name], 1);
        Self { terms }
    }

    fn add(&self, other: &Self) -> Self {
        let mut result = self.terms.clone();
        for (k, v) in &other.terms {
            *result.entry(k.clone()).or_insert(0) += v;
        }
        result.retain(|_, v| *v != 0);
        Self { terms: result }
    }

    fn neg(&self) -> Self {
        let terms = self.terms.iter().map(|(k, v)| (k.clone(), -v)).collect();
        Self { terms }
    }

    fn sub(&self, other: &Self) -> Self {
        self.add(&other.neg())
    }

    fn mul(&self, other: &Self) -> Option<Self> {
        let mut result: std::collections::BTreeMap<Vec<String>, i64> =
            std::collections::BTreeMap::new();
        for (lk, lv) in &self.terms {
            for (rk, rv) in &other.terms {
                let mut combined = lk.clone();
                combined.extend(rk.iter().cloned());
                combined.sort();
                // Cap degree to avoid runaway expansion
                if combined.len() > 4 {
                    return None;
                }
                *result.entry(combined).or_insert(0) += lv * rv;
            }
        }
        result.retain(|_, v| *v != 0);
        Some(Self { terms: result })
    }
}

fn polynomial_from_numeric_expr(expr: &NumericExpr) -> Option<Polynomial> {
    match expr {
        NumericExpr::Const(c) => Some(Polynomial::constant(*c)),
        NumericExpr::Var(name) | NumericExpr::Symbol(name) => {
            Some(Polynomial::variable(name.clone()))
        }
        NumericExpr::Neg(inner) => Some(polynomial_from_numeric_expr(inner)?.neg()),
        NumericExpr::Add(lhs, rhs) => {
            let l = polynomial_from_numeric_expr(lhs)?;
            let r = polynomial_from_numeric_expr(rhs)?;
            Some(l.add(&r))
        }
        NumericExpr::Sub(lhs, rhs) => {
            let l = polynomial_from_numeric_expr(lhs)?;
            let r = polynomial_from_numeric_expr(rhs)?;
            Some(l.sub(&r))
        }
        NumericExpr::Mul(lhs, rhs) => {
            let l = polynomial_from_numeric_expr(lhs)?;
            let r = polynomial_from_numeric_expr(rhs)?;
            l.mul(&r)
        }
        // Division and modulo aren't representable in linear polynomial form
        // — bail out (caller will fall back to other unification strategies).
        NumericExpr::Div(_, _) | NumericExpr::Mod(_, _) => None,
    }
}

fn swapped_compare_op(op: CompareOp) -> CompareOp {
    match op {
        CompareOp::Eq => CompareOp::Eq,
        CompareOp::Neq => CompareOp::Neq,
        CompareOp::Lt => CompareOp::Gt,
        CompareOp::Lte => CompareOp::Gte,
        CompareOp::Gt => CompareOp::Lt,
        CompareOp::Gte => CompareOp::Lte,
    }
}

fn numeric_expr_key(expr: &NumericExpr) -> String {
    match expr {
        NumericExpr::Const(value) => value.to_string(),
        NumericExpr::Var(name) | NumericExpr::Symbol(name) => name.clone(),
        NumericExpr::Neg(inner) => format!("(-{})", numeric_expr_key(inner)),
        NumericExpr::Add(lhs, rhs) => {
            format!("({}+{})", numeric_expr_key(lhs), numeric_expr_key(rhs))
        }
        NumericExpr::Sub(lhs, rhs) => {
            format!("({}-{})", numeric_expr_key(lhs), numeric_expr_key(rhs))
        }
        NumericExpr::Mul(lhs, rhs) => {
            format!("({}*{})", numeric_expr_key(lhs), numeric_expr_key(rhs))
        }
        NumericExpr::Div(lhs, rhs) => {
            format!("({}/{})", numeric_expr_key(lhs), numeric_expr_key(rhs))
        }
        NumericExpr::Mod(lhs, rhs) => {
            format!("({}%{})", numeric_expr_key(lhs), numeric_expr_key(rhs))
        }
    }
}

fn subst_numeric_expr(expr: &NumericExpr, subst: &Subst) -> NumericExpr {
    match expr {
        NumericExpr::Const(value) => NumericExpr::Const(*value),
        NumericExpr::Var(name) => {
            let resolved = subst
                .values
                .get(name)
                .and_then(|value| parse_numeric_expr_text(value))
                .or_else(|| {
                    subst.types.get(name).and_then(|ty| {
                        let text = ty.display_text();
                        parse_numeric_expr_text(&text)
                    })
                });
            match resolved {
                Some(NumericExpr::Var(bound)) if &bound == name => NumericExpr::Var(name.clone()),
                Some(expr) => subst_numeric_expr(&expr, subst),
                None => NumericExpr::Var(name.clone()),
            }
        }
        NumericExpr::Symbol(name) => NumericExpr::Symbol(name.clone()),
        NumericExpr::Neg(inner) => NumericExpr::Neg(Box::new(subst_numeric_expr(inner, subst))),
        NumericExpr::Add(lhs, rhs) => NumericExpr::Add(
            Box::new(subst_numeric_expr(lhs, subst)),
            Box::new(subst_numeric_expr(rhs, subst)),
        ),
        NumericExpr::Sub(lhs, rhs) => NumericExpr::Sub(
            Box::new(subst_numeric_expr(lhs, subst)),
            Box::new(subst_numeric_expr(rhs, subst)),
        ),
        NumericExpr::Mul(lhs, rhs) => NumericExpr::Mul(
            Box::new(subst_numeric_expr(lhs, subst)),
            Box::new(subst_numeric_expr(rhs, subst)),
        ),
        NumericExpr::Div(lhs, rhs) => NumericExpr::Div(
            Box::new(subst_numeric_expr(lhs, subst)),
            Box::new(subst_numeric_expr(rhs, subst)),
        ),
        NumericExpr::Mod(lhs, rhs) => NumericExpr::Mod(
            Box::new(subst_numeric_expr(lhs, subst)),
            Box::new(subst_numeric_expr(rhs, subst)),
        ),
    }
}

fn stronger_lower_bound(current: NumericBound, candidate: NumericBound) -> NumericBound {
    if candidate.value > current.value
        || (candidate.value == current.value && !candidate.inclusive && current.inclusive)
    {
        candidate
    } else {
        current
    }
}

fn stronger_upper_bound(current: NumericBound, candidate: NumericBound) -> NumericBound {
    if candidate.value < current.value
        || (candidate.value == current.value && !candidate.inclusive && current.inclusive)
    {
        candidate
    } else {
        current
    }
}

fn constraint_facts_add_compare(facts: &mut ConstraintFacts, op: CompareOp, value: i64) {
    match op {
        CompareOp::Eq => {
            let singleton = HashSet::from([value]);
            facts.exact_values = Some(match facts.exact_values.take() {
                Some(values) => values.intersection(&singleton).copied().collect(),
                None => singleton,
            });
            facts.lower = Some(match facts.lower {
                Some(current) => stronger_lower_bound(
                    current,
                    NumericBound {
                        value,
                        inclusive: true,
                    },
                ),
                None => NumericBound {
                    value,
                    inclusive: true,
                },
            });
            facts.upper = Some(match facts.upper {
                Some(current) => stronger_upper_bound(
                    current,
                    NumericBound {
                        value,
                        inclusive: true,
                    },
                ),
                None => NumericBound {
                    value,
                    inclusive: true,
                },
            });
        }
        CompareOp::Neq => {
            facts.excluded_values.insert(value);
        }
        CompareOp::Gt => {
            let bound = NumericBound {
                value,
                inclusive: false,
            };
            facts.lower = Some(match facts.lower {
                Some(current) => stronger_lower_bound(current, bound),
                None => bound,
            });
        }
        CompareOp::Gte => {
            let bound = NumericBound {
                value,
                inclusive: true,
            };
            facts.lower = Some(match facts.lower {
                Some(current) => stronger_lower_bound(current, bound),
                None => bound,
            });
        }
        CompareOp::Lt => {
            let bound = NumericBound {
                value,
                inclusive: false,
            };
            facts.upper = Some(match facts.upper {
                Some(current) => stronger_upper_bound(current, bound),
                None => bound,
            });
        }
        CompareOp::Lte => {
            let bound = NumericBound {
                value,
                inclusive: true,
            };
            facts.upper = Some(match facts.upper {
                Some(current) => stronger_upper_bound(current, bound),
                None => bound,
            });
        }
    }
}

fn constraint_facts_add_set(facts: &mut ConstraintFacts, values: HashSet<i64>) {
    facts.exact_values = Some(match facts.exact_values.take() {
        Some(existing) => existing.intersection(&values).copied().collect(),
        None => values,
    });
}

fn bound_min(bound: NumericBound) -> i64 {
    if bound.inclusive {
        bound.value
    } else {
        bound.value.saturating_add(1)
    }
}

fn bound_max(bound: NumericBound) -> i64 {
    if bound.inclusive {
        bound.value
    } else {
        bound.value.saturating_sub(1)
    }
}

fn facts_possible_values(facts: &ConstraintFacts) -> Option<HashSet<i64>> {
    let mut values = facts.exact_values.clone()?;
    if let Some(lower) = facts.lower {
        let lower = bound_min(lower);
        values.retain(|value| *value >= lower);
    }
    if let Some(upper) = facts.upper {
        let upper = bound_max(upper);
        values.retain(|value| *value <= upper);
    }
    values.retain(|value| !facts.excluded_values.contains(value));
    Some(values)
}

fn facts_are_contradictory(facts: &ConstraintFacts) -> bool {
    if let Some(values) = facts_possible_values(facts) {
        return values.is_empty();
    }

    if let (Some(lower), Some(upper)) = (facts.lower, facts.upper) {
        let lower = bound_min(lower);
        let upper = bound_max(upper);
        if lower > upper {
            return true;
        }
        if lower == upper && facts.excluded_values.contains(&lower) {
            return true;
        }
    }

    false
}

fn compare_holds(lhs: i64, op: CompareOp, rhs: i64) -> bool {
    match op {
        CompareOp::Eq => lhs == rhs,
        CompareOp::Neq => lhs != rhs,
        CompareOp::Lt => lhs < rhs,
        CompareOp::Lte => lhs <= rhs,
        CompareOp::Gt => lhs > rhs,
        CompareOp::Gte => lhs >= rhs,
    }
}

fn facts_imply_compare(facts: &ConstraintFacts, op: CompareOp, target: i64) -> bool {
    if let Some(values) = facts_possible_values(facts) {
        return !values.is_empty() && values.iter().all(|value| compare_holds(*value, op, target));
    }

    match op {
        CompareOp::Eq => {
            if let (Some(lower), Some(upper)) = (facts.lower, facts.upper) {
                let lower = bound_min(lower);
                let upper = bound_max(upper);
                lower == target && upper == target && !facts.excluded_values.contains(&target)
            } else {
                false
            }
        }
        CompareOp::Neq => facts
            .lower
            .map(bound_min)
            .zip(facts.upper.map(bound_max))
            .map(|(lower, upper)| target < lower || target > upper)
            .unwrap_or_else(|| facts.excluded_values.contains(&target)),
        CompareOp::Gt => facts
            .lower
            .map(bound_min)
            .is_some_and(|lower| lower > target),
        CompareOp::Gte => facts
            .lower
            .map(bound_min)
            .is_some_and(|lower| lower >= target),
        CompareOp::Lt => facts
            .upper
            .map(bound_max)
            .is_some_and(|upper| upper < target),
        CompareOp::Lte => facts
            .upper
            .map(bound_max)
            .is_some_and(|upper| upper <= target),
    }
}

fn direct_constraint_match(
    assumption: &ConstraintExpr,
    target: &ConstraintExpr,
    subst: &Subst,
) -> bool {
    fn compare_matches(
        lhs: &NumericExpr,
        op: CompareOp,
        rhs: &NumericExpr,
        other_lhs: &NumericExpr,
        other_op: CompareOp,
        other_rhs: &NumericExpr,
        subst: &Subst,
    ) -> bool {
        let lhs = subst_numeric_expr(lhs, subst);
        let rhs = subst_numeric_expr(rhs, subst);
        let other_lhs = subst_numeric_expr(other_lhs, subst);
        let other_rhs = subst_numeric_expr(other_rhs, subst);

        (op == other_op && lhs == other_lhs && rhs == other_rhs)
            || (swapped_compare_op(op) == other_op && lhs == other_rhs && rhs == other_lhs)
    }

    match (assumption, target) {
        (ConstraintExpr::Bool(lhs), ConstraintExpr::Bool(rhs)) => lhs == rhs,
        (
            ConstraintExpr::Compare { lhs, op, rhs },
            ConstraintExpr::Compare {
                lhs: other_lhs,
                op: other_op,
                rhs: other_rhs,
            },
        ) => compare_matches(lhs, *op, rhs, other_lhs, *other_op, other_rhs, subst),
        (
            ConstraintExpr::InSet { value, items },
            ConstraintExpr::InSet {
                value: other_value,
                items: other_items,
            },
        ) => {
            subst_numeric_expr(value, subst) == subst_numeric_expr(other_value, subst)
                && items.len() == other_items.len()
                && items.iter().zip(other_items.iter()).all(|(lhs, rhs)| {
                    subst_numeric_expr(lhs, subst) == subst_numeric_expr(rhs, subst)
                })
        }
        (
            ConstraintExpr::Compare {
                lhs,
                op: CompareOp::Eq,
                rhs,
            },
            ConstraintExpr::InSet { value, items },
        )
        | (
            ConstraintExpr::InSet { value, items },
            ConstraintExpr::Compare {
                lhs,
                op: CompareOp::Eq,
                rhs,
            },
        ) if items.len() == 1 => {
            let lhs = subst_numeric_expr(lhs, subst);
            let rhs = subst_numeric_expr(rhs, subst);
            let value = subst_numeric_expr(value, subst);
            let item = subst_numeric_expr(&items[0], subst);
            (lhs == value && rhs == item) || (lhs == item && rhs == value)
        }
        (ConstraintExpr::Not(lhs), ConstraintExpr::Not(rhs)) => {
            direct_constraint_match(lhs, rhs, subst)
        }
        _ => false,
    }
}

fn collect_constraint_facts(
    constraint: &ConstraintExpr,
    subst: &Subst,
    facts: &mut HashMap<String, ConstraintFacts>,
) -> bool {
    match constraint {
        ConstraintExpr::Bool(true) => false,
        ConstraintExpr::Bool(false) => true,
        ConstraintExpr::And(items) => items
            .iter()
            .any(|item| collect_constraint_facts(item, subst, facts)),
        ConstraintExpr::Compare { lhs, op, rhs } => {
            let lhs = subst_numeric_expr(lhs, subst);
            let rhs = subst_numeric_expr(rhs, subst);
            let lhs_const = eval_numeric_expr(&lhs, subst, &[]);
            let rhs_const = eval_numeric_expr(&rhs, subst, &[]);

            match (lhs_const, rhs_const) {
                (Some(lhs), Some(rhs)) => !compare_holds(lhs, *op, rhs),
                (_, Some(value)) => {
                    let key = numeric_expr_key(&lhs);
                    let entry = facts.entry(key).or_default();
                    constraint_facts_add_compare(entry, *op, value);
                    facts_are_contradictory(entry)
                }
                (Some(value), _) => {
                    let key = numeric_expr_key(&rhs);
                    let entry = facts.entry(key).or_default();
                    constraint_facts_add_compare(entry, swapped_compare_op(*op), value);
                    facts_are_contradictory(entry)
                }
                (None, None) => false,
            }
        }
        ConstraintExpr::InSet { value, items } => {
            let value = subst_numeric_expr(value, subst);
            let item_values = items
                .iter()
                .map(|item| eval_numeric_expr(&subst_numeric_expr(item, subst), subst, &[]))
                .collect::<Option<Vec<_>>>();

            let Some(item_values) = item_values else {
                return false;
            };

            if let Some(value) = eval_numeric_expr(&value, subst, &[]) {
                !item_values.contains(&value)
            } else {
                let key = numeric_expr_key(&value);
                let entry = facts.entry(key).or_default();
                constraint_facts_add_set(entry, item_values.into_iter().collect());
                facts_are_contradictory(entry)
            }
        }
        ConstraintExpr::Or(_) | ConstraintExpr::Not(_) | ConstraintExpr::Unsupported => false,
    }
}

fn constraint_implied_by_facts(
    target: &ConstraintExpr,
    subst: &Subst,
    facts: &HashMap<String, ConstraintFacts>,
) -> bool {
    match target {
        ConstraintExpr::Bool(true) => true,
        ConstraintExpr::Bool(false) => false,
        ConstraintExpr::And(items) => items
            .iter()
            .all(|item| constraint_implied_by_facts(item, subst, facts)),
        ConstraintExpr::Compare { lhs, op, rhs } => {
            let lhs = subst_numeric_expr(lhs, subst);
            let rhs = subst_numeric_expr(rhs, subst);
            match (
                facts.get(&numeric_expr_key(&lhs)),
                eval_numeric_expr(&rhs, subst, &[]),
                eval_numeric_expr(&lhs, subst, &[]),
                facts.get(&numeric_expr_key(&rhs)),
            ) {
                (Some(facts), Some(value), _, _) => facts_imply_compare(facts, *op, value),
                (_, _, Some(value), Some(facts)) => {
                    facts_imply_compare(facts, swapped_compare_op(*op), value)
                }
                _ => false,
            }
        }
        ConstraintExpr::InSet { value, items } => {
            let value = subst_numeric_expr(value, subst);
            let target_values = items
                .iter()
                .map(|item| eval_numeric_expr(&subst_numeric_expr(item, subst), subst, &[]))
                .collect::<Option<HashSet<_>>>();
            let Some(target_values) = target_values else {
                return false;
            };
            facts.get(&numeric_expr_key(&value)).is_some_and(|facts| {
                facts_possible_values(facts)
                    .map(|values| !values.is_empty() && values.is_subset(&target_values))
                    .unwrap_or(false)
            })
        }
        ConstraintExpr::Not(_) | ConstraintExpr::Or(_) | ConstraintExpr::Unsupported => false,
    }
}

fn constraint_implied_by_assumptions(
    assumptions: &[ConstraintExpr],
    target: &ConstraintExpr,
    subst: &Subst,
) -> bool {
    if assumptions
        .iter()
        .any(|assumption| direct_constraint_match(assumption, target, subst))
    {
        return true;
    }

    let mut facts = HashMap::new();
    for assumption in assumptions {
        collect_constraint_facts(assumption, subst, &mut facts);
    }
    constraint_implied_by_facts(target, subst, &facts)
}

fn constraints_are_contradictory(constraints: &[ConstraintExpr], subst: &Subst) -> bool {
    let mut facts = HashMap::new();
    constraints
        .iter()
        .any(|constraint| collect_constraint_facts(constraint, subst, &mut facts))
}

fn unify_value(expected: &str, actual: &str, subst: &mut Subst) -> bool {
    if normalized_value_text(expected) == normalized_value_text(actual) {
        return true;
    }

    // Conditional types: `if cond then N else M` cannot be evaluated without
    // knowing `cond`. The local LSP type checker has no SMT solver, so be
    // permissive — accept any actual that COULD match either branch.
    let is_conditional = |s: &str| {
        let t = s.trim();
        (t.starts_with("if ") || t.contains(" if "))
            && t.contains(" then ")
            && t.contains(" else ")
    };
    if is_conditional(expected) || is_conditional(actual) {
        return true;
    }

    if expected.starts_with('\'') {
        match subst.values.get(expected) {
            Some(bound) => {
                let bound = bound.clone();
                bound == actual || unify_value(&bound, actual, subst)
            }
            None => {
                subst
                    .values
                    .insert(expected.to_string(), actual.to_string());
                true
            }
        }
    } else if actual.starts_with('\'') {
        // Symmetric: if actual is a type variable, try to bind it.
        match subst.values.get(actual) {
            Some(bound) => {
                let bound = bound.clone();
                bound == expected || unify_value(expected, &bound, subst)
            }
            None => {
                subst
                    .values
                    .insert(actual.to_string(), expected.to_string());
                true
            }
        }
    } else if let (Some(expected), Some(actual)) = (
        parse_numeric_expr_text(expected),
        parse_numeric_expr_text(actual),
    ) {
        unify_numeric_expr(&expected, &actual, subst)
    } else {
        normalized_value_text(expected) == normalized_value_text(actual)
    }
}

fn apply_subst(ty: &Ty, subst: &Subst) -> Ty {
    match ty.kind() {
        TyData::Unknown => ty.clone(),
        TyData::Text(_) => ty.clone(),
        TyData::Var(name) => subst
            .types
            .get(name)
            .cloned()
            .unwrap_or_else(|| ty.clone()),
        TyData::Tuple(items) => {
            Ty::tuple(items.iter().map(|item| apply_subst(item, subst)).collect())
        }
        TyData::Function { params, ret } => Ty::function(
            params
                .iter()
                .map(|param| apply_subst(param, subst))
                .collect(),
            apply_subst(ret, subst),
        ),
        TyData::App { name, args, .. } => {
            let args = args
                .iter()
                .map(|arg| match arg {
                    TyArg::Type(t) => TyArg::Type(apply_subst(t, subst)),
                    TyArg::Value(value) => TyArg::Value(
                        subst
                            .values
                            .get(value)
                            .cloned()
                            .unwrap_or_else(|| value.clone()),
                    ),
                })
                .collect::<Vec<_>>();
            let text = app_text(name, &args);
            Ty::app(name.clone(), args, text)
        }
    }
}

/// Whether a textual type name is one of Sail's numeric scalar types,
/// including parameterised forms like `range(0, 10)` or `atom('n)`.
fn is_numeric_text(t: &str) -> bool {
    t == "int"
        || t == "nat"
        || t.starts_with("range(")
        || t.starts_with("atom(")
        || t.starts_with("int(")
        || t.starts_with("nat(")
}

/// Cheap structural test: is `ty` a Sail numeric scalar type
/// (`int`, `nat`, or `range(_)` / `atom(_)` / `int(_)` / `nat(_)`)?
/// Allocation-free; replaces a series of `.display_text().starts_with("range(")`
/// fallbacks that used to dominate `unify`'s hot path.
fn is_numeric_scalar_ty(ty: &Ty) -> bool {
    match ty.kind() {
        TyData::Text(t) => t == "int" || t == "nat",
        TyData::App { name, .. } => {
            matches!(name.as_str(), "range" | "atom" | "int" | "nat")
        }
        _ => false,
    }
}

/// Whether `ty` is something the checker classes as a "primitive scalar"
/// for the purposes of accepting cross-file aliases. Mirrors the previous
/// `is_actual_primitive` check in `unify`, but without going through
/// `Ty::display_text()`.
fn is_primitive_or_bits_ty(ty: &Ty) -> bool {
    match ty.kind() {
        TyData::Text(t) => matches!(
            t.as_str(),
            "int" | "nat" | "bool" | "string" | "unit" | "real" | "bit" | "_"
        ),
        TyData::App { name, .. } => {
            matches!(name.as_str(), "bits" | "range" | "atom" | "int" | "nat")
        }
        _ => false,
    }
}

/// Extract the bitvector width if `ty` looks like `bits(N)` or `bit`
/// (which is `bits(1)`). Returns the width string from `Ty::App`'s value
/// arg without going through `Ty::display_text()`.
fn bits_width<'a>(ty: &'a Ty) -> Option<&'a str> {
    match ty.kind() {
        TyData::Text(t) if t == "bit" => Some("1"),
        TyData::App { name, args, .. } if name == "bits" => match args.first() {
            Some(TyArg::Value(width)) => Some(width.as_str()),
            _ => None,
        },
        _ => None,
    }
}

/// Maximum recursion depth for `unify`. Sail signatures rarely nest
/// types more than ~10 levels (`forall ... vector(N, struct{...})`), so
/// 96 leaves a healthy safety margin while still tripping a runaway
/// before the worker thread's 64 MiB stack overflows.
const UNIFY_DEPTH_LIMIT: usize = 96;

fn unify(expected: &Ty, actual: &Ty, subst: &mut Subst) -> bool {
    unify_inner(expected, actual, subst, 0)
}

fn unify_inner(expected: &Ty, actual: &Ty, subst: &mut Subst, depth: usize) -> bool {
    if depth > UNIFY_DEPTH_LIMIT {
        // Refuse to recurse further. Conservatively accept — the
        // alternative is reporting a spurious mismatch on a deeply
        // nested type we couldn't fully walk.
        return true;
    }
    // Symmetric early-out for Unknown: either side being Unknown means we
    // can't verify types (typically a cross-file reference), so we accept.
    if actual.is_unknown() {
        return true;
    }
    match expected.kind() {
        TyData::Unknown => true,
        TyData::Var(name) => {
            if matches!(actual.kind(), TyData::Var(actual_name) if actual_name == name) {
                return true;
            }
            if ty_contains_var(actual, name) {
                return false;
            }
            match subst.types.get(name).cloned() {
                Some(bound) => unify_inner(&bound, actual, subst, depth + 1),
                None => {
                    subst.types.insert(name.clone(), actual.clone());
                    true
                }
            }
        }
        TyData::Text(expected) => {
            // Tuples and Functions can never match a text type. Bail out
            // before paying for `actual.display_text()`.
            if matches!(actual.kind(), TyData::Tuple(_) | TyData::Function { .. }) {
                return false;
            }
            // Direct text match.
            if let TyData::Text(actual_text) = actual.kind() {
                if expected == actual_text {
                    return true;
                }
                // bit ≡ bits(1) — check via the textual form on the left
                // (the App-side analogue is handled lower down).
                if (expected == "bit" && actual_text == "bits(1)")
                    || (expected == "bits(1)" && actual_text == "bit")
                {
                    return true;
                }
                // Two different primitives are not equivalent unless they
                // are both numeric scalars (which fall into the structural
                // numeric check below).
                let primitives = [
                    "int", "nat", "bool", "string", "unit", "real", "bit", "_",
                ];
                let exp_prim = primitives.contains(&expected.as_str());
                let act_prim = primitives.contains(&actual_text.as_str());
                if exp_prim
                    && act_prim
                    && !(is_numeric_text(expected) && is_numeric_text(actual_text))
                {
                    return false;
                }
            }
            // Sail subtyping: int ↔ range(...) ↔ atom(...) ↔ nat ↔ int(N)
            // are all numeric and the LSP can't verify exact constraints.
            if is_numeric_text(expected) && is_numeric_scalar_ty(actual) {
                return true;
            }
            // bit ≡ bits(1) (App form on the right).
            if expected == "bit" {
                if let Some(width) = bits_width(actual) {
                    return width.trim() == "1";
                }
            }
            // bits(N) form on the LHS string vs structured `Ty::App` on RHS.
            if expected.starts_with("bits(") && expected.ends_with(')') {
                let expected_width = &expected["bits(".len()..expected.len() - 1];
                if let Some(actual_width) = bits_width(actual) {
                    let exp_num = expected_width.parse::<i64>().ok();
                    let act_num = actual_width.parse::<i64>().ok();
                    return match (exp_num, act_num) {
                        (Some(a), Some(b)) => a == b,
                        // Either side has a type variable / arithmetic — we
                        // can't decide without SMT, so be permissive.
                        _ => true,
                    };
                }
            }
            // Cross-file type aliases (e.g. xlenbits = bits(64)) are
            // unknown to the local type checker. If either side is a non-
            // primitive type name we can't resolve, treat them as compatible.
            let primitives = [
                "int", "nat", "bool", "string", "unit", "real", "bit", "_",
            ];
            let is_expected_primitive = primitives.contains(&expected.as_str());
            let is_actual_primitive = is_primitive_or_bits_ty(actual);
            if !is_expected_primitive || !is_actual_primitive {
                return true;
            }
            false
        }
        TyData::Tuple(expected_items) => match actual.kind() {
            TyData::Tuple(actual_items) if expected_items.len() == actual_items.len() => {
                expected_items
                    .iter()
                    .zip(actual_items.iter())
                    .all(|(e, a)| unify_inner(e, a, subst, depth + 1))
            }
            _ => false,
        },
        TyData::Function {
            params: expected_params,
            ret: expected_ret,
        } => match actual.kind() {
            TyData::Function {
                params: actual_params,
                ret: actual_ret,
            } if expected_params.len() == actual_params.len() => {
                expected_params
                    .iter()
                    .zip(actual_params.iter())
                    .all(|(e, a)| unify_inner(e, a, subst, depth + 1))
                    && unify_inner(expected_ret, actual_ret, subst, depth + 1)
            }
            _ => false,
        },
        TyData::App {
            name: expected_name,
            args: expected_args,
            ..
        } => {
            // Sail subtyping: range/atom/nat/int and parameterized int(N) /
            // atom(N) / nat(N) are all numeric. Structural check, no
            // string allocation.
            if matches!(expected_name.as_str(), "range" | "atom" | "int" | "nat")
                && is_numeric_scalar_ty(actual)
            {
                return true;
            }
            // bit ≡ bits(1) — accept either direction.
            if expected_name == "bits"
                && matches!(actual.kind(), TyData::Text(t) if t == "bit")
            {
                if let Some(TyArg::Value(width)) = expected_args.first() {
                    if width.trim() == "1" {
                        return true;
                    }
                }
            }
            // bits(N) ≡ vector(N, bit) (Sail equivalence). Structural,
            // both directions handled.
            if expected_name == "bits" {
                if let TyData::App {
                    name: a_name,
                    args: a_args,
                    ..
                } = actual.kind()
                {
                    if a_name == "vector" {
                        if let (Some(TyArg::Value(actual_n)), Some(TyArg::Type(elem))) =
                            (a_args.first(), a_args.get(1))
                        {
                            if matches!(elem.kind(), TyData::Text(t) if t == "bit") {
                                if let Some(TyArg::Value(expected_n)) = expected_args.first() {
                                    return unify_value(expected_n, actual_n, subst);
                                }
                            }
                        }
                    }
                }
            }
            if expected_name == "vector" {
                if let Some(actual_n) = bits_width(actual) {
                    if let Some(TyArg::Value(expected_n)) = expected_args.first() {
                        if let Some(TyArg::Type(elem)) = expected_args.get(1) {
                            if matches!(elem.kind(), TyData::Text(t) if t == "bit") {
                                return unify_value(expected_n, actual_n, subst);
                            }
                        }
                    }
                }
            }
            match actual.kind() {
                TyData::App {
                    name: actual_name,
                    args: actual_args,
                    ..
                } if expected_name == actual_name
                    && expected_args.len() == actual_args.len() =>
                {
                    expected_args
                        .iter()
                        .zip(actual_args.iter())
                        .all(|(expected, actual)| match (expected, actual) {
                            (TyArg::Type(expected), TyArg::Type(actual)) => {
                                unify_inner(expected, actual, subst, depth + 1)
                            }
                            (TyArg::Value(expected), TyArg::Value(actual)) => {
                                unify_value(expected, actual, subst)
                            }
                            (TyArg::Value(expected), TyArg::Type(actual)) => {
                                unify_value(expected, &actual.display_text(), subst)
                            }
                            (TyArg::Type(expected), TyArg::Value(actual)) => {
                                unify_inner(
                                    expected,
                                    &Ty::text(actual.clone()),
                                    subst,
                                    depth + 1,
                                )
                            }
                        })
                }
                _ => false,
            }
        }
    }
}

/// Pretty-print a `TypeScheme` as a Sail-style signature, e.g.
/// `forall 'n, 'm, 'n > 0. (bits('n), int('m)) -> bits('n + 'm)`.
/// Used to enrich `UnresolvedQuants` diagnostics so users see which
/// callable shape their unresolved type variables came from.
fn format_scheme_signature(scheme: &TypeScheme) -> String {
    let mut header = String::new();
    if !scheme.quantifiers.is_empty() || !scheme.constraints.is_empty() {
        header.push_str("forall ");
        let parts = scheme
            .quantifiers
            .iter()
            .cloned()
            .chain(scheme.constraints.iter().map(|c| c.text.clone()))
            .collect::<Vec<_>>();
        header.push_str(&parts.join(", "));
        header.push_str(". ");
    }
    let params = scheme
        .params
        .iter()
        .map(|p| p.display_text())
        .collect::<Vec<_>>()
        .join(", ");
    let ret = scheme.ret.display_text();
    if scheme.params.len() == 1 {
        format!("{header}{params} -> {ret}")
    } else {
        format!("{header}({params}) -> {ret}")
    }
}

/// Pretty-print a `MappingScheme` as `lhs <-> rhs` plus quantifiers.
fn format_mapping_signature(scheme: &MappingScheme) -> String {
    let mut header = String::new();
    if !scheme.quantifiers.is_empty() || !scheme.constraints.is_empty() {
        header.push_str("forall ");
        let parts = scheme
            .quantifiers
            .iter()
            .cloned()
            .chain(scheme.constraints.iter().map(|c| c.text.clone()))
            .collect::<Vec<_>>();
        header.push_str(&parts.join(", "));
        header.push_str(". ");
    }
    format!("{header}{} <-> {}", scheme.lhs.display_text(), scheme.rhs.display_text())
}

/// Map a typechecker `Ty` into the language-agnostic `MatchTy` consumed
/// by the pattern usefulness algorithm. Anything outside the supported
/// subset (functions, vars, App-with-args we don't model) collapses to
/// `Unknown`, which the algorithm treats as having an unlistable
/// constructor universe (i.e. a wildcard arm is required).
fn ty_to_match_ty(ty: &Ty) -> MatchTy {
    match ty.kind() {
        TyData::Text(name) if name == "bool" => MatchTy::Bool,
        TyData::Text(name) => MatchTy::Named(name.clone()),
        TyData::App { name, .. } => MatchTy::Named(name.clone()),
        TyData::Tuple(items) => MatchTy::Tuple(items.iter().map(ty_to_match_ty).collect()),
        TyData::Unknown | TyData::Var(_) | TyData::Function { .. } => MatchTy::Unknown,
    }
}

struct Checker<'a> {
    file: &'a File,
    source: &'a str,
    env: TopLevelEnv,
    pattern_constants: HashSet<String>,
    diagnostics: Vec<Diagnostic>,
    expr_types: HashMap<SpanKey, String>,
    binding_types: HashMap<SpanKey, String>,
    seen_errors: HashSet<(DiagnosticCode, usize, usize, TypeError)>,
    cancel: CancellationToken,
    /// Set to `true` while we're walking an l-expression's call form
    /// (e.g. the LHS of `wX(idx) = data`). The cross-file arity check
    /// uses this to allow `arg_count == total - 1`, since Sail's setter
    /// desugaring leaves the LHS call site one argument short of the
    /// underlying signature.
    in_lexp_call: bool,
}

struct ConcatOperandInfo {
    width: String,
    elem: Ty,
    is_vector: bool,
}

impl<'a> Checker<'a> {
    fn new(file: &'a File, env: TopLevelEnv, pattern_constants: HashSet<String>) -> Self {
        Self::with_cancel(file, env, pattern_constants, CancellationToken::never())
    }

    fn with_cancel(
        file: &'a File,
        env: TopLevelEnv,
        pattern_constants: HashSet<String>,
        cancel: CancellationToken,
    ) -> Self {
        Self {
            file,
            source: file.source.text(),
            env,
            pattern_constants,
            diagnostics: Vec::new(),
            expr_types: HashMap::new(),
            binding_types: HashMap::new(),
            seen_errors: HashSet::new(),
            cancel,
            in_lexp_call: false,
        }
    }

    fn finish(self) -> TypeCheckResult {
        TypeCheckResult {
            diagnostics: self.diagnostics,
            expr_types: self.expr_types,
            binding_types: self.binding_types,
        }
    }

    fn trace_typecheck(&self, kind: &str, name: &str, span: Option<Span>) {
        if std::env::var_os("SAIL_TYPECHECK_TRACE").is_none() {
            return;
        }
        if let Some(span) = span {
            let pos = self.file.source.position_at(span.start);
            eprintln!(
                "[typecheck] {kind} {name} @ {}:{}",
                pos.line + 1,
                pos.character + 1
            );
        } else {
            eprintln!("[typecheck] {kind} {name}");
        }
    }

    fn push_error(&mut self, code: DiagnosticCode, span: Span, error: TypeError) {
        let key = (code.clone(), span.start, span.end, error.clone());
        if !self.seen_errors.insert(key) {
            return;
        }
        self.diagnostics.push(diagnostic_for_error(
            self.file,
            code,
            ReportingError::Type { span, error },
        ));
    }

    fn record_expr_type(&mut self, span: Span, ty: &Ty) {
        if !ty.is_unknown() {
            self.expr_types.insert((span.start, span.end), ty.display_text());
        }
    }

    fn record_binding_type(&mut self, span: Span, ty: &Ty) {
        if !ty.is_unknown() {
            self.binding_types.insert((span.start, span.end), ty.display_text());
        }
    }

    /// Unify two types, resolving cross-file type aliases on both sides first.
    /// Use this instead of calling the bare `unify` free function whenever
    /// you have access to a `Checker`.
    fn unify_with_aliases(&self, expected: &Ty, actual: &Ty, subst: &mut Subst) -> bool {
        let expected = self.env.resolve_alias(expected);
        let actual = self.env.resolve_alias(actual);
        unify(&expected, &actual, subst)
    }

    fn expect_type(&mut self, span: Span, actual: &Ty, expected: &Ty) -> bool {
        // Skip checks involving Unknown — these come from cross-file references
        // (functions, constants, registers) that the per-file type checker
        // cannot resolve. Reporting subtype errors against Unknown produces
        // thousands of false positives.
        if actual.is_unknown() || expected.is_unknown() {
            return true;
        }
        // Type variables (e.g. polymorphic 'm, 'n in `forall 'n. bits('n)`)
        // should match any type for LSP purposes — we don't track kinds.
        if matches!(actual.kind(), TyData::Var(_)) || matches!(expected.kind(), TyData::Var(_)) {
            return true;
        }
        // Resolve type aliases on both sides (e.g. xlenbits → bits(64)) before
        // unification so cross-file aliases compare correctly.
        let actual_resolved = self.env.resolve_alias(actual);
        let expected_resolved = self.env.resolve_alias(expected);
        let mut subst = Subst::default();
        if unify(&expected_resolved, &actual_resolved, &mut subst) {
            true
        } else {
            self.push_error(
                DiagnosticCode::TypeError,
                span,
                TypeError::Subtype {
                    lhs: actual.display_text(),
                    rhs: expected.display_text(),
                    constraint: None,
                },
            );
            false
        }
    }

    fn expect_int_type(&mut self, span: Span, actual: &Ty) -> bool {
        self.expect_type(span, actual, &Ty::text("int".to_string()))
    }

    fn quantifier_is_bound(&self, name: &str, subst: &Subst) -> bool {
        subst.values.contains_key(name) || subst.types.contains_key(name)
    }

    fn fill_assumptions(&self, locals: &LocalEnv, out: &mut Vec<ConstraintExpr>) {
        out.clear();
        out.extend(self.env.global_constraints.iter().cloned());
        out.extend(locals.constraints.iter().cloned());
    }

    fn evaluate_constraint(
        &self,
        expr: &ConstraintExpr,
        subst: &Subst,
        assumptions: &[ConstraintExpr],
    ) -> ConstraintStatus {
        if constraint_implied_by_assumptions(assumptions, expr, subst) {
            return ConstraintStatus::Satisfied;
        }

        match expr {
            ConstraintExpr::Bool(true) => ConstraintStatus::Satisfied,
            ConstraintExpr::Bool(false) => ConstraintStatus::Failed,
            ConstraintExpr::Compare { lhs, op, rhs } => {
                let (Some(lhs), Some(rhs)) = (
                    eval_numeric_expr(lhs, subst, assumptions),
                    eval_numeric_expr(rhs, subst, assumptions),
                ) else {
                    return ConstraintStatus::Unknown;
                };
                let holds = match op {
                    CompareOp::Eq => lhs == rhs,
                    CompareOp::Neq => lhs != rhs,
                    CompareOp::Lt => lhs < rhs,
                    CompareOp::Lte => lhs <= rhs,
                    CompareOp::Gt => lhs > rhs,
                    CompareOp::Gte => lhs >= rhs,
                };
                if holds {
                    ConstraintStatus::Satisfied
                } else {
                    ConstraintStatus::Failed
                }
            }
            ConstraintExpr::InSet { value, items } => {
                let Some(value) = eval_numeric_expr(value, subst, assumptions) else {
                    return ConstraintStatus::Unknown;
                };
                let mut all_known = true;
                for item in items {
                    match eval_numeric_expr(item, subst, assumptions) {
                        Some(item) if item == value => return ConstraintStatus::Satisfied,
                        Some(_) => {}
                        None => all_known = false,
                    }
                }
                if all_known {
                    ConstraintStatus::Failed
                } else {
                    ConstraintStatus::Unknown
                }
            }
            ConstraintExpr::And(items) => {
                let mut saw_unknown = false;
                for item in items {
                    match self.evaluate_constraint(item, subst, assumptions) {
                        ConstraintStatus::Satisfied => {}
                        ConstraintStatus::Failed => return ConstraintStatus::Failed,
                        ConstraintStatus::Unknown => saw_unknown = true,
                    }
                }
                if saw_unknown {
                    ConstraintStatus::Unknown
                } else {
                    ConstraintStatus::Satisfied
                }
            }
            ConstraintExpr::Or(items) => {
                let mut saw_unknown = false;
                for item in items {
                    match self.evaluate_constraint(item, subst, assumptions) {
                        ConstraintStatus::Satisfied => return ConstraintStatus::Satisfied,
                        ConstraintStatus::Failed => {}
                        ConstraintStatus::Unknown => saw_unknown = true,
                    }
                }
                if saw_unknown {
                    ConstraintStatus::Unknown
                } else {
                    ConstraintStatus::Failed
                }
            }
            ConstraintExpr::Not(inner) => match self.evaluate_constraint(inner, subst, assumptions)
            {
                ConstraintStatus::Satisfied => ConstraintStatus::Failed,
                ConstraintStatus::Failed => ConstraintStatus::Satisfied,
                ConstraintStatus::Unknown => ConstraintStatus::Unknown,
            },
            ConstraintExpr::Unsupported => ConstraintStatus::Unknown,
        }
    }

    fn instantiation_error_with_sig(
        &self,
        id: &str,
        quantifiers: &[String],
        constraints: &[QuantConstraint],
        subst: &Subst,
        assumptions: &[ConstraintExpr],
        signature: Option<String>,
    ) -> Option<TypeError> {
        let mut unresolved = quantifiers
            .iter()
            .filter(|quantifier| !self.quantifier_is_bound(quantifier, subst))
            .cloned()
            .collect::<Vec<_>>();

        for constraint in constraints {
            if constraint
                .mentions
                .iter()
                .any(|name| quantifiers.contains(name) && !self.quantifier_is_bound(name, subst))
            {
                unresolved.push(constraint.text.clone());
                continue;
            }

            let status = self.evaluate_constraint(&constraint.expr, subst, assumptions);
            match status {
                ConstraintStatus::Satisfied => {}
                ConstraintStatus::Failed => {
                    return Some(TypeError::FailedConstraint {
                        constraint: constraint.text.clone(),
                        derived_from: Vec::new(),
                    });
                }
                ConstraintStatus::Unknown => unresolved.push(constraint.text.clone()),
            }
        }

        unresolved.sort();
        unresolved.dedup();
        (!unresolved.is_empty()).then_some(TypeError::UnresolvedQuants {
            id: id.to_string(),
            quants: unresolved,
            signature,
        })
    }

    fn add_expr_constraint(&self, locals: &mut LocalEnv, expr: &Spanned<Expr>, positive: bool) {
        if let Some(constraint) = constraint_expr_from_expr(self.source, expr, positive) {
            locals.add_constraint(constraint);
        }
    }

    fn propagate_post_expr_constraints(&self, expr: &Spanned<Expr>, locals: &mut LocalEnv) {
        match &expr.0 {
            Expr::Assert { condition, .. } => self.add_expr_constraint(locals, condition, true),
            Expr::If {
                cond,
                then_branch,
                else_branch: None,
            } if matches!(then_branch.0, Expr::Throw(_) | Expr::Exit(_)) => {
                self.add_expr_constraint(locals, cond, false);
            }
            _ => {}
        }
    }

    fn record_info_for_type(&self, ty: &Ty) -> Option<(String, RecordInfo, Subst)> {
        match ty.kind() {
            TyData::Text(name) => self
                .env
                .records
                .get(name)
                .cloned()
                .map(|info| (name.clone(), info, Subst::default())),
            TyData::App { name, args, .. } => {
                let info = self.env.records.get(name)?.clone();
                let mut subst = Subst::default();
                for (param, arg) in info.params.iter().zip(args.iter()) {
                    match arg {
                        TyArg::Type(ty) => {
                            subst.types.insert(param.clone(), ty.clone());
                            subst.values.insert(param.clone(), ty.display_text());
                        }
                        TyArg::Value(value) => {
                            subst.values.insert(param.clone(), value.clone());
                        }
                    }
                }
                Some((name.clone(), info, subst))
            }
            _ => None,
        }
    }

    fn record_field_type(&self, ty: &Ty, field: &str) -> Option<Ty> {
        let (_, info, subst) = self.record_info_for_type(ty)?;
        info.fields
            .get(field)
            .map(|field_ty| apply_subst(field_ty, &subst))
    }

    fn register_type_for_name(&self, name: &str) -> Option<Ty> {
        self.env.registers.get(name).cloned()
    }

    fn bitfield_info_for_type(&self, ty: &Ty) -> Option<(String, BitfieldInfo)> {
        match ty.kind() {
            TyData::Text(name) => self
                .env
                .bitfields
                .get(name)
                .cloned()
                .map(|info| (name.clone(), info)),
            _ => None,
        }
    }

    fn bitfield_field_type(&self, ty: &Ty, field: &str) -> Option<Ty> {
        let (_, info) = self.bitfield_info_for_type(ty)?;
        if field == "bits" {
            Some(info.underlying)
        } else {
            info.fields.get(field).cloned()
        }
    }

    fn infer_shorthand_binding(
        &mut self,
        name: &Spanned<String>,
        locals: &mut LocalEnv,
    ) -> Option<Ty> {
        if let Some(ty) = self.env.lookup_value(locals, &name.0) {
            self.record_binding_type(name.1, &ty);
            Some(ty)
        } else {
            // Cross-file binding — silently skip.
            None
        }
    }

    fn field_name_from_expr(&self, expr: &Spanned<Expr>) -> Option<String> {
        match &expr.0 {
            Expr::Ident(name) => Some(name.clone()),
            Expr::Field { field, .. } => Some(field.0.clone()),
            _ => None,
        }
    }

    fn lexp_to_expr(&self, lexp: &Spanned<Lexp>) -> Spanned<Expr> {
        match &lexp.0 {
            Lexp::Attribute { attr, lexp: inner } => (
                Expr::Attribute {
                    attr: attr.clone(),
                    expr: Box::new(self.lexp_to_expr(inner)),
                },
                lexp.1,
            ),
            Lexp::Typed { lexp: inner, ty } => (
                Expr::Cast {
                    expr: Box::new(self.lexp_to_expr(inner)),
                    ty: ty.clone(),
                },
                lexp.1,
            ),
            Lexp::Id(name) => (Expr::Ident(name.clone()), lexp.1),
            Lexp::Deref(_) => (
                Expr::Error("unsupported deref l-expression".to_string()),
                lexp.1,
            ),
            Lexp::Call(call) => (Expr::Call(call.clone()), lexp.1),
            Lexp::Field { lexp: inner, field } => (
                Expr::Field {
                    expr: Box::new(self.lexp_to_expr(inner)),
                    field: field.clone(),
                },
                lexp.1,
            ),
            Lexp::Vector { lexp: inner, index } => (
                Expr::Call(Call {
                    callee: Box::new((Expr::Ident("vector_access#".to_string()), index.1)),
                    args: vec![self.lexp_to_expr(inner), index.clone()],
                    open_span: index.1,
                    close_span: index.1,
                    arg_separator_spans: Vec::new(),
                }),
                lexp.1,
            ),
            Lexp::VectorRange {
                lexp: inner,
                start,
                end,
            } => (
                Expr::Call(Call {
                    callee: Box::new((Expr::Ident("vector_subrange#".to_string()), start.1)),
                    args: vec![self.lexp_to_expr(inner), start.clone(), end.clone()],
                    open_span: start.1,
                    close_span: end.1,
                    arg_separator_spans: Vec::new(),
                }),
                lexp.1,
            ),
            Lexp::VectorConcat(items) => {
                let mut items = items.iter().map(|item| self.lexp_to_expr(item));
                let Some(first) = items.next() else {
                    return (
                        Expr::Error("empty vector concat l-expression".to_string()),
                        lexp.1,
                    );
                };
                let expr = items.fold(first, |lhs, rhs| {
                    (
                        Expr::Infix {
                            lhs: Box::new(lhs),
                            op: ("@".to_string(), lexp.1),
                            rhs: Box::new(rhs),
                        },
                        lexp.1,
                    )
                });
                expr
            }
            Lexp::Tuple(items) => (
                Expr::Tuple(items.iter().map(|item| self.lexp_to_expr(item)).collect()),
                lexp.1,
            ),
            Lexp::Error(message) => (Expr::Error(message.clone()), lexp.1),
        }
    }

    fn lexp_assignment_kind(
        &self,
        lexp: &Spanned<Lexp>,
        locals: &LocalEnv,
    ) -> TargetAssignmentKind {
        match &lexp.0 {
            Lexp::Attribute { lexp, .. } | Lexp::Typed { lexp, .. } => {
                self.lexp_assignment_kind(lexp, locals)
            }
            Lexp::Id(name) => {
                if locals.lookup(name).is_some()
                    || self.env.values.contains_key(name)
                    || self.register_type_for_name(name).is_some()
                {
                    TargetAssignmentKind::Update
                } else {
                    TargetAssignmentKind::Declaration
                }
            }
            Lexp::Tuple(items) | Lexp::VectorConcat(items) => {
                let mut saw_declaration = false;
                let mut saw_update = false;
                for item in items {
                    match self.lexp_assignment_kind(item, locals) {
                        TargetAssignmentKind::Declaration => saw_declaration = true,
                        TargetAssignmentKind::Update => saw_update = true,
                        TargetAssignmentKind::Mixed => {
                            saw_declaration = true;
                            saw_update = true;
                        }
                    }
                }
                match (saw_declaration, saw_update) {
                    (true, true) => TargetAssignmentKind::Mixed,
                    (true, false) => TargetAssignmentKind::Declaration,
                    _ => TargetAssignmentKind::Update,
                }
            }
            Lexp::Deref(_)
            | Lexp::Call(_)
            | Lexp::Field { .. }
            | Lexp::Vector { .. }
            | Lexp::VectorRange { .. }
            | Lexp::Error(_) => TargetAssignmentKind::Update,
        }
    }

    fn lexp_annotation_type(&self, lexp: &Spanned<Lexp>) -> Option<Ty> {
        match &lexp.0 {
            Lexp::Attribute { lexp, .. } => self.lexp_annotation_type(lexp),
            Lexp::Typed { ty, .. } => Some(type_from_type_expr(self.source, ty)),
            _ => None,
        }
    }

    fn local_name_from_lexp(&self, lexp: &Spanned<Lexp>) -> Option<(String, Span)> {
        match &lexp.0 {
            Lexp::Attribute { lexp, .. } | Lexp::Typed { lexp, .. } => {
                self.local_name_from_lexp(lexp)
            }
            Lexp::Id(name) => Some((name.clone(), lexp.1)),
            _ => None,
        }
    }

    fn infer_lexp(&mut self, lexp: &Spanned<Lexp>, locals: &mut LocalEnv) -> Ty {
        match &lexp.0 {
            Lexp::Attribute { lexp, .. } => self.infer_lexp(lexp, locals),
            Lexp::Typed { lexp: inner, ty } => {
                let annotated = type_from_type_expr(self.source, ty);
                let actual = self.infer_lexp(inner, locals);
                if !actual.is_unknown() {
                    self.expect_type(lexp.1, &actual, &annotated);
                }
                annotated
            }
            Lexp::Deref(expr) => {
                let inner_ty = self.infer_expr(expr, locals);
                match inner_ty.kind() {
                    TyData::App { name, args, .. } if name == "register" => args
                        .iter()
                        .next()
                        .and_then(|arg| match arg {
                            TyArg::Type(ty) => Some(ty.clone()),
                            TyArg::Value(_) => None,
                        })
                        .unwrap_or(Ty::unknown()),
                    _ => {
                        self.push_error(
                            DiagnosticCode::TypeError,
                            lexp.1,
                            TypeError::other(format!(
                                "Cannot dereference non-register type {}",
                                inner_ty.display_text()
                            )),
                        );
                        Ty::unknown()
                    }
                }
            }
            _ => {
                // Mark the recursive infer_expr call as l-expression
                // context so the cross-file arity check tolerates the
                // setter-desugaring "off by one" pattern (`wX(idx) =
                // data` parses as a 1-arg call but the underlying
                // signature expects 2 args).
                let prev = self.in_lexp_call;
                self.in_lexp_call = true;
                let lowered = self.lexp_to_expr(lexp);
                let ty = self.infer_expr(&lowered, locals);
                self.in_lexp_call = prev;
                ty
            }
        }
    }

    fn infer_var_target_value(
        &mut self,
        target: &Spanned<Lexp>,
        value: &Spanned<Expr>,
        locals: &mut LocalEnv,
    ) -> Ty {
        if let Some(target_ty) = self.lexp_annotation_type(target) {
            self.check_expr(value, &target_ty, locals);
            target_ty
        } else {
            self.infer_expr(value, locals)
        }
    }

    fn bind_var_target_declaration(
        &mut self,
        target: &Spanned<Lexp>,
        value_ty: &Ty,
        locals: &mut LocalEnv,
    ) {
        match self.lexp_assignment_kind(target, locals) {
            TargetAssignmentKind::Declaration => {
                if let Some((name, span)) = self.local_name_from_lexp(target) {
                    locals.define(&name, value_ty.clone());
                    self.record_binding_type(span, value_ty);
                }
            }
            TargetAssignmentKind::Update => {
                self.push_error(
                    DiagnosticCode::TypeError,
                    target.1,
                    TypeError::other(
                        "var expression can only be used to declare new variables, not update them"
                            .to_string(),
                    ),
                );
            }
            TargetAssignmentKind::Mixed => {
                self.push_error(
                    DiagnosticCode::TypeError,
                    target.1,
                    TypeError::other(
                        "var expression cannot mix new declarations with updates".to_string(),
                    ),
                );
            }
        }
    }

    fn collection_element_type(&self, ty: &Ty) -> Option<Ty> {
        match ty.kind() {
            TyData::App { name, args, .. } if name == "list" => {
                args.first().and_then(|arg| match arg {
                    TyArg::Type(ty) => Some(ty.clone()),
                    TyArg::Value(_) => None,
                })
            }
            TyData::App { name, args, .. } if name == "vector" => {
                args.last().and_then(|arg| match arg {
                    TyArg::Type(ty) => Some(ty.clone()),
                    TyArg::Value(_) => None,
                })
            }
            TyData::App { name, .. } if name == "bits" => Some(Ty::text("bit".to_string())),
            _ => None,
        }
    }

    fn collection_length_text(&self, ty: &Ty) -> Option<String> {
        match ty.kind() {
            TyData::App { name, args, .. } if name == "vector" || name == "bits" => {
                args.first().and_then(|arg| match arg {
                    TyArg::Value(value) => Some(value.clone()),
                    TyArg::Type(ty) => Some(ty.display_text()),
                })
            }
            _ => None,
        }
    }

    fn collection_length_expr(&self, ty: &Ty) -> Option<NumericExpr> {
        self.collection_length_text(ty)
            .and_then(|text| parse_numeric_expr_text(&text))
    }

    fn collection_slice_type(&self, ty: &Ty, len_text: String) -> Option<Ty> {
        match ty.kind() {
            TyData::App { name, .. } if name == "bits" => Some(bits_ty(len_text)),
            TyData::App { name, .. } if name == "vector" => self
                .collection_element_type(ty)
                .map(|elem_ty| vector_ty(len_text, elem_ty)),
            _ => None,
        }
    }

    fn prove_required_constraint(
        &mut self,
        span: Span,
        constraint: ConstraintExpr,
        text: String,
        locals: &LocalEnv,
    ) {
        let mut assumptions = Vec::new();
        self.fill_assumptions(locals, &mut assumptions);
        // Only report when the constraint is provably Failed. Without an SMT
        // solver and without cross-file context, many valid constraints get
        // ConstraintStatus::Unknown — reporting them as errors floods users
        // with false positives on perfectly correct code.
        if matches!(
            self.evaluate_constraint(&constraint, &Subst::default(), &assumptions),
            ConstraintStatus::Failed
        ) {
            self.push_error(
                DiagnosticCode::TypeError,
                span,
                TypeError::FailedConstraint {
                    constraint: text,
                    derived_from: Vec::new(),
                },
            );
        }
    }

    fn check_collection_index_bounds(
        &mut self,
        index: &Spanned<Expr>,
        collection_ty: &Ty,
        locals: &LocalEnv,
    ) {
        let Some(index_expr) = numeric_expr_from_expr(index) else {
            return;
        };
        let Some(len_expr) = self.collection_length_expr(collection_ty) else {
            return;
        };
        let constraint = ConstraintExpr::And(vec![
            ConstraintExpr::Compare {
                lhs: NumericExpr::Const(0),
                op: CompareOp::Lte,
                rhs: index_expr.clone(),
            },
            ConstraintExpr::Compare {
                lhs: index_expr,
                op: CompareOp::Lt,
                rhs: len_expr,
            },
        ]);
        self.prove_required_constraint(
            index.1,
            constraint,
            format!(
                "0 <= {} < {}",
                span_text(self.source, index.1),
                self.collection_length_text(collection_ty)
                    .unwrap_or_else(|| "?".to_string())
            ),
            locals,
        );
    }

    fn expr_static_int(&self, expr: &Spanned<Expr>) -> Option<i64> {
        let expr = numeric_expr_from_expr(expr)?;
        eval_numeric_expr(&expr, &Subst::default(), &[])
    }

    fn range_length_text(&self, start: &Spanned<Expr>, end: &Spanned<Expr>) -> String {
        if let (Some(start), Some(end)) = (self.expr_static_int(start), self.expr_static_int(end)) {
            let len = match self.env.vector_order {
                VectorOrder::Dec => start - end + 1,
                VectorOrder::Inc => end - start + 1,
            };
            return len.to_string();
        }
        let start = span_text(self.source, start.1);
        let end = span_text(self.source, end.1);
        // Wrap each operand in parentheses so a later parser doesn't misread
        // `'m - i - 1 - 'm - i - 8 + 1` (which loses the original grouping
        // from `('m - i - 1) - ('m - i - 8) + 1`).
        match self.env.vector_order {
            VectorOrder::Dec => format!("(({start}) - ({end}) + 1)"),
            VectorOrder::Inc => format!("(({end}) - ({start}) + 1)"),
        }
    }

    fn check_collection_range_bounds(
        &mut self,
        span: Span,
        start: &Spanned<Expr>,
        end: &Spanned<Expr>,
        collection_ty: &Ty,
        locals: &LocalEnv,
    ) -> Option<Ty> {
        let slice_ty =
            self.collection_slice_type(collection_ty, self.range_length_text(start, end));
        let Some(start_expr) = numeric_expr_from_expr(start) else {
            return slice_ty;
        };
        let Some(end_expr) = numeric_expr_from_expr(end) else {
            return slice_ty;
        };
        let Some(len_expr) = self.collection_length_expr(collection_ty) else {
            return slice_ty;
        };
        let constraint = match self.env.vector_order {
            VectorOrder::Dec => ConstraintExpr::And(vec![
                ConstraintExpr::Compare {
                    lhs: NumericExpr::Const(0),
                    op: CompareOp::Lte,
                    rhs: end_expr.clone(),
                },
                ConstraintExpr::Compare {
                    lhs: end_expr.clone(),
                    op: CompareOp::Lte,
                    rhs: start_expr.clone(),
                },
                ConstraintExpr::Compare {
                    lhs: start_expr,
                    op: CompareOp::Lt,
                    rhs: len_expr,
                },
            ]),
            VectorOrder::Inc => ConstraintExpr::And(vec![
                ConstraintExpr::Compare {
                    lhs: NumericExpr::Const(0),
                    op: CompareOp::Lte,
                    rhs: start_expr.clone(),
                },
                ConstraintExpr::Compare {
                    lhs: start_expr.clone(),
                    op: CompareOp::Lte,
                    rhs: end_expr.clone(),
                },
                ConstraintExpr::Compare {
                    lhs: end_expr,
                    op: CompareOp::Lt,
                    rhs: len_expr,
                },
            ]),
        };
        self.prove_required_constraint(
            span,
            constraint,
            match self.env.vector_order {
                VectorOrder::Dec => format!(
                    "0 <= {} <= {} < {}",
                    span_text(self.source, end.1),
                    span_text(self.source, start.1),
                    self.collection_length_text(collection_ty)
                        .unwrap_or_else(|| "?".to_string())
                ),
                VectorOrder::Inc => format!(
                    "0 <= {} <= {} < {}",
                    span_text(self.source, start.1),
                    span_text(self.source, end.1),
                    self.collection_length_text(collection_ty)
                        .unwrap_or_else(|| "?".to_string())
                ),
            },
            locals,
        );
        slice_ty
    }

    fn check_collection_window_bounds(
        &mut self,
        span: Span,
        start: &Spanned<Expr>,
        length: &Spanned<Expr>,
        collection_ty: &Ty,
        locals: &LocalEnv,
    ) -> Option<Ty> {
        let slice_ty = self.collection_slice_type(
            collection_ty,
            self.expr_static_int(length)
                .map(|value| value.to_string())
                .unwrap_or_else(|| span_text(self.source, length.1).to_string()),
        );
        let Some(start_expr) = numeric_expr_from_expr(start) else {
            return slice_ty;
        };
        let Some(length_expr) = numeric_expr_from_expr(length) else {
            return slice_ty;
        };
        let Some(len_expr) = self.collection_length_expr(collection_ty) else {
            return slice_ty;
        };
        let constraint = ConstraintExpr::And(vec![
            ConstraintExpr::Compare {
                lhs: NumericExpr::Const(0),
                op: CompareOp::Lte,
                rhs: start_expr.clone(),
            },
            ConstraintExpr::Compare {
                lhs: NumericExpr::Const(0),
                op: CompareOp::Lte,
                rhs: length_expr.clone(),
            },
            ConstraintExpr::Compare {
                lhs: NumericExpr::Add(Box::new(start_expr), Box::new(length_expr)),
                op: CompareOp::Lte,
                rhs: len_expr,
            },
        ]);
        self.prove_required_constraint(
            span,
            constraint,
            format!(
                "0 <= {} && 0 <= {} && {} + {} <= {}",
                span_text(self.source, start.1),
                span_text(self.source, length.1),
                span_text(self.source, start.1),
                span_text(self.source, length.1),
                self.collection_length_text(collection_ty)
                    .unwrap_or_else(|| "?".to_string())
            ),
            locals,
        );
        slice_ty
    }

    fn infer_slice_builtin_call(
        &mut self,
        call: &sail_parser::Call,
        arg_types: &[Ty],
        locals: &LocalEnv,
        expected_ret: Option<&Ty>,
    ) -> Ty {
        if call.args.len() != 3 {
            self.push_error(
                DiagnosticCode::MismatchedArgCount,
                call.callee.1,
                TypeError::other(format!("Expected 3 arguments, found {}", call.args.len())),
            );
            return Ty::unknown();
        }

        let start_ty = &arg_types[1];
        self.expect_int_type(call.args[1].1, start_ty);
        let length_ty = &arg_types[2];
        self.expect_int_type(call.args[2].1, length_ty);

        let call_span = Span::new(call.args[0].1.start, call.close_span.end);
        let slice_ty = self
            .check_collection_window_bounds(
                call_span,
                &call.args[1],
                &call.args[2],
                &arg_types[0],
                locals,
            )
            .unwrap_or_else(|| arg_types[0].clone());
        if let Some(expected_ret) = expected_ret {
            self.expect_type(call_span, &slice_ty, expected_ret);
        }
        slice_ty
    }

    fn infer_vector_access_builtin_call(
        &mut self,
        call: &sail_parser::Call,
        locals: &mut LocalEnv,
        expected_ret: Option<&Ty>,
    ) -> Ty {
        if call.args.len() != 2 {
            self.push_error(
                DiagnosticCode::MismatchedArgCount,
                call.callee.1,
                TypeError::other(format!("Expected 2 arguments, found {}", call.args.len())),
            );
            return Ty::unknown();
        }

        let base_ty = self.infer_expr(&call.args[0], locals);
        // Resolve type aliases (e.g. xlenbits → bits(64)) so downstream
        // checks can recognize the underlying form.
        let base_ty = self.env.resolve_alias(&base_ty);
        let call_span = Span::new(call.args[0].1.start, call.close_span.end);
        if let Some((bitfield_name, _)) = self.bitfield_info_for_type(&base_ty) {
            match &call.args[1].0 {
                Expr::Ident(field_name) => {
                    let field_ty =
                        if let Some(field_ty) = self.bitfield_field_type(&base_ty, field_name) {
                            field_ty
                        } else {
                            self.push_error(
                                DiagnosticCode::TypeError,
                                call.args[1].1,
                                TypeError::other(format!(
                                    "Unknown field {} in bitfield {}",
                                    field_name, bitfield_name
                                )),
                            );
                            Ty::unknown()
                        };
                    if let Some(expected_ret) = expected_ret {
                        self.expect_type(call_span, &field_ty, expected_ret);
                    }
                    return field_ty;
                }
                _ => {
                    self.infer_expr(&call.args[1], locals);
                    self.push_error(
                        DiagnosticCode::TypeError,
                        call.args[1].1,
                        TypeError::other(
                            "Vector access could not be interpreted as a bitfield access"
                                .to_string(),
                        ),
                    );
                    return Ty::unknown();
                }
            }
        }

        // If the base type isn't a recognized collection (bits/vector/list/etc.)
        // it may be a cross-file bitfield we don't have info for. Return
        // Unknown without trying to type-check the "index" — which might
        // actually be a field name that looks like an enum member elsewhere.
        let base_text = base_ty.display_text();
        let is_recognized_collection = base_text.starts_with("bits(")
            || base_text.starts_with("vector(")
            || base_text.starts_with("list(")
            || base_text == "bit";
        if !is_recognized_collection && !base_ty.is_unknown() {
            self.infer_expr(&call.args[1], locals);
            return Ty::unknown();
        }

        let index_ty = self.infer_expr(&call.args[1], locals);
        self.expect_int_type(call.args[1].1, &index_ty);
        self.check_collection_index_bounds(&call.args[1], &base_ty, locals);
        let result_ty = self
            .collection_element_type(&base_ty)
            .unwrap_or(Ty::unknown());
        if let Some(expected_ret) = expected_ret {
            self.expect_type(call_span, &result_ty, expected_ret);
        }
        result_ty
    }

    fn infer_vector_subrange_builtin_call(
        &mut self,
        call: &sail_parser::Call,
        locals: &mut LocalEnv,
        expected_ret: Option<&Ty>,
    ) -> Ty {
        if call.args.len() != 3 {
            self.push_error(
                DiagnosticCode::MismatchedArgCount,
                call.callee.1,
                TypeError::other(format!("Expected 3 arguments, found {}", call.args.len())),
            );
            return Ty::unknown();
        }

        let base_ty = self.infer_expr(&call.args[0], locals);
        // Resolve type aliases (e.g. flenbits → bits(flen)) so the slice
        // width can be computed correctly.
        let base_ty = self.env.resolve_alias(&base_ty);
        let start_ty = self.infer_expr(&call.args[1], locals);
        self.expect_int_type(call.args[1].1, &start_ty);
        let end_ty = self.infer_expr(&call.args[2], locals);
        self.expect_int_type(call.args[2].1, &end_ty);

        let call_span = Span::new(call.args[0].1.start, call.close_span.end);
        let result_ty = self
            .check_collection_range_bounds(
                call_span,
                &call.args[1],
                &call.args[2],
                &base_ty,
                locals,
            )
            .unwrap_or(base_ty);
        if let Some(expected_ret) = expected_ret {
            self.expect_type(call_span, &result_ty, expected_ret);
        }
        result_ty
    }

    fn infer_vector_update_builtin_call(
        &mut self,
        call: &sail_parser::Call,
        locals: &mut LocalEnv,
        expected_ret: Option<&Ty>,
    ) -> Ty {
        if call.args.len() != 3 {
            self.push_error(
                DiagnosticCode::MismatchedArgCount,
                call.callee.1,
                TypeError::other(format!("Expected 3 arguments, found {}", call.args.len())),
            );
            return Ty::unknown();
        }

        let update = (
            VectorUpdate::Assignment {
                target: call.args[1].clone(),
                value: call.args[2].clone(),
            },
            Span::new(call.args[1].1.start, call.close_span.end),
        );

        if let Some(expected_ret) = expected_ret {
            self.check_vector_update_expr_against(
                &call.args[0],
                std::slice::from_ref(&update),
                expected_ret,
                locals,
            )
        } else {
            self.infer_vector_update_expr(&call.args[0], std::slice::from_ref(&update), locals)
        }
    }

    fn infer_vector_update_subrange_builtin_call(
        &mut self,
        call: &sail_parser::Call,
        locals: &mut LocalEnv,
        expected_ret: Option<&Ty>,
    ) -> Ty {
        if call.args.len() != 4 {
            self.push_error(
                DiagnosticCode::MismatchedArgCount,
                call.callee.1,
                TypeError::other(format!("Expected 4 arguments, found {}", call.args.len())),
            );
            return Ty::unknown();
        }

        let update = (
            VectorUpdate::RangeAssignment {
                start: call.args[1].clone(),
                end: call.args[2].clone(),
                value: call.args[3].clone(),
            },
            Span::new(call.args[1].1.start, call.close_span.end),
        );

        if let Some(expected_ret) = expected_ret {
            self.check_vector_update_expr_against(
                &call.args[0],
                std::slice::from_ref(&update),
                expected_ret,
                locals,
            )
        } else {
            self.infer_vector_update_expr(&call.args[0], std::slice::from_ref(&update), locals)
        }
    }

    fn pattern_subrange(&mut self, span: Span, first: i64, second: i64) -> (i64, i64) {
        match self.env.vector_order {
            VectorOrder::Dec => {
                if first < second {
                    self.push_error(
                        DiagnosticCode::TypeError,
                        span,
                        TypeError::VectorSubrange {
                            first: first.to_string(),
                            second: second.to_string(),
                            order: VectorOrder::Dec,
                        },
                    );
                }
            }
            VectorOrder::Inc => {
                if first > second {
                    self.push_error(
                        DiagnosticCode::TypeError,
                        span,
                        TypeError::VectorSubrange {
                            first: first.to_string(),
                            second: second.to_string(),
                            order: VectorOrder::Inc,
                        },
                    );
                }
            }
        }
        (first.max(second), first.min(second))
    }

    fn pattern_index_range(
        &mut self,
        span: Span,
        start: &Spanned<TypeExpr>,
        end: &Spanned<TypeExpr>,
    ) -> Option<(i64, i64)> {
        let first = type_expr_static_int(self.source, start)?;
        let second = type_expr_static_int(self.source, end)?;
        Some(self.pattern_subrange(span, first, second))
    }

    fn note_pattern_binding(
        &mut self,
        name: &str,
        span: Span,
        bindings: &mut HashMap<String, Span>,
    ) {
        if let Some(previous) = bindings.insert(name.to_string(), span) {
            self.push_error(
                DiagnosticCode::TypeError,
                span,
                TypeError::Alternate {
                    primary: Box::new(TypeError::other(format!(
                        "Duplicate binding for {name} in pattern"
                    ))),
                    reasons: vec![(
                        "because".to_string(),
                        previous,
                        Box::new(TypeError::Hint(format!("Previous binding of {name} here"))),
                    )],
                },
            );
        }
    }

    fn collect_pattern_prebindings(
        &mut self,
        pattern: &Spanned<Pattern>,
        bindings: &mut HashMap<String, Span>,
        subranges: &mut HashMap<String, Vec<(Span, i64, i64)>>,
    ) {
        match &pattern.0 {
            Pattern::Attribute { pattern, .. } => {
                self.collect_pattern_prebindings(pattern, bindings, subranges);
            }
            Pattern::Ident(name) => {
                if is_pattern_binding(name, &self.pattern_constants, self.env.has_workspace_context) {
                    self.note_pattern_binding(name, pattern.1, bindings);
                }
            }
            Pattern::Typed(inner, _) | Pattern::AsType(inner, _) => {
                self.collect_pattern_prebindings(inner, bindings, subranges);
            }
            Pattern::Tuple(items) | Pattern::List(items) | Pattern::Vector(items) => {
                for item in items {
                    self.collect_pattern_prebindings(item, bindings, subranges);
                }
            }
            Pattern::App { args, .. } => {
                for arg in args {
                    self.collect_pattern_prebindings(arg, bindings, subranges);
                }
            }
            Pattern::Index { name, index } => {
                if !is_pattern_binding(&name.0, &self.pattern_constants, self.env.has_workspace_context) {
                    self.push_error(
                        DiagnosticCode::TypeError,
                        name.1,
                        TypeError::other(format!(
                            "Identifier {} is not valid in vector subrange pattern",
                            name.0
                        )),
                    );
                    return;
                }
                if let Some(index) = type_expr_static_int(self.source, index) {
                    let (hi, lo) = self.pattern_subrange(pattern.1, index, index);
                    subranges
                        .entry(name.0.clone())
                        .or_default()
                        .push((name.1, hi, lo));
                }
            }
            Pattern::RangeIndex { name, start, end } => {
                if !is_pattern_binding(&name.0, &self.pattern_constants, self.env.has_workspace_context) {
                    self.push_error(
                        DiagnosticCode::TypeError,
                        name.1,
                        TypeError::other(format!(
                            "Identifier {} is not valid in vector subrange pattern",
                            name.0
                        )),
                    );
                    return;
                }
                if let Some((hi, lo)) = self.pattern_index_range(pattern.1, start, end) {
                    subranges
                        .entry(name.0.clone())
                        .or_default()
                        .push((name.1, hi, lo));
                }
            }
            Pattern::Struct { fields, .. } => {
                for field in fields {
                    match &field.0 {
                        FieldPattern::Binding { pattern, .. } => {
                            self.collect_pattern_prebindings(pattern, bindings, subranges);
                        }
                        FieldPattern::Shorthand(name) => {
                            self.note_pattern_binding(&name.0, name.1, bindings);
                        }
                        FieldPattern::Wild(_) => {}
                    }
                }
            }
            Pattern::Infix { lhs, rhs, .. } => {
                self.collect_pattern_prebindings(lhs, bindings, subranges);
                self.collect_pattern_prebindings(rhs, bindings, subranges);
            }
            Pattern::AsBinding {
                pattern: inner,
                binding,
            } => {
                self.collect_pattern_prebindings(inner, bindings, subranges);
                self.note_pattern_binding(&binding.0, binding.1, bindings);
            }
            Pattern::Wild | Pattern::Literal(_) | Pattern::TypeVar(_) | Pattern::Error(_) => {}
        }
    }

    fn precheck_pattern(&mut self, pattern: &Spanned<Pattern>, locals: &mut LocalEnv) {
        let mut bindings = HashMap::new();
        let mut subranges = HashMap::<String, Vec<(Span, i64, i64)>>::new();
        self.collect_pattern_prebindings(pattern, &mut bindings, &mut subranges);

        for (name, entries) in &subranges {
            if let Some(previous) = bindings.get(name) {
                let span = entries
                    .first()
                    .map(|(span, _, _)| *span)
                    .unwrap_or(*previous);
                self.push_error(
                    DiagnosticCode::TypeError,
                    span,
                    TypeError::Alternate {
                        primary: Box::new(TypeError::other(format!(
                            "Vector subrange binding {name} is also bound as a regular identifier"
                        ))),
                        reasons: vec![(
                            "because".to_string(),
                            *previous,
                            Box::new(TypeError::Hint("Regular binding is here".to_string())),
                        )],
                    },
                );
            }
        }

        for (name, entries) in subranges {
            let mut merged = Vec::new();
            let mut spans = Vec::new();
            for (span, hi, lo) in entries {
                spans.push(span);
                insert_subrange(&mut merged, hi, lo);
            }
            match merged.as_slice() {
                [(hi, lo)] if *lo == 0 => {
                    let ty = bits_ty(hi + 1);
                    locals.define(&name, ty.clone());
                    for span in spans {
                        self.record_binding_type(span, &ty);
                    }
                }
                [(_, lo)] => {
                    let span = spans.first().copied().unwrap_or(pattern.1);
                    self.push_error(
                        DiagnosticCode::TypeError,
                        span,
                        TypeError::other(format!(
                            "Cannot bind {name} as pattern subranges do not start at bit 0 (lowest bit is {lo})."
                        )),
                    );
                }
                [_, (hi, _), ..] => {
                    let span = spans.first().copied().unwrap_or(pattern.1);
                    self.push_error(
                        DiagnosticCode::TypeError,
                        span,
                        TypeError::other(format!(
                            "Cannot bind {name} as pattern subranges are non-contiguous. {name}[{}] is not defined.",
                            hi + 1
                        )),
                    );
                }
                [] => {}
            }
        }
    }

    fn collect_pattern_binding_name_spans(
        &self,
        pattern: &Spanned<Pattern>,
        out: &mut HashMap<String, Span>,
    ) {
        match &pattern.0 {
            Pattern::Attribute { pattern, .. } => {
                self.collect_pattern_binding_name_spans(pattern, out);
            }
            Pattern::Ident(name) => {
                if is_pattern_binding(name, &self.pattern_constants, self.env.has_workspace_context) {
                    out.entry(name.clone()).or_insert(pattern.1);
                }
            }
            Pattern::Typed(inner, _) | Pattern::AsType(inner, _) => {
                self.collect_pattern_binding_name_spans(inner, out);
            }
            Pattern::Tuple(items) | Pattern::List(items) | Pattern::Vector(items) => {
                for item in items {
                    self.collect_pattern_binding_name_spans(item, out);
                }
            }
            Pattern::App { args, .. } => {
                for arg in args {
                    self.collect_pattern_binding_name_spans(arg, out);
                }
            }
            Pattern::Index { name, .. } | Pattern::RangeIndex { name, .. } => {
                if is_pattern_binding(&name.0, &self.pattern_constants, self.env.has_workspace_context) {
                    out.entry(name.0.clone()).or_insert(name.1);
                }
            }
            Pattern::Struct { fields, .. } => {
                for field in fields {
                    match &field.0 {
                        FieldPattern::Binding { pattern, .. } => {
                            self.collect_pattern_binding_name_spans(pattern, out);
                        }
                        FieldPattern::Shorthand(name) => {
                            out.entry(name.0.clone()).or_insert(name.1);
                        }
                        FieldPattern::Wild(_) => {}
                    }
                }
            }
            Pattern::Infix { lhs, rhs, .. } => {
                self.collect_pattern_binding_name_spans(lhs, out);
                self.collect_pattern_binding_name_spans(rhs, out);
            }
            Pattern::AsBinding {
                pattern: inner,
                binding,
            } => {
                self.collect_pattern_binding_name_spans(inner, out);
                out.entry(binding.0.clone()).or_insert(binding.1);
            }
            Pattern::Wild | Pattern::Literal(_) | Pattern::TypeVar(_) | Pattern::Error(_) => {}
        }
    }

    fn capture_pattern_bindings(
        &mut self,
        pattern: &Spanned<Pattern>,
        expected_ty: Ty,
        locals: &mut LocalEnv,
    ) -> HashMap<String, (Span, Ty)> {
        let mark = locals.snapshot();
        locals.push_scope();
        self.bind_pattern(pattern, Some(expected_ty), locals);
        let mut names = HashMap::new();
        self.collect_pattern_binding_name_spans(pattern, &mut names);
        let bindings = names
            .into_iter()
            .filter_map(|(name, span)| locals.lookup(&name).cloned().map(|ty| (name, (span, ty))))
            .collect();
        locals.restore(mark);
        bindings
    }

    fn define_captured_bindings(
        &mut self,
        locals: &mut LocalEnv,
        bindings: &HashMap<String, (Span, Ty)>,
    ) {
        for (name, (span, ty)) in bindings {
            locals.define(name, ty.clone());
            self.record_binding_type(*span, ty);
        }
    }

    fn merge_mapping_bindings(
        &mut self,
        span: Span,
        left: &HashMap<String, (Span, Ty)>,
        right: &HashMap<String, (Span, Ty)>,
    ) -> HashMap<String, (Span, Ty)> {
        if left.is_empty() {
            return right.clone();
        }
        if right.is_empty() {
            return left.clone();
        }

        let mut merged = HashMap::new();
        for (name, (left_span, left_ty)) in left {
            match right.get(name) {
                Some((right_span, right_ty)) => {
                    let compatible = {
                        let mut subst = Subst::default();
                        unify(left_ty, right_ty, &mut subst)
                            || unify(right_ty, left_ty, &mut Subst::default())
                    };
                    if !compatible {
                        self.push_error(
                            DiagnosticCode::TypeError,
                            span,
                            TypeError::Alternate {
                                primary: Box::new(TypeError::other(format!(
                                    "'{name}' must have the same type on both sides of the mapping"
                                ))),
                                reasons: vec![
                                    (
                                        "because".to_string(),
                                        *left_span,
                                        Box::new(TypeError::Hint(format!(
                                            "has type {}",
                                            left_ty.display_text()
                                        ))),
                                    ),
                                    (
                                        "and".to_string(),
                                        *right_span,
                                        Box::new(TypeError::Hint(format!(
                                            "has type {}",
                                            right_ty.display_text()
                                        ))),
                                    ),
                                ],
                            },
                        );
                    }
                    merged.insert(name.clone(), (*left_span, left_ty.clone()));
                }
                None => {
                    self.push_error(
                        DiagnosticCode::TypeError,
                        *left_span,
                        TypeError::other(format!(
                            "Identifier {name} found on left hand side of mapping, but not on right"
                        )),
                    );
                }
            }
        }

        for (name, (right_span, _)) in right {
            if !left.contains_key(name) {
                self.push_error(
                    DiagnosticCode::TypeError,
                    *right_span,
                    TypeError::other(format!(
                        "Identifier {name} found on right hand side of mapping, but not on left"
                    )),
                );
            }
        }

        merged
    }

    fn infer_struct_expr(
        &mut self,
        span: Span,
        name: Option<&Spanned<String>>,
        fields: &[Spanned<FieldExpr>],
        locals: &mut LocalEnv,
    ) -> Ty {
        let Some(name) = name else {
            for field in fields {
                match &field.0 {
                    FieldExpr::Assignment { value, .. } => {
                        self.infer_expr(value, locals);
                    }
                    FieldExpr::Shorthand(name) => {
                        self.infer_shorthand_binding(name, locals);
                    }
                }
            }
            return Ty::unknown();
        };

        let Some(record_info) = self.env.records.get(&name.0).cloned() else {
            self.push_error(
                DiagnosticCode::TypeError,
                name.1,
                TypeError::other(format!("Unknown record type {}", name.0)),
            );
            return Ty::unknown();
        };

        let record_ty = Ty::text(name.0.clone());
        let mut remaining_fields = record_info.fields.keys().cloned().collect::<HashSet<_>>();

        for field in fields {
            match &field.0 {
                FieldExpr::Assignment { target, value } => {
                    let Some(field_name) = self.field_name_from_expr(target) else {
                        self.infer_expr(value, locals);
                        self.push_error(
                            DiagnosticCode::TypeError,
                            target.1,
                            TypeError::other("Struct field assignment must target a field name"),
                        );
                        continue;
                    };
                    remaining_fields.remove(&field_name);
                    let value_ty = self.infer_expr(value, locals);
                    if let Some(expected) = self.record_field_type(&record_ty, &field_name) {
                        self.expect_type(value.1, &value_ty, &expected);
                    } else {
                        self.push_error(
                            DiagnosticCode::TypeError,
                            target.1,
                            TypeError::other(format!(
                                "Record {} has no field {}",
                                name.0, field_name
                            )),
                        );
                    }
                }
                FieldExpr::Shorthand(binding) => {
                    remaining_fields.remove(&binding.0);
                    let Some(value_ty) = self.infer_shorthand_binding(binding, locals) else {
                        continue;
                    };
                    if let Some(expected) = self.record_field_type(&record_ty, &binding.0) {
                        self.expect_type(binding.1, &value_ty, &expected);
                    } else {
                        self.push_error(
                            DiagnosticCode::TypeError,
                            binding.1,
                            TypeError::other(format!(
                                "Record {} has no field {}",
                                name.0, binding.0
                            )),
                        );
                    }
                }
            }
        }

        if !remaining_fields.is_empty() {
            let mut missing = remaining_fields.into_iter().collect::<Vec<_>>();
            missing.sort();
            self.push_error(
                DiagnosticCode::TypeError,
                span,
                TypeError::other(format!(
                    "struct literal missing fields: {}",
                    missing.join(", ")
                )),
            );
        }

        record_ty
    }

    fn infer_update_expr(
        &mut self,
        base: &Spanned<Expr>,
        fields: &[Spanned<FieldExpr>],
        locals: &mut LocalEnv,
    ) -> Ty {
        let base_ty = self.infer_expr(base, locals);
        let record_name = self.record_info_for_type(&base_ty).map(|(name, _, _)| name);
        let bitfield_name = self.bitfield_info_for_type(&base_ty).map(|(name, _)| name);
        if record_name.is_none() && bitfield_name.is_none() {
            if !is_known_non_record(&base_ty) {
                return Ty::unknown();
            }
            self.push_error(
                DiagnosticCode::TypeError,
                base.1,
                TypeError::other(format!("The type {} is not a record", base_ty.display_text())),
            );
            return Ty::unknown();
        }

        for field in fields {
            match &field.0 {
                FieldExpr::Assignment { target, value } => {
                    let Some(field_name) = self.field_name_from_expr(target) else {
                        self.infer_expr(value, locals);
                        self.push_error(
                            DiagnosticCode::TypeError,
                            target.1,
                            TypeError::other(if bitfield_name.is_some() {
                                "Bitfield update must target a field name".to_string()
                            } else {
                                "Record update must target a field name".to_string()
                            }),
                        );
                        continue;
                    };
                    let value_ty = self.infer_expr(value, locals);
                    if let Some(expected) = self
                        .record_field_type(&base_ty, &field_name)
                        .or_else(|| self.bitfield_field_type(&base_ty, &field_name))
                    {
                        self.expect_type(value.1, &value_ty, &expected);
                    } else {
                        let message = if let Some(record_name) = &record_name {
                            format!("Record {} has no field {}", record_name, field_name)
                        } else {
                            format!(
                                "Unknown field {} in bitfield {}",
                                field_name,
                                bitfield_name.as_deref().unwrap_or("?")
                            )
                        };
                        self.push_error(
                            DiagnosticCode::TypeError,
                            target.1,
                            TypeError::other(message),
                        );
                    }
                }
                FieldExpr::Shorthand(binding) => {
                    let Some(value_ty) = self.infer_shorthand_binding(binding, locals) else {
                        continue;
                    };
                    if let Some(expected) = self
                        .record_field_type(&base_ty, &binding.0)
                        .or_else(|| self.bitfield_field_type(&base_ty, &binding.0))
                    {
                        self.expect_type(binding.1, &value_ty, &expected);
                    } else {
                        let message = if let Some(record_name) = &record_name {
                            format!("Record {} has no field {}", record_name, binding.0)
                        } else {
                            format!(
                                "Unknown field {} in bitfield {}",
                                binding.0,
                                bitfield_name.as_deref().unwrap_or("?")
                            )
                        };
                        self.push_error(
                            DiagnosticCode::TypeError,
                            binding.1,
                            TypeError::other(message),
                        );
                    }
                }
            }
        }

        base_ty
    }

    fn infer_vector_update_expr(
        &mut self,
        base: &Spanned<Expr>,
        updates: &[Spanned<VectorUpdate>],
        locals: &mut LocalEnv,
    ) -> Ty {
        let base_ty = self.infer_expr(base, locals);
        if let Some((bitfield_name, _)) = self.bitfield_info_for_type(&base_ty) {
            for update in updates {
                match &update.0 {
                    VectorUpdate::Assignment { target, value } => {
                        let Some(field_name) = self.field_name_from_expr(target) else {
                            self.infer_expr(value, locals);
                            self.push_error(
                                DiagnosticCode::TypeError,
                                target.1,
                                TypeError::other(
                                    "Vector update could not be interpreted as a bitfield update"
                                        .to_string(),
                                ),
                            );
                            continue;
                        };
                        if let Some(expected) = self.bitfield_field_type(&base_ty, &field_name) {
                            self.check_expr(value, &expected, locals);
                        } else {
                            self.infer_expr(value, locals);
                            self.push_error(
                                DiagnosticCode::TypeError,
                                target.1,
                                TypeError::other(format!(
                                    "Unknown field {} in bitfield {}",
                                    field_name, bitfield_name
                                )),
                            );
                        }
                    }
                    VectorUpdate::RangeAssignment { start, end, value } => {
                        self.infer_expr(start, locals);
                        self.infer_expr(end, locals);
                        self.infer_expr(value, locals);
                        self.push_error(
                            DiagnosticCode::TypeError,
                            update.1,
                            TypeError::other(
                                "Vector update could not be interpreted as a bitfield update"
                                    .to_string(),
                            ),
                        );
                    }
                    VectorUpdate::Shorthand(binding) => {
                        let Some(value_ty) = self.infer_shorthand_binding(binding, locals) else {
                            continue;
                        };
                        if let Some(expected) = self.bitfield_field_type(&base_ty, &binding.0) {
                            self.expect_type(binding.1, &value_ty, &expected);
                        } else {
                            self.push_error(
                                DiagnosticCode::TypeError,
                                binding.1,
                                TypeError::other(format!(
                                    "Unknown field {} in bitfield {}",
                                    binding.0, bitfield_name
                                )),
                            );
                        }
                    }
                }
            }
            return base_ty;
        }
        let element_ty = self.collection_element_type(&base_ty);

        for update in updates {
            match &update.0 {
                VectorUpdate::Assignment { target, value } => {
                    let index_ty = self.infer_expr(target, locals);
                    self.expect_int_type(target.1, &index_ty);
                    self.check_collection_index_bounds(target, &base_ty, locals);
                    let value_ty = self.infer_expr(value, locals);
                    if let Some(expected) = &element_ty {
                        self.expect_type(value.1, &value_ty, expected);
                    }
                }
                VectorUpdate::RangeAssignment { start, end, value } => {
                    let start_ty = self.infer_expr(start, locals);
                    self.expect_int_type(start.1, &start_ty);
                    let end_ty = self.infer_expr(end, locals);
                    self.expect_int_type(end.1, &end_ty);
                    if let Some(range_ty) =
                        self.check_collection_range_bounds(update.1, start, end, &base_ty, locals)
                    {
                        self.check_expr(value, &range_ty, locals);
                    } else {
                        self.infer_expr(value, locals);
                    }
                }
                VectorUpdate::Shorthand(binding) => {
                    self.infer_shorthand_binding(binding, locals);
                }
            }
        }

        base_ty
    }

    fn check_struct_expr_against(
        &mut self,
        span: Span,
        name: Option<&Spanned<String>>,
        fields: &[Spanned<FieldExpr>],
        expected: &Ty,
        locals: &mut LocalEnv,
    ) -> Ty {
        let Some((record_name, _, _)) = self.record_info_for_type(expected) else {
            let actual = self.infer_struct_expr(span, name, fields, locals);
            self.expect_type(span, &actual, expected);
            return if expected.is_unknown() {
                actual
            } else {
                expected.clone()
            };
        };

        if let Some(name) = name {
            if name.0 != record_name {
                self.push_error(
                    DiagnosticCode::TypeError,
                    name.1,
                    TypeError::other(format!(
                        "Struct type {} found, {} expected",
                        name.0, record_name
                    )),
                );
            }
        }

        let mut remaining_fields = self
            .env
            .records
            .get(&record_name)
            .map(|info| info.fields.keys().cloned().collect::<HashSet<_>>())
            .unwrap_or_default();

        for field in fields {
            match &field.0 {
                FieldExpr::Assignment { target, value } => {
                    let Some(field_name) = self.field_name_from_expr(target) else {
                        self.infer_expr(value, locals);
                        self.push_error(
                            DiagnosticCode::TypeError,
                            target.1,
                            TypeError::other("Struct field assignment must target a field name"),
                        );
                        continue;
                    };
                    remaining_fields.remove(&field_name);
                    self.check_expr(
                        value,
                        &self
                            .record_field_type(expected, &field_name)
                            .unwrap_or(Ty::unknown()),
                        locals,
                    );
                    if self.record_field_type(expected, &field_name).is_none() {
                        self.push_error(
                            DiagnosticCode::TypeError,
                            target.1,
                            TypeError::other(format!(
                                "Record {} has no field {}",
                                record_name, field_name
                            )),
                        );
                    }
                }
                FieldExpr::Shorthand(binding) => {
                    remaining_fields.remove(&binding.0);
                    let Some(value_ty) = self.infer_shorthand_binding(binding, locals) else {
                        continue;
                    };
                    if let Some(field_ty) = self.record_field_type(expected, &binding.0) {
                        self.expect_type(binding.1, &value_ty, &field_ty);
                    } else {
                        self.push_error(
                            DiagnosticCode::TypeError,
                            binding.1,
                            TypeError::other(format!(
                                "Record {} has no field {}",
                                record_name, binding.0
                            )),
                        );
                    }
                }
            }
        }

        if !remaining_fields.is_empty() {
            let mut missing = remaining_fields.into_iter().collect::<Vec<_>>();
            missing.sort();
            self.push_error(
                DiagnosticCode::TypeError,
                span,
                TypeError::other(format!(
                    "struct literal missing fields: {}",
                    missing.join(", ")
                )),
            );
        }

        expected.clone()
    }

    fn check_update_expr_against(
        &mut self,
        base: &Spanned<Expr>,
        fields: &[Spanned<FieldExpr>],
        expected: &Ty,
        locals: &mut LocalEnv,
    ) -> Ty {
        let base_ty = if self.record_info_for_type(expected).is_some()
            || self.bitfield_info_for_type(expected).is_some()
        {
            self.check_expr(base, expected, locals)
        } else {
            self.infer_expr(base, locals)
        };
        let record_ty = if self.record_info_for_type(expected).is_some()
            || self.bitfield_info_for_type(expected).is_some()
        {
            expected.clone()
        } else {
            base_ty.clone()
        };
        let record_name = self
            .record_info_for_type(&record_ty)
            .map(|(name, _, _)| name);
        let bitfield_name = self
            .bitfield_info_for_type(&record_ty)
            .map(|(name, _)| name);
        if record_name.is_none() && bitfield_name.is_none() {
            // Skip the error for cross-file type aliases / unknown types.
            if !is_known_non_record(&record_ty) {
                return Ty::unknown();
            }
            self.push_error(
                DiagnosticCode::TypeError,
                base.1,
                TypeError::other(format!("The type {} is not a record", record_ty.display_text())),
            );
            return Ty::unknown();
        }

        for field in fields {
            match &field.0 {
                FieldExpr::Assignment { target, value } => {
                    let Some(field_name) = self.field_name_from_expr(target) else {
                        self.infer_expr(value, locals);
                        self.push_error(
                            DiagnosticCode::TypeError,
                            target.1,
                            TypeError::other(if bitfield_name.is_some() {
                                "Bitfield update must target a field name".to_string()
                            } else {
                                "Record update must target a field name".to_string()
                            }),
                        );
                        continue;
                    };
                    if let Some(field_ty) = self
                        .record_field_type(&record_ty, &field_name)
                        .or_else(|| self.bitfield_field_type(&record_ty, &field_name))
                    {
                        self.check_expr(value, &field_ty, locals);
                    } else {
                        self.infer_expr(value, locals);
                        let message = if let Some(record_name) = &record_name {
                            format!("Record {} has no field {}", record_name, field_name)
                        } else {
                            format!(
                                "Unknown field {} in bitfield {}",
                                field_name,
                                bitfield_name.as_deref().unwrap_or("?")
                            )
                        };
                        self.push_error(
                            DiagnosticCode::TypeError,
                            target.1,
                            TypeError::other(message),
                        );
                    }
                }
                FieldExpr::Shorthand(binding) => {
                    let Some(value_ty) = self.infer_shorthand_binding(binding, locals) else {
                        continue;
                    };
                    if let Some(field_ty) = self
                        .record_field_type(&record_ty, &binding.0)
                        .or_else(|| self.bitfield_field_type(&record_ty, &binding.0))
                    {
                        self.expect_type(binding.1, &value_ty, &field_ty);
                    } else {
                        let message = if let Some(record_name) = &record_name {
                            format!("Record {} has no field {}", record_name, binding.0)
                        } else {
                            format!(
                                "Unknown field {} in bitfield {}",
                                binding.0,
                                bitfield_name.as_deref().unwrap_or("?")
                            )
                        };
                        self.push_error(
                            DiagnosticCode::TypeError,
                            binding.1,
                            TypeError::other(message),
                        );
                    }
                }
            }
        }

        record_ty
    }

    fn check_vector_update_expr_against(
        &mut self,
        base: &Spanned<Expr>,
        updates: &[Spanned<VectorUpdate>],
        expected: &Ty,
        locals: &mut LocalEnv,
    ) -> Ty {
        let collection_ty = if self.collection_element_type(expected).is_some() {
            self.check_expr(base, expected, locals);
            expected.clone()
        } else {
            self.infer_expr(base, locals)
        };
        if let Some((bitfield_name, _)) = self.bitfield_info_for_type(&collection_ty) {
            for update in updates {
                match &update.0 {
                    VectorUpdate::Assignment { target, value } => {
                        let Some(field_name) = self.field_name_from_expr(target) else {
                            self.infer_expr(value, locals);
                            self.push_error(
                                DiagnosticCode::TypeError,
                                target.1,
                                TypeError::other(
                                    "Vector update could not be interpreted as a bitfield update"
                                        .to_string(),
                                ),
                            );
                            continue;
                        };
                        if let Some(field_ty) =
                            self.bitfield_field_type(&collection_ty, &field_name)
                        {
                            self.check_expr(value, &field_ty, locals);
                        } else {
                            self.infer_expr(value, locals);
                            self.push_error(
                                DiagnosticCode::TypeError,
                                target.1,
                                TypeError::other(format!(
                                    "Unknown field {} in bitfield {}",
                                    field_name, bitfield_name
                                )),
                            );
                        }
                    }
                    VectorUpdate::RangeAssignment { start, end, value } => {
                        self.infer_expr(start, locals);
                        self.infer_expr(end, locals);
                        self.infer_expr(value, locals);
                        self.push_error(
                            DiagnosticCode::TypeError,
                            update.1,
                            TypeError::other(
                                "Vector update could not be interpreted as a bitfield update"
                                    .to_string(),
                            ),
                        );
                    }
                    VectorUpdate::Shorthand(binding) => {
                        let Some(value_ty) = self.infer_shorthand_binding(binding, locals) else {
                            continue;
                        };
                        if let Some(field_ty) = self.bitfield_field_type(&collection_ty, &binding.0)
                        {
                            self.expect_type(binding.1, &value_ty, &field_ty);
                        } else {
                            self.push_error(
                                DiagnosticCode::TypeError,
                                binding.1,
                                TypeError::other(format!(
                                    "Unknown field {} in bitfield {}",
                                    binding.0, bitfield_name
                                )),
                            );
                        }
                    }
                }
            }
            return collection_ty;
        }
        let element_ty = self.collection_element_type(&collection_ty);

        for update in updates {
            match &update.0 {
                VectorUpdate::Assignment { target, value } => {
                    let index_ty = self.infer_expr(target, locals);
                    self.expect_int_type(target.1, &index_ty);
                    self.check_collection_index_bounds(target, &collection_ty, locals);
                    if let Some(element_ty) = &element_ty {
                        self.check_expr(value, element_ty, locals);
                    } else {
                        self.infer_expr(value, locals);
                    }
                }
                VectorUpdate::RangeAssignment { start, end, value } => {
                    let start_ty = self.infer_expr(start, locals);
                    self.expect_int_type(start.1, &start_ty);
                    let end_ty = self.infer_expr(end, locals);
                    self.expect_int_type(end.1, &end_ty);
                    if let Some(range_ty) = self.check_collection_range_bounds(
                        update.1,
                        start,
                        end,
                        &collection_ty,
                        locals,
                    ) {
                        self.check_expr(value, &range_ty, locals);
                    } else {
                        self.infer_expr(value, locals);
                    }
                }
                VectorUpdate::Shorthand(binding) => {
                    self.infer_shorthand_binding(binding, locals);
                }
            }
        }

        collection_ty
    }

    fn check_collection_expr(
        &mut self,
        span: Span,
        items: &[Spanned<Expr>],
        expected: &Ty,
        locals: &mut LocalEnv,
        name: &str,
    ) -> Ty {
        match expected.kind() {
            TyData::App {
                name: expected_name,
                ..
            } if expected_name == name => {
                if name == "vector" {
                    if let Some(expected_len) = self
                        .collection_length_text(expected)
                        .and_then(|text| parse_int_literal(&text))
                    {
                        let actual_len = items.len() as i64;
                        if expected_len != actual_len {
                            self.push_error(
                                DiagnosticCode::TypeError,
                                span,
                                TypeError::Subtype {
                                    lhs: vector_ty(actual_len, Ty::unknown()).display_text(),
                                    rhs: expected.display_text(),
                                    constraint: None,
                                },
                            );
                        }
                    }
                }
                if let Some(elem_ty) = self.collection_element_type(expected) {
                    for item in items {
                        self.check_expr(item, &elem_ty, locals);
                    }
                    expected.clone()
                } else {
                    let actual = infer_collection_type(self, items, locals, name);
                    self.expect_type(span, &actual, expected);
                    if expected.is_unknown() {
                        actual
                    } else {
                        expected.clone()
                    }
                }
            }
            _ => {
                let actual = infer_collection_type(self, items, locals, name);
                self.expect_type(span, &actual, expected);
                if expected.is_unknown() {
                    actual
                } else {
                    expected.clone()
                }
            }
        }
    }

    fn check_tuple_expr(
        &mut self,
        span: Span,
        items: &[Spanned<Expr>],
        expected: &Ty,
        locals: &mut LocalEnv,
    ) -> Ty {
        match expected.kind() {
            TyData::Tuple(expected_items) if expected_items.len() == items.len() => {
                for (item, expected_item) in items.iter().zip(expected_items.iter()) {
                    self.check_expr(item, expected_item, locals);
                }
                expected.clone()
            }
            _ => {
                let actual = self.infer_expr(&(Expr::Tuple(items.to_vec()), span), locals);
                self.expect_type(span, &actual, expected);
                if expected.is_unknown() {
                    actual
                } else {
                    expected.clone()
                }
            }
        }
    }

    fn check_expr(&mut self, expr: &Spanned<Expr>, expected: &Ty, locals: &mut LocalEnv) -> Ty {
        if expected.is_unknown() {
            return self.infer_expr(expr, locals);
        }

        let mut current = expr;
        let mut chain_mark = None;
        let mut wrapper_spans = Vec::new();
        loop {
            match &current.0 {
                Expr::Attribute { expr: inner, .. } => {
                    wrapper_spans.push(current.1);
                    current = inner;
                }
                Expr::Let { binding, body } => {
                    wrapper_spans.push(current.1);
                    let value_ty = if let Some(expected_bind) =
                        pattern_annotation_type(self.source, &binding.pattern)
                    {
                        self.check_expr(&binding.value, &expected_bind, locals);
                        expected_bind
                    } else {
                        self.infer_expr(&binding.value, locals)
                    };
                    if chain_mark.is_none() {
                        chain_mark = Some(locals.snapshot());
                    }
                    locals.push_scope();
                    self.bind_pattern(&binding.pattern, Some(value_ty), locals);
                    current = body;
                }
                _ => break,
            }
        }

        let ty = self.check_expr_dispatch(current, expected, locals);
        if let Some(mark) = chain_mark {
            locals.restore(mark);
        }
        for span in wrapper_spans {
            self.record_expr_type(span, &ty);
        }
        ty
    }

    fn check_expr_dispatch(
        &mut self,
        expr: &Spanned<Expr>,
        expected: &Ty,
        locals: &mut LocalEnv,
    ) -> Ty {
        if expected.is_unknown() {
            return self.infer_expr(expr, locals);
        }

        let ty = match &expr.0 {
            Expr::Attribute { expr, .. } => self.check_expr(expr, expected, locals),
            Expr::Return(inner) => {
                let ret_ty = locals
                    .expected_return
                    .clone()
                    .unwrap_or_else(|| expected.clone());
                self.check_expr(inner, &ret_ty, locals);
                ret_ty
            }
            Expr::Let { binding, body } => {
                let value_ty = if let Some(expected_bind) =
                    pattern_annotation_type(self.source, &binding.pattern)
                {
                    self.check_expr(&binding.value, &expected_bind, locals);
                    expected_bind
                } else {
                    self.infer_expr(&binding.value, locals)
                };
                locals.push_scope();
                self.bind_pattern(&binding.pattern, Some(value_ty), locals);
                let body_ty = self.check_expr(body, expected, locals);
                locals.pop_scope();
                body_ty
            }
            Expr::Var {
                target,
                value,
                body,
            } => {
                let value_ty = self.infer_var_target_value(target, value, locals);
                locals.push_scope();
                self.bind_var_target_declaration(target, &value_ty, locals);
                let body_ty = self.check_expr(body, expected, locals);
                locals.pop_scope();
                body_ty
            }
            Expr::Block(items) => {
                locals.push_scope();
                let mut last_ty = Ty::text("unit".to_string());
                for (index, item) in items.iter().enumerate() {
                    match &item.0 {
                        sail_parser::BlockItem::Let(binding) => {
                            self.trace_typecheck("block-let", "_", Some(binding.value.1));
                        }
                        sail_parser::BlockItem::Var { value, .. } => {
                            self.trace_typecheck("block-var", "_", Some(value.1));
                        }
                        sail_parser::BlockItem::Expr(inner) => {
                            self.trace_typecheck(
                                "block-expr",
                                expr_kind_name(&inner.0),
                                Some(inner.1),
                            );
                        }
                    }
                    let is_last = index + 1 == items.len();
                    last_ty = match &item.0 {
                        sail_parser::BlockItem::Let(binding) => {
                            let value_ty = if let Some(expected_bind) =
                                pattern_annotation_type(self.source, &binding.pattern)
                            {
                                self.check_expr(&binding.value, &expected_bind, locals);
                                expected_bind
                            } else {
                                self.infer_expr(&binding.value, locals)
                            };
                            self.bind_pattern(&binding.pattern, Some(value_ty), locals);
                            Ty::text("unit".to_string())
                        }
                        sail_parser::BlockItem::Var { target, value } => {
                            let value_ty = self.infer_var_target_value(target, value, locals);
                            self.bind_var_target_declaration(target, &value_ty, locals);
                            Ty::text("unit".to_string())
                        }
                        sail_parser::BlockItem::Expr(inner) if is_last => {
                            self.check_expr(inner, expected, locals)
                        }
                        sail_parser::BlockItem::Expr(inner) => {
                            let ty = self.infer_expr(inner, locals);
                            self.propagate_post_expr_constraints(inner, locals);
                            ty
                        }
                    };
                }
                locals.pop_scope();
                if items
                    .last()
                    .map(|item| matches!(item.0, sail_parser::BlockItem::Expr(_)))
                    .unwrap_or(false)
                {
                    last_ty
                } else {
                    let unit_ty = Ty::text("unit".to_string());
                    self.expect_type(expr.1, &unit_ty, expected);
                    unit_ty
                }
            }
            Expr::If {
                cond,
                then_branch,
                else_branch,
            } => {
                let cond_ty = self.infer_expr(cond, locals);
                self.expect_type(cond.1, &cond_ty, &Ty::text("bool".to_string()));
                let branch_expected = if else_branch.is_some() {
                    expected.clone()
                } else {
                    Ty::text("unit".to_string())
                };
                let then_mark = locals.snapshot();
                self.add_expr_constraint(locals, cond, true);
                self.check_expr(then_branch, &branch_expected, locals);
                locals.restore(then_mark);
                if let Some(else_branch) = else_branch {
                    let else_mark = locals.snapshot();
                    self.add_expr_constraint(locals, cond, false);
                    self.check_expr(else_branch, &branch_expected, locals);
                    locals.restore(else_mark);
                    expected.clone()
                } else {
                    let unit_ty = Ty::text("unit".to_string());
                    self.expect_type(expr.1, &unit_ty, expected);
                    unit_ty
                }
            }
            Expr::Match { scrutinee, cases } | Expr::Try { scrutinee, cases } => {
                let scrutinee_ty = self.infer_expr(scrutinee, locals);
                self.check_match_cases(scrutinee_ty, cases, expected, locals)
            }
            Expr::Call(call) => self.infer_call(call, locals, Some(expected)),
            Expr::Tuple(items) => self.check_tuple_expr(expr.1, items, expected, locals),
            Expr::List(items) => {
                self.check_collection_expr(expr.1, items, expected, locals, "list")
            }
            Expr::Vector(items) => {
                self.check_collection_expr(expr.1, items, expected, locals, "vector")
            }
            Expr::Struct { name, fields } => {
                self.check_struct_expr_against(expr.1, name.as_ref(), fields, expected, locals)
            }
            Expr::Update { base, fields } => {
                self.check_update_expr_against(base, fields, expected, locals)
            }
            _ => {
                let actual = self.infer_expr(expr, locals);
                self.expect_type(expr.1, &actual, expected);
                expected.clone()
            }
        };
        self.record_expr_type(expr.1, &ty);
        ty
    }

    fn check_source_file(mut self, ast: &SourceFile) -> TypeCheckResult {
        let mut global_constraints = Vec::new();
        for (item, span) in &ast.defs {
            // Cooperative cancellation: bail out at the next top-level
            // definition boundary if a newer typecheck has been queued.
            if self.cancel.is_cancelled() {
                break;
            }
            match &item.kind {
                DefinitionKind::Callable(def) => {
                    self.trace_typecheck("callable", &def.name.0, Some(*span));
                    self.check_callable_definition(def);
                }
                DefinitionKind::Named(def)
                    if matches!(
                        def.kind,
                        NamedDefKind::Register | NamedDefKind::Let | NamedDefKind::Var
                    ) =>
                {
                    self.trace_typecheck("binding", &def.name.0, Some(*span));
                    self.check_named_binding(def);
                }
                DefinitionKind::Named(def) if matches!(def.kind, NamedDefKind::Bitfield) => {
                    self.trace_typecheck("bitfield", &def.name.0, Some(*span));
                    self.check_bitfield_definition(def);
                }
                DefinitionKind::Constraint(def) if !def.is_type_constraint => {
                    self.trace_typecheck("constraint", "global", Some(*span));
                    global_constraints.push(constraint_expr_from_type_expr(self.source, &def.ty));
                    if constraints_are_contradictory(&global_constraints, &Subst::default()) {
                        self.push_error(
                            DiagnosticCode::TypeError,
                            def.ty.1,
                            TypeError::other(
                                "Global constraint appears inconsistent with previous global constraints"
                                    .to_string(),
                            ),
                        );
                    }
                }
                _ => {}
            }
        }
        self.finish()
    }

    fn check_bitfield_definition(&mut self, def: &sail_parser::core_ast::NamedDefinition) {
        let Some(ty) = &def.ty else {
            return;
        };
        let underlying = type_from_type_expr(self.source, ty);
        let width_is_known = match underlying.kind() {
            TyData::App { name, args, .. } if name == "bits" => args
                .first()
                .and_then(|arg| match arg {
                    TyArg::Value(value) => parse_numeric_expr_text(value)
                        .and_then(|expr| eval_numeric_expr(&expr, &Subst::default(), &[])),
                    TyArg::Type(inner) => parse_numeric_expr_text(&inner.display_text())
                        .and_then(|expr| eval_numeric_expr(&expr, &Subst::default(), &[])),
                })
                .is_some(),
            _ => false,
        };
        // If the underlying type is a non-`bits` type alias (e.g. xlenbits),
        // we cannot resolve it without cross-file context. Be permissive.
        let is_cross_file_alias = !matches!(underlying.kind(),
            TyData::App { name, .. } if name == "bits") && !underlying.is_unknown();
        if !width_is_known && !is_cross_file_alias {
            self.push_error(
                DiagnosticCode::TypeError,
                ty.1,
                TypeError::other(format!(
                    "Underlying bitfield type {} must be a constant-width bitvector",
                    underlying.display_text()
                )),
            );
        }

        if let Some(NamedDefDetail::Bitfield { fields }) = &def.detail {
            for field in fields {
                if field.0.name.0 == "bits" {
                    self.push_error(
                        DiagnosticCode::TypeError,
                        field.0.name.1,
                        TypeError::other(
                            "Field with name 'bits' found in bitfield definition.\n\nThis is used as the default name for all the bits in the bitfield, so should not be overridden.".to_string(),
                        ),
                    );
                }
            }
        }
    }

    fn check_named_binding(&mut self, def: &sail_parser::core_ast::NamedDefinition) {
        let Some(value) = &def.value else {
            return;
        };
        let expected_ty = def
            .ty
            .as_ref()
            .map(|ty| type_from_type_expr(self.source, ty));
        let mut locals = LocalEnv::new(expected_ty.clone());
        let value_ty = if let Some(expected_ty) = &expected_ty {
            self.check_expr(value, expected_ty, &mut locals)
        } else {
            self.infer_expr(value, &mut locals)
        };
        if let Some(expected_ty) = &expected_ty {
            self.record_binding_type(def.name.1, expected_ty);
        } else {
            self.record_binding_type(def.name.1, &value_ty);
        }
    }

    fn check_callable_definition(&mut self, def: &sail_parser::core_ast::CallableDefinition) {
        if matches!(
            def.kind,
            CallableDefKind::Mapping | CallableDefKind::MappingClause
        ) {
            self.check_mapping_definition(def);
            return;
        }

        if !matches!(
            def.kind,
            CallableDefKind::Function | CallableDefKind::FunctionClause
        ) {
            return;
        }

        let expected_scheme: Option<Arc<TypeScheme>> = self
            .env
            .functions
            .get(&def.name.0)
            .and_then(|schemes| schemes.first().cloned())
            .or_else(|| {
                def.signature
                    .as_ref()
                    .map(|ty| Arc::new(scheme_from_type_expr(self.source, ty)))
            })
            .or_else(|| scheme_from_callable_head(self.source, def).map(Arc::new));

        if def.clauses.is_empty() {
            let mut locals =
                LocalEnv::new(expected_scheme.as_ref().map(|scheme| scheme.ret.clone()));
            if let Some(scheme) = &expected_scheme {
                for (param, expected_ty) in def.params.iter().zip(scheme.params.iter()) {
                    self.bind_pattern(param, Some(expected_ty.clone()), &mut locals);
                }
            } else {
                for param in &def.params {
                    self.bind_pattern(param, None, &mut locals);
                }
            }
            if let Some(body) = &def.body {
                if let Some(expected) = expected_scheme.as_ref().map(|scheme| scheme.ret.clone()) {
                    self.check_expr(body, &expected, &mut locals);
                } else {
                    self.infer_expr(body, &mut locals);
                }
            }
            return;
        }

        for clause in &def.clauses {
            self.check_callable_clause(clause, expected_scheme.as_deref());
        }
    }

    fn check_callable_clause(
        &mut self,
        clause: &Spanned<CallableClause>,
        expected_scheme: Option<&TypeScheme>,
    ) {
        let mut locals = LocalEnv::new(expected_scheme.map(|scheme| scheme.ret.clone()));
        if let Some(scheme) = expected_scheme {
            // A `val f : (A, B) -> C` declaration gives a single tuple
            // param, but the clause can be written as `function clause
            // f(a, b) = ...` with two separate patterns. Flatten the
            // tuple so each pattern gets bound with its matching type —
            // otherwise `b` above would never enter locals and every
            // reference to it would fire as "Unresolved identifier".
            let mut param_tys = scheme.params.clone();
            if param_tys.len() == 1 && clause.0.patterns.len() > 1 {
                if let TyData::Tuple(items) = param_tys[0].kind() {
                    if items.len() == clause.0.patterns.len() {
                        param_tys = items.clone();
                    }
                }
            }
            for (pattern, expected_ty) in clause.0.patterns.iter().zip(param_tys.iter()) {
                self.bind_pattern(pattern, Some(expected_ty.clone()), &mut locals);
            }
        } else {
            for pattern in &clause.0.patterns {
                self.bind_pattern(pattern, None, &mut locals);
            }
        }
        if let Some(guard) = &clause.0.guard {
            let guard_ty = self.infer_expr(guard, &mut locals);
            let mut subst = Subst::default();
            if !guard_ty.is_unknown()
                && !unify(&Ty::text("bool".to_string()), &guard_ty, &mut subst)
            {
                self.push_error(
                    DiagnosticCode::TypeError,
                    guard.1,
                    TypeError::Subtype {
                        lhs: guard_ty.display_text(),
                        rhs: "bool".to_string(),
                        constraint: None,
                    },
                );
            }
            self.add_expr_constraint(&mut locals, guard, true);
        }
        if let Some(body) = &clause.0.body {
            if let Some(expected) = expected_scheme.map(|scheme| scheme.ret.clone()) {
                self.check_expr(body, &expected, &mut locals);
            } else {
                self.infer_expr(body, &mut locals);
            }
        }
    }

    fn collect_vector_concat_pattern_parts<'b>(
        &self,
        pattern: &'b Spanned<Pattern>,
        parts: &mut Vec<&'b Spanned<Pattern>>,
    ) {
        let mut stack = vec![pattern];
        while let Some(pattern) = stack.pop() {
            match &pattern.0 {
                Pattern::Infix { lhs, op, rhs } if op.0 == "@" => {
                    stack.push(rhs);
                    stack.push(lhs);
                }
                _ => parts.push(pattern),
            }
        }
    }

    fn bind_vector_concat_pattern(
        &mut self,
        pattern: &Spanned<Pattern>,
        expected_ty: Option<&Ty>,
        locals: &mut LocalEnv,
    ) {
        let mut parts = Vec::new();
        self.collect_vector_concat_pattern_parts(pattern, &mut parts);

        let Some(expected_ty) = expected_ty else {
            for part in parts {
                self.bind_pattern_inner(part, None, locals);
            }
            return;
        };

        let Some(total_width) = self
            .collection_length_text(expected_ty)
            .and_then(|text| parse_int_literal(&text))
        else {
            for part in parts {
                self.bind_pattern_inner(part, None, locals);
            }
            return;
        };

        let widths = parts
            .iter()
            .map(|part| pattern_static_bit_width(self.source, part))
            .collect::<Vec<_>>();
        let known_width = widths.iter().flatten().sum::<i64>();
        if known_width > total_width {
            for part in parts {
                self.bind_pattern_inner(part, None, locals);
            }
            return;
        }

        let unknown_count = widths.iter().filter(|width| width.is_none()).count();
        let inferred_unknown_width = match unknown_count {
            0 if known_width == total_width => None,
            1 => Some(total_width - known_width),
            _ => None,
        };
        let vector_elem_ty = self.collection_element_type(expected_ty);
        let expected_is_vector =
            matches!(expected_ty.kind(), TyData::App { name, .. } if name == "vector");
        let mk_expected = |width| {
            if expected_is_vector {
                vector_ty(width, vector_elem_ty.clone().unwrap_or(Ty::unknown()))
            } else {
                bits_ty(width)
            }
        };

        for (part, width) in parts.into_iter().zip(widths.into_iter()) {
            let expected = width.or(inferred_unknown_width).map(&mk_expected);
            self.bind_pattern_inner(part, expected, locals);
        }
    }

    fn bind_struct_pattern(
        &mut self,
        pattern_span: Span,
        name: Option<&Spanned<String>>,
        fields: &[Spanned<FieldPattern>],
        expected_ty: Option<Ty>,
        locals: &mut LocalEnv,
    ) {
        let record_ty = expected_ty
            .clone()
            .or_else(|| name.as_ref().map(|name| Ty::text(name.0.clone())));
        let record_info = record_ty
            .as_ref()
            .and_then(|record_ty| self.record_info_for_type(record_ty));

        if let Some(name) = name {
            match &record_info {
                Some((record_name, _, _)) if &name.0 != record_name => {
                    self.push_error(
                        DiagnosticCode::TypeError,
                        name.1,
                        TypeError::other(format!(
                            "Struct type {} found, {} expected",
                            name.0, record_name
                        )),
                    );
                }
                None => {
                    // Skip when the record might be defined in another file.
                    if !self.env.cross_file_function_names.contains(&name.0) {
                        // Heuristic: if the name appears as a constructor or
                        // is otherwise visible cross-file, don't error.
                        // For now, suppress all "Unknown record type" errors —
                        // these are usually cross-file struct definitions.
                    }
                }
                _ => {}
            }
        } else if let Some(expected) = &record_ty {
            if record_info.is_none()
                && !expected.is_unknown()
                && is_known_non_record(expected)
            {
                self.push_error(
                    DiagnosticCode::TypeError,
                    pattern_span,
                    TypeError::other(format!("The type {} is not a record", expected.display_text())),
                );
            }
        }

        let mut remaining_fields = record_info
            .as_ref()
            .map(|(_, info, _)| info.fields.keys().cloned().collect::<HashSet<_>>())
            .unwrap_or_default();
        let mut has_wildcard = false;

        for field in fields {
            match &field.0 {
                FieldPattern::Binding {
                    name: field_name,
                    pattern,
                } => {
                    let expected = record_ty
                        .as_ref()
                        .and_then(|record_ty| self.record_field_type(record_ty, &field_name.0));
                    if expected.is_none() && record_info.is_some() {
                        self.push_error(
                            DiagnosticCode::TypeError,
                            field_name.1,
                            TypeError::other(format!(
                                "Record {} has no field {}",
                                record_info.as_ref().map(|(name, _, _)| name).unwrap(),
                                field_name.0
                            )),
                        );
                    }
                    remaining_fields.remove(&field_name.0);
                    self.bind_pattern_inner(pattern, expected, locals);
                }
                FieldPattern::Shorthand(field_name) => {
                    let expected = record_ty
                        .as_ref()
                        .and_then(|record_ty| self.record_field_type(record_ty, &field_name.0))
                        .unwrap_or(Ty::unknown());
                    if expected.is_unknown() && record_info.is_some() {
                        self.push_error(
                            DiagnosticCode::TypeError,
                            field_name.1,
                            TypeError::other(format!(
                                "Record {} has no field {}",
                                record_info.as_ref().map(|(name, _, _)| name).unwrap(),
                                field_name.0
                            )),
                        );
                    }
                    remaining_fields.remove(&field_name.0);
                    self.bind_pattern_inner(
                        &(Pattern::Ident(field_name.0.clone()), field_name.1),
                        Some(expected),
                        locals,
                    );
                }
                FieldPattern::Wild(_) => has_wildcard = true,
            }
        }

        if !has_wildcard && !remaining_fields.is_empty() {
            let mut missing = remaining_fields.into_iter().collect::<Vec<_>>();
            missing.sort();
            self.push_error(
                DiagnosticCode::TypeError,
                pattern_span,
                TypeError::other(format!(
                    "struct pattern missing fields: {}",
                    missing.join(", ")
                )),
            );
        }
    }

    fn bind_pattern(
        &mut self,
        pattern: &Spanned<Pattern>,
        expected_ty: Option<Ty>,
        locals: &mut LocalEnv,
    ) {
        self.precheck_pattern(pattern, locals);
        self.bind_pattern_inner(pattern, expected_ty, locals);
    }

    fn bind_pattern_inner(
        &mut self,
        pattern: &Spanned<Pattern>,
        expected_ty: Option<Ty>,
        locals: &mut LocalEnv,
    ) {
        match &pattern.0 {
            Pattern::Attribute { pattern, .. } => {
                self.bind_pattern_inner(pattern, expected_ty, locals);
            }
            Pattern::Ident(name) => {
                if is_pattern_binding(name, &self.pattern_constants, self.env.has_workspace_context) {
                    let ty = expected_ty.unwrap_or(Ty::unknown());
                    locals.define(name, ty.clone());
                    self.record_binding_type(pattern.1, &ty);
                }
            }
            Pattern::Typed(inner, ty) | Pattern::AsType(inner, ty) => {
                let annotated = type_from_type_expr(self.source, ty);
                if let Some(expected) = expected_ty {
                    let mut subst = Subst::default();
                    if !expected.is_unknown()
                        && !annotated.is_unknown()
                        && !unify(&annotated, &expected, &mut subst)
                    {
                        self.push_error(
                            DiagnosticCode::TypeError,
                            ty.1,
                            TypeError::Subtype {
                                lhs: expected.display_text(),
                                rhs: annotated.display_text(),
                                constraint: None,
                            },
                        );
                    }
                }
                self.bind_pattern_inner(inner, Some(annotated), locals);
            }
            Pattern::AsBinding {
                pattern: inner,
                binding,
            } => {
                self.bind_pattern_inner(inner, expected_ty.clone(), locals);
                let ty = expected_ty.unwrap_or(Ty::unknown());
                locals.define(&binding.0, ty.clone());
                self.record_binding_type(binding.1, &ty);
            }
            Pattern::Tuple(items) => {
                let tuple_items = match expected_ty.as_ref().map(|t| t.kind()) {
                    Some(TyData::Tuple(expected_items))
                        if expected_items.len() == items.len() =>
                    {
                        Some(expected_items.clone())
                    }
                    Some(_)
                        if !expected_ty
                            .as_ref()
                            .map(|t| t.is_unknown())
                            .unwrap_or(true) =>
                    {
                        let display = expected_ty
                            .as_ref()
                            .map(|t| t.display_text())
                            .unwrap_or_default();
                        self.push_error(
                            DiagnosticCode::TypeError,
                            pattern.1,
                            TypeError::other(format!(
                                "Cannot bind tuple pattern against non tuple type {}",
                                display
                            )),
                        );
                        None
                    }
                    _ => None,
                };
                for (index, item) in items.iter().enumerate() {
                    self.bind_pattern_inner(
                        item,
                        tuple_items
                            .as_ref()
                            .and_then(|items| items.get(index).cloned()),
                        locals,
                    );
                }
            }
            Pattern::Struct { fields, name } => {
                self.bind_struct_pattern(pattern.1, name.as_ref(), fields, expected_ty, locals);
            }
            Pattern::List(items) | Pattern::Vector(items) => {
                let element_ty = expected_ty
                    .as_ref()
                    .and_then(|ty| self.collection_element_type(ty));
                for item in items {
                    self.bind_pattern_inner(item, element_ty.clone(), locals);
                }
            }
            Pattern::App { args, callee } => {
                let expected_ty = expected_ty.unwrap_or(Ty::unknown());
                let candidates = self.env.lookup_constructors(&callee.0);
                let mappings = self.env.lookup_mappings(&callee.0);
                let mut assumptions = Vec::new();
                self.fill_assumptions(locals, &mut assumptions);
                if args.len() > 1 && (!candidates.is_empty() || !mappings.is_empty()) {
                    let tuple_pattern = (
                        Pattern::Tuple(args.clone()),
                        Span::new(
                            args[0].1.start,
                            args.last().map(|arg| arg.1.end).unwrap_or(pattern.1.end),
                        ),
                    );
                    self.bind_pattern_inner(
                        &(
                            Pattern::App {
                                callee: callee.clone(),
                                args: vec![tuple_pattern],
                            },
                            pattern.1,
                        ),
                        Some(expected_ty),
                        locals,
                    );
                    return;
                }
                if candidates.is_empty() {
                    if let Some(arg) = args.first() {
                        if !mappings.is_empty() {
                            if expected_ty.is_unknown() {
                                let mapping = &mappings[0];
                                self.bind_pattern_inner(arg, Some(mapping.lhs.clone()), locals);
                                return;
                            }

                            let mut first_mapping_error = None;
                            for mapping in mappings {
                                let sig = format_mapping_signature(mapping.as_ref());
                                let mut backwards_subst = Subst::default();
                                if unify(&mapping.rhs, &expected_ty, &mut backwards_subst) {
                                    if let Some(error) = self.instantiation_error_with_sig(
                                        &callee.0,
                                        &mapping.quantifiers,
                                        &mapping.constraints,
                                        &backwards_subst,
                                        &assumptions,
                                        Some(sig.clone()),
                                    ) {
                                        first_mapping_error.get_or_insert(error);
                                    } else {
                                        self.bind_pattern_inner(
                                            arg,
                                            Some(apply_subst(&mapping.lhs, &backwards_subst)),
                                            locals,
                                        );
                                        return;
                                    }
                                }

                                let mut forwards_subst = Subst::default();
                                if unify(&mapping.lhs, &expected_ty, &mut forwards_subst) {
                                    if let Some(error) = self.instantiation_error_with_sig(
                                        &callee.0,
                                        &mapping.quantifiers,
                                        &mapping.constraints,
                                        &forwards_subst,
                                        &assumptions,
                                        Some(sig),
                                    ) {
                                        first_mapping_error.get_or_insert(error);
                                    } else {
                                        self.bind_pattern_inner(
                                            arg,
                                            Some(apply_subst(&mapping.rhs, &forwards_subst)),
                                            locals,
                                        );
                                        return;
                                    }
                                }
                            }

                            if let Some(error) = first_mapping_error {
                                self.push_error(DiagnosticCode::TypeError, pattern.1, error);
                            } else {
                                self.push_error(
                                    DiagnosticCode::TypeError,
                                    pattern.1,
                                    TypeError::other(format!(
                                        "Pattern {} does not match type {}",
                                        callee.0,
                                        expected_ty.display_text()
                                    )),
                                );
                            }
                            return;
                        }
                    }

                    for arg in args {
                        self.bind_pattern_inner(arg, None, locals);
                    }
                    return;
                }

                let mut count_mismatch = None;
                let mut first_candidate_error = None;
                for candidate in candidates {
                    let mut candidate_params = candidate.params.clone();
                    if args.len() != candidate_params.len() && candidate_params.len() == 1 {
                        if let TyData::Tuple(items) = candidate_params[0].kind() {
                            if items.len() == args.len() {
                                candidate_params = items.clone();
                            }
                        }
                    }
                    if args.len() != candidate_params.len() {
                        count_mismatch = Some(candidate_params.len());
                        continue;
                    }

                    let mut subst = Subst::default();
                    if !unify(&candidate.ret, &expected_ty, &mut subst) && !expected_ty.is_unknown()
                    {
                        continue;
                    }
                    if let Some(error) = self.instantiation_error_with_sig(
                        &callee.0,
                        &candidate.quantifiers,
                        &candidate.constraints,
                        &subst,
                        &assumptions,
                        Some(format_scheme_signature(candidate.as_ref())),
                    ) {
                        first_candidate_error.get_or_insert(error);
                        continue;
                    }

                    for (arg, param_ty) in args.iter().zip(candidate_params.iter()) {
                        self.bind_pattern_inner(arg, Some(apply_subst(param_ty, &subst)), locals);
                    }
                    return;
                }

                if let Some(expected) = count_mismatch {
                    self.push_error(
                        DiagnosticCode::TypeError,
                        pattern.1,
                        TypeError::other(format!(
                            "Constructor {} expects {} arguments, found {}",
                            callee.0,
                            expected,
                            args.len()
                        )),
                    );
                } else if let Some(error) = first_candidate_error {
                    self.push_error(DiagnosticCode::TypeError, pattern.1, error);
                } else if !expected_ty.is_unknown() {
                    self.push_error(
                        DiagnosticCode::TypeError,
                        pattern.1,
                        TypeError::other(format!(
                            "Pattern {} does not match type {}",
                            callee.0,
                            expected_ty.display_text()
                        )),
                    );
                }
            }
            Pattern::Infix { lhs, op, rhs } => match op.0.as_str() {
                "::" => {
                    if let Some(expected) = expected_ty.as_ref() {
                        if let Some(element_ty) = self.collection_element_type(expected) {
                            self.bind_pattern_inner(lhs, Some(element_ty), locals);
                            self.bind_pattern_inner(rhs, Some(expected.clone()), locals);
                        } else {
                            self.push_error(
                                DiagnosticCode::TypeError,
                                pattern.1,
                                TypeError::other(format!(
                                    "Cannot match cons pattern against non-list type {}",
                                    expected.display_text()
                                )),
                            );
                        }
                    } else {
                        self.bind_pattern_inner(lhs, None, locals);
                        self.bind_pattern_inner(rhs, None, locals);
                    }
                }
                "^" => {
                    let string_ty = match expected_ty.as_ref() {
                        Some(expected)
                            if expected.display_text() == "string"
                                || expected.display_text() == "string_literal" =>
                        {
                            expected.clone()
                        }
                        Some(expected) if !expected.is_unknown() => {
                            self.push_error(
                                DiagnosticCode::TypeError,
                                pattern.1,
                                TypeError::other(format!(
                                    "Cannot match string-append pattern against non-string type {}",
                                    expected.display_text()
                                )),
                            );
                            Ty::text("string".to_string())
                        }
                        _ => Ty::text("string".to_string()),
                    };
                    self.bind_pattern_inner(lhs, Some(string_ty.clone()), locals);
                    self.bind_pattern_inner(rhs, Some(string_ty), locals);
                }
                "@" => {
                    self.bind_vector_concat_pattern(pattern, expected_ty.as_ref(), locals);
                }
                _ => {
                    self.bind_pattern_inner(lhs, None, locals);
                    self.bind_pattern_inner(rhs, None, locals);
                }
            },
            Pattern::Index { index, .. } => {
                if let Some(width) = type_expr_static_int(self.source, index).map(|_| 1) {
                    let slice_ty = bits_ty(width);
                    if let Some(expected) = expected_ty.as_ref() {
                        self.expect_type(pattern.1, &slice_ty, expected);
                    }
                }
            }
            Pattern::RangeIndex { start, end, .. } => {
                if let Some((hi, lo)) = self.pattern_index_range(pattern.1, start, end) {
                    let slice_ty = bits_ty(hi - lo + 1);
                    if let Some(expected) = expected_ty.as_ref() {
                        self.expect_type(pattern.1, &slice_ty, expected);
                    }
                }
            }
            Pattern::Literal(literal) => {
                if let Some(expected) = expected_ty.as_ref() {
                    let actual = infer_literal_type(literal);
                    self.expect_type(pattern.1, &actual, expected);
                }
            }
            Pattern::TypeVar(name) => {
                // `let 'X = e` in Sail simultaneously binds the type
                // variable `'X` and a value `X` (without the tick). The
                // lexer currently carries the leading `'` through, so
                // strip it before defining the value binding.
                let value_name = name.strip_prefix('\'').unwrap_or(name);
                let ty = expected_ty.unwrap_or(Ty::unknown());
                locals.define(value_name, ty.clone());
                self.record_binding_type(pattern.1, &ty);
            }
            Pattern::Wild | Pattern::Error(_) => {}
        }
    }

    fn infer_expr(&mut self, expr: &Spanned<Expr>, locals: &mut LocalEnv) -> Ty {
        let mut current = expr;
        let mut chain_mark = None;
        let mut wrapper_spans = Vec::new();
        loop {
            match &current.0 {
                Expr::Attribute { expr: inner, .. } => {
                    wrapper_spans.push(current.1);
                    current = inner;
                }
                Expr::Let { binding, body } => {
                    wrapper_spans.push(current.1);
                    let value_ty = if let Some(expected_bind) =
                        pattern_annotation_type(self.source, &binding.pattern)
                    {
                        self.check_expr(&binding.value, &expected_bind, locals);
                        expected_bind
                    } else {
                        self.infer_expr(&binding.value, locals)
                    };
                    if chain_mark.is_none() {
                        chain_mark = Some(locals.snapshot());
                    }
                    locals.push_scope();
                    self.bind_pattern(&binding.pattern, Some(value_ty), locals);
                    current = body;
                }
                _ => break,
            }
        }

        let ty = self.infer_expr_dispatch(current, locals);
        if let Some(mark) = chain_mark {
            locals.restore(mark);
        }
        for span in wrapper_spans {
            self.record_expr_type(span, &ty);
        }
        ty
    }

    fn infer_expr_dispatch(&mut self, expr: &Spanned<Expr>, locals: &mut LocalEnv) -> Ty {
        let ty = match &expr.0 {
            Expr::Attribute { expr, .. } => self.infer_expr(expr, locals),
            Expr::Assign { lhs, rhs } => {
                let lhs_ty = self.infer_lexp(lhs, locals);
                let rhs_ty = self.infer_expr(rhs, locals);
                if !lhs_ty.is_unknown() {
                    self.expect_type(rhs.1, &rhs_ty, &lhs_ty);
                }
                // Sail assignments are statements that always have type unit,
                // not the rhs type. (Previously returned rhs_ty, which caused
                // false-positive "X is not a subtype of unit" errors when the
                // assignment was the last expression of a unit-returning fn.)
                Ty::text("unit".to_string())
            }
            Expr::Let { binding, body } => {
                let value_ty = if let Some(expected_bind) =
                    pattern_annotation_type(self.source, &binding.pattern)
                {
                    self.check_expr(&binding.value, &expected_bind, locals);
                    expected_bind
                } else {
                    self.infer_expr(&binding.value, locals)
                };
                locals.push_scope();
                self.bind_pattern(&binding.pattern, Some(value_ty), locals);
                let body_ty = self.infer_expr(body, locals);
                locals.pop_scope();
                body_ty
            }
            Expr::Var {
                target,
                value,
                body,
            } => {
                let value_ty = self.infer_var_target_value(target, value, locals);
                locals.push_scope();
                self.bind_var_target_declaration(target, &value_ty, locals);
                let body_ty = self.infer_expr(body, locals);
                locals.pop_scope();
                body_ty
            }
            Expr::Block(items) => {
                locals.push_scope();
                let mut last_ty = Ty::text("unit".to_string());
                for item in items {
                    match &item.0 {
                        sail_parser::BlockItem::Let(binding) => {
                            self.trace_typecheck("block-let", "_", Some(binding.value.1));
                        }
                        sail_parser::BlockItem::Var { value, .. } => {
                            self.trace_typecheck("block-var", "_", Some(value.1));
                        }
                        sail_parser::BlockItem::Expr(expr) => {
                            self.trace_typecheck(
                                "block-expr",
                                expr_kind_name(&expr.0),
                                Some(expr.1),
                            );
                        }
                    }
                    last_ty = match &item.0 {
                        sail_parser::BlockItem::Let(binding) => {
                            let value_ty = if let Some(expected_bind) =
                                pattern_annotation_type(self.source, &binding.pattern)
                            {
                                self.check_expr(&binding.value, &expected_bind, locals);
                                expected_bind
                            } else {
                                self.infer_expr(&binding.value, locals)
                            };
                            self.bind_pattern(&binding.pattern, Some(value_ty), locals);
                            Ty::text("unit".to_string())
                        }
                        sail_parser::BlockItem::Var { target, value } => {
                            let value_ty = self.infer_var_target_value(target, value, locals);
                            self.bind_var_target_declaration(target, &value_ty, locals);
                            Ty::text("unit".to_string())
                        }
                        sail_parser::BlockItem::Expr(expr) => {
                            let ty = self.infer_expr(expr, locals);
                            self.propagate_post_expr_constraints(expr, locals);
                            ty
                        }
                    };
                }
                locals.pop_scope();
                last_ty
            }
            Expr::Return(expr) => {
                let value_ty = self.infer_expr(expr, locals);
                if let Some(expected) = &locals.expected_return {
                    let mut subst = Subst::default();
                    if !value_ty.is_unknown()
                        && !expected.is_unknown()
                        && !unify(expected, &value_ty, &mut subst)
                    {
                        self.push_error(
                            DiagnosticCode::TypeError,
                            expr.1,
                            TypeError::Subtype {
                                lhs: value_ty.display_text(),
                                rhs: expected.display_text(),
                                constraint: None,
                            },
                        );
                    }
                }
                // `return` is diverging — return Unknown so it unifies with
                // any sibling branch type.
                Ty::unknown()
            }
            Expr::Throw(expr) => {
                self.infer_expr(expr, locals);
                // `throw` is diverging — return Unknown so it unifies with any
                // sibling branch type.
                Ty::unknown()
            }
            Expr::Assert { condition, message } => {
                let cond_ty = self.infer_expr(condition, locals);
                let mut subst = Subst::default();
                if !cond_ty.is_unknown()
                    && !unify(&Ty::text("bool".to_string()), &cond_ty, &mut subst)
                {
                    self.push_error(
                        DiagnosticCode::TypeError,
                        condition.1,
                        TypeError::Subtype {
                            lhs: cond_ty.display_text(),
                            rhs: "bool".to_string(),
                            constraint: None,
                        },
                    );
                }
                if let Some(message) = message {
                    self.infer_expr(message, locals);
                }
                self.add_expr_constraint(locals, condition, true);
                Ty::text("unit".to_string())
            }
            Expr::Exit(expr) => {
                if let Some(inner) = expr.as_ref() {
                    self.infer_expr(inner, locals);
                }
                // `exit` has the diverging type `forall 'a. _ -> 'a` — it
                // never returns. In a match/if branch alongside other arms,
                // its type should unify with any sibling. Return Unknown so
                // our case-type unifier treats it as compatible.
                Ty::unknown()
            }
            Expr::If {
                cond,
                then_branch,
                else_branch,
            } => {
                let cond_ty = self.infer_expr(cond, locals);
                let mut subst = Subst::default();
                if !cond_ty.is_unknown()
                    && !unify(&Ty::text("bool".to_string()), &cond_ty, &mut subst)
                {
                    self.push_error(
                        DiagnosticCode::TypeError,
                        cond.1,
                        TypeError::Subtype {
                            lhs: cond_ty.display_text(),
                            rhs: "bool".to_string(),
                            constraint: None,
                        },
                    );
                }
                let then_mark = locals.snapshot();
                self.add_expr_constraint(locals, cond, true);
                let then_ty = self.infer_expr(then_branch, locals);
                locals.restore(then_mark);
                let else_ty = else_branch
                    .as_ref()
                    .map(|branch| {
                        let else_mark = locals.snapshot();
                        self.add_expr_constraint(locals, cond, false);
                        let else_ty = self.infer_expr(branch, locals);
                        locals.restore(else_mark);
                        else_ty
                    })
                    .unwrap_or_else(|| Ty::text("unit".to_string()));
                let mut subst = Subst::default();
                // If either branch diverges (Unknown), return the OTHER branch's
                // type since the Unknown branch never completes.
                if then_ty.is_unknown() {
                    else_ty
                } else if else_ty.is_unknown() {
                    then_ty
                } else if self.unify_with_aliases(&then_ty, &else_ty, &mut subst) {
                    apply_subst(&then_ty, &subst)
                } else {
                    self.push_error(
                        DiagnosticCode::TypeError,
                        expr.1,
                        TypeError::Subtype {
                            lhs: else_ty.display_text(),
                            rhs: then_ty.display_text(),
                            constraint: None,
                        },
                    );
                    Ty::unknown()
                }
            }
            Expr::Match { scrutinee, cases } | Expr::Try { scrutinee, cases } => {
                let scrutinee_ty = self.infer_expr(scrutinee, locals);
                self.infer_match_cases(scrutinee_ty, cases, locals)
            }
            Expr::Foreach(foreach) => {
                let start_ty = self.infer_expr(&foreach.start, locals);
                self.expect_int_type(foreach.start.1, &start_ty);
                let end_ty = self.infer_expr(&foreach.end, locals);
                self.expect_int_type(foreach.end.1, &end_ty);
                if let Some(step) = &foreach.step {
                    let step_ty = self.infer_expr(step, locals);
                    self.expect_int_type(step.1, &step_ty);
                }
                locals.push_scope();
                let iter_ty = foreach
                    .ty
                    .as_ref()
                    .map(|ty| type_from_type_expr(self.source, ty))
                    .unwrap_or_else(|| Ty::text("int".to_string()));
                locals.define(&foreach.iterator.0, iter_ty.clone());
                self.record_binding_type(foreach.iterator.1, &iter_ty);
                self.infer_expr(&foreach.body, locals);
                locals.pop_scope();
                Ty::text("unit".to_string())
            }
            Expr::Repeat {
                measure,
                body,
                until,
            } => {
                if let Some(measure) = measure {
                    self.infer_expr(measure, locals);
                }
                self.infer_expr(body, locals);
                let until_ty = self.infer_expr(until, locals);
                let mut subst = Subst::default();
                if !until_ty.is_unknown()
                    && !unify(&Ty::text("bool".to_string()), &until_ty, &mut subst)
                {
                    self.push_error(
                        DiagnosticCode::TypeError,
                        until.1,
                        TypeError::Subtype {
                            lhs: until_ty.display_text(),
                            rhs: "bool".to_string(),
                            constraint: None,
                        },
                    );
                }
                Ty::text("unit".to_string())
            }
            Expr::While {
                measure,
                cond,
                body,
            } => {
                if let Some(measure) = measure {
                    self.infer_expr(measure, locals);
                }
                let cond_ty = self.infer_expr(cond, locals);
                let mut subst = Subst::default();
                if !unify(&Ty::text("bool".to_string()), &cond_ty, &mut subst) {
                    self.push_error(
                        DiagnosticCode::TypeError,
                        cond.1,
                        TypeError::Subtype {
                            lhs: cond_ty.display_text(),
                            rhs: "bool".to_string(),
                            constraint: None,
                        },
                    );
                }
                self.infer_expr(body, locals);
                Ty::text("unit".to_string())
            }
            Expr::Infix { lhs, op, rhs } => self.infer_infix(expr, lhs, op.0.as_str(), rhs, locals),
            Expr::Prefix { op, expr: inner } => {
                let inner_ty = self.infer_expr(inner, locals);
                match op.0.as_str() {
                    "not" => {
                        let mut subst = Subst::default();
                        if !inner_ty.is_unknown()
                            && !unify(&Ty::text("bool".to_string()), &inner_ty, &mut subst)
                        {
                            self.push_error(
                                DiagnosticCode::TypeError,
                                inner.1,
                                TypeError::Subtype {
                                    lhs: inner_ty.display_text(),
                                    rhs: "bool".to_string(),
                                    constraint: None,
                                },
                            );
                        }
                        Ty::text("bool".to_string())
                    }
                    // Negation and bitwise NOT preserve the inner type.
                    "-" | "~" => inner_ty,
                    _ => Ty::unknown(),
                }
            }
            Expr::Cast { ty, .. } => type_from_type_expr(self.source, ty),
            Expr::Config(_) => Ty::unknown(),
            Expr::Literal(literal) => infer_literal_type(literal),
            Expr::Ident(name) => {
                if let Some(ty) = self.env.lookup_value(locals, name) {
                    ty
                } else {
                    // Under workspace-aware analysis, if a bare identifier
                    // isn't known anywhere in the workspace (cross-file
                    // values/functions/constructors/registers/enum-members
                    // or the upstream prelude whitelist), it's a genuine
                    // unresolved reference — report it. In single-file mode
                    // the cross-file sets are empty, so we stay silent to
                    // avoid a flood of false positives.
                    if self.env.has_workspace_context
                        && !self.env.top_level_symbol_exists(name)
                        && !self.pattern_constants.contains(name)
                    {
                        self.push_error(
                            DiagnosticCode::TypeError,
                            expr.1,
                            TypeError::Other(format!("Unresolved identifier `{name}`")),
                        );
                    }
                    Ty::unknown()
                }
            }
            Expr::TypeVar(name) => Ty::var(name.clone()),
            Expr::Ref(name) => {
                if let Some(ty) = self.register_type_for_name(&name.0) {
                    register_ty(ty)
                } else {
                    // `&reg` must refer to a register. Report only when
                    // workspace context is active and the name is not a
                    // register anywhere.
                    if self.env.has_workspace_context
                        && !self.env.registers.contains_key(&name.0)
                        && !self.env.cross_file_register_names.contains(&name.0)
                    {
                        self.push_error(
                            DiagnosticCode::TypeError,
                            name.1,
                            TypeError::Other(format!("Unresolved register `{}`", name.0)),
                        );
                    }
                    Ty::unknown()
                }
            }
            Expr::Call(call) => self.infer_call(call, locals, None),
            Expr::Field {
                expr: inner, field, ..
            } => {
                let base_ty = self.infer_expr(inner, locals);
                // Field access on Unknown (typically from cross-file functions
                // returning unresolved types) shouldn't produce errors.
                if base_ty.is_unknown() {
                    return Ty::unknown();
                }
                match self.record_field_type(&base_ty, &field.0) {
                    Some(field_ty) => field_ty,
                    None => match self.bitfield_field_type(&base_ty, &field.0) {
                        Some(field_ty) => field_ty,
                        None => {
                            if self.record_info_for_type(&base_ty).is_some() {
                                self.push_error(
                                    DiagnosticCode::TypeError,
                                    field.1,
                                    TypeError::other(format!(
                                        "Record {} has no field {}",
                                        base_ty.display_text(),
                                        field.0
                                    )),
                                );
                            } else if let Some((bitfield_name, _)) =
                                self.bitfield_info_for_type(&base_ty)
                            {
                                self.push_error(
                                    DiagnosticCode::TypeError,
                                    field.1,
                                    TypeError::other(format!(
                                        "Unknown field {} in bitfield {}",
                                        field.0, bitfield_name
                                    )),
                                );
                            } else {
                                // For unresolved cross-file types (e.g. Minterrupts
                                // from another file), we can't tell if it's a record
                                // or what fields it has. Skip the error to avoid
                                // thousands of false positives.
                                if !is_known_non_record(&base_ty) {
                                    return Ty::unknown();
                                }
                                self.push_error(
                                    DiagnosticCode::TypeError,
                                    inner.1,
                                    TypeError::other(format!(
                                        "The type {} is not a record",
                                        base_ty.display_text()
                                    )),
                                );
                            }
                            Ty::unknown()
                        }
                    },
                }
            }
            Expr::SizeOf(_) => Ty::text("int".to_string()),
            Expr::Constraint(_) => Ty::text("bool".to_string()),
            Expr::Struct { name, fields } => {
                self.infer_struct_expr(expr.1, name.as_ref(), fields, locals)
            }
            Expr::Update { base, fields } => self.infer_update_expr(base, fields, locals),
            Expr::List(items) => infer_collection_type(self, items, locals, "list"),
            Expr::Vector(items) => infer_collection_type(self, items, locals, "vector"),
            Expr::Tuple(items) => Ty::tuple(
                items
                    .iter()
                    .map(|item| self.infer_expr(item, locals))
                    .collect(),
            ),
            Expr::Error(_) => Ty::unknown(),
        };
        self.record_expr_type(expr.1, &ty);
        ty
    }

    fn concat_operand_info(&self, ty: &Ty) -> Option<ConcatOperandInfo> {
        match ty.kind() {
            TyData::Text(text) if text == "bit" => Some(ConcatOperandInfo {
                width: "1".to_string(),
                elem: Ty::text("bit".to_string()),
                is_vector: false,
            }),
            TyData::App { name, .. } if name == "bits" => Some(ConcatOperandInfo {
                width: self.collection_length_text(ty)?,
                elem: Ty::text("bit".to_string()),
                is_vector: false,
            }),
            TyData::App { name, .. } if name == "vector" => Some(ConcatOperandInfo {
                width: self.collection_length_text(ty)?,
                elem: self.collection_element_type(ty)?,
                is_vector: true,
            }),
            _ => None,
        }
    }

    fn concat_width_text(&self, lhs: &str, rhs: &str) -> String {
        let lhs_value = parse_numeric_expr_text(lhs)
            .and_then(|expr| eval_numeric_expr(&expr, &Subst::default(), &[]));
        let rhs_value = parse_numeric_expr_text(rhs)
            .and_then(|expr| eval_numeric_expr(&expr, &Subst::default(), &[]));
        match (lhs_value, rhs_value) {
            (Some(lhs), Some(rhs)) => (lhs + rhs).to_string(),
            _ => format!("({lhs}) + ({rhs})"),
        }
    }

    fn infer_concat_result_type(&mut self, span: Span, lhs_ty: &Ty, rhs_ty: &Ty) -> Ty {
        if lhs_ty.is_unknown() || rhs_ty.is_unknown() {
            return Ty::unknown();
        }
        // Cross-file type aliases (e.g. xlenbits, regidx) cannot be resolved
        // by the local checker. Skip the concat check for any type that isn't
        // explicitly bits(...) or vector(...).
        let is_definitely_concatenable = |t: &Ty| {
            let text = t.display_text();
            text.starts_with("bits(") || text.starts_with("vector(")
        };
        let is_definitely_not_concatenable = |t: &Ty| {
            let text = t.display_text();
            matches!(text.as_str(), "int" | "nat" | "bool" | "string" | "unit" | "real")
        };
        if !is_definitely_concatenable(lhs_ty) && !is_definitely_not_concatenable(lhs_ty) {
            return Ty::unknown();
        }
        if !is_definitely_concatenable(rhs_ty) && !is_definitely_not_concatenable(rhs_ty) {
            return Ty::unknown();
        }

        let Some(lhs) = self.concat_operand_info(lhs_ty) else {
            self.push_error(
                DiagnosticCode::TypeError,
                span,
                TypeError::other(format!(
                    "Cannot concatenate non-vector type {}",
                    lhs_ty.display_text()
                )),
            );
            return Ty::unknown();
        };
        let Some(rhs) = self.concat_operand_info(rhs_ty) else {
            self.push_error(
                DiagnosticCode::TypeError,
                span,
                TypeError::other(format!(
                    "Cannot concatenate non-vector type {}",
                    rhs_ty.display_text()
                )),
            );
            return Ty::unknown();
        };

        let mut subst = Subst::default();
        if !unify(&lhs.elem, &rhs.elem, &mut subst) {
            self.push_error(
                DiagnosticCode::TypeError,
                span,
                TypeError::other(format!(
                    "Cannot concatenate {} with {}",
                    lhs_ty.display_text(),
                    rhs_ty.display_text()
                )),
            );
            return Ty::unknown();
        }

        let elem_ty = apply_subst(&lhs.elem, &subst);
        let width = self.concat_width_text(&lhs.width, &rhs.width);

        if lhs.is_vector && rhs.is_vector {
            vector_ty(width, elem_ty)
        } else {
            bits_ty(width)
        }
    }

    fn infer_concat_expr(&mut self, expr: &Spanned<Expr>, locals: &mut LocalEnv) -> Ty {
        enum Frame<'a> {
            Visit(&'a Spanned<Expr>),
            Reduce(Span),
        }

        let mut stack = vec![Frame::Visit(expr)];
        let mut values = Vec::new();

        while let Some(frame) = stack.pop() {
            match frame {
                Frame::Visit(expr) => match &expr.0 {
                    Expr::Infix { lhs, op, rhs } if op.0 == "@" => {
                        stack.push(Frame::Reduce(expr.1));
                        stack.push(Frame::Visit(rhs));
                        stack.push(Frame::Visit(lhs));
                    }
                    _ => values.push(self.infer_expr(expr, locals)),
                },
                Frame::Reduce(span) => {
                    let rhs_ty = values.pop().unwrap_or(Ty::unknown());
                    let lhs_ty = values.pop().unwrap_or(Ty::unknown());
                    let ty = self.infer_concat_result_type(span, &lhs_ty, &rhs_ty);
                    self.record_expr_type(span, &ty);
                    values.push(ty);
                }
            }
        }

        values.pop().unwrap_or(Ty::unknown())
    }

    fn infer_infix(
        &mut self,
        expr: &Spanned<Expr>,
        lhs: &Spanned<Expr>,
        op: &str,
        rhs: &Spanned<Expr>,
        locals: &mut LocalEnv,
    ) -> Ty {
        if op == "@" {
            return self.infer_concat_expr(expr, locals);
        }

        let lhs_ty = self.infer_expr(lhs, locals);
        let rhs_ty = self.infer_expr(rhs, locals);
        match op {
            "&&" | "||" => {
                for (side_ty, side_span) in [(&lhs_ty, lhs.1), (&rhs_ty, rhs.1)] {
                    let mut subst = Subst::default();
                    if !unify(&Ty::text("bool".to_string()), side_ty, &mut subst) {
                        self.push_error(
                            DiagnosticCode::TypeError,
                            side_span,
                            TypeError::Subtype {
                                lhs: side_ty.display_text(),
                                rhs: "bool".to_string(),
                                constraint: None,
                            },
                        );
                    }
                }
                Ty::text("bool".to_string())
            }
            "==" | "!=" | "<" | ">" | "<=" | ">="
            | "<_u" | ">_u" | "<=_u" | ">=_u"
            | "<_s" | ">_s" | "<=_s" | ">=_s" => {
                let mut subst = Subst::default();
                // Comparisons in Sail allow comparing any two compatible types
                // including bitvectors of polymorphic widths. Be permissive
                // when either side involves Unknown, polymorphic types, or
                // a custom (non-primitive) type alias that the local checker
                // can't fully resolve — Sail allows comparing bit-encodings
                // against named types (e.g. `pmpAddrMatchType_encdec(x) == TOR`
                // where the encoder returns `bits(2)` and TOR is an enum).
                let lhs_text = lhs_ty.display_text();
                let rhs_text = rhs_ty.display_text();
                let primitives = [
                    "int", "nat", "bool", "string", "unit", "real", "bit", "_",
                ];
                let is_primitive_or_collection = |ty: &Ty, text: &str| {
                    primitives.contains(&text)
                        || text.starts_with("bits(")
                        || text.starts_with("vector(")
                        || text.starts_with("list(")
                        || text.starts_with("range(")
                        || text.starts_with("atom(")
                        || text.starts_with("int(")
                        || text.starts_with("nat(")
                        || matches!(ty.kind(), TyData::Tuple(_) | TyData::App { .. })
                };
                let has_polymorphism = lhs_text.contains('\'')
                    || rhs_text.contains('\'')
                    || lhs_ty.is_unknown()
                    || rhs_ty.is_unknown()
                    || (matches!(lhs_ty.kind(), TyData::Text(_))
                        && !is_primitive_or_collection(&lhs_ty, &lhs_text))
                    || (matches!(rhs_ty.kind(), TyData::Text(_))
                        && !is_primitive_or_collection(&rhs_ty, &rhs_text));
                if !has_polymorphism && !unify(&lhs_ty, &rhs_ty, &mut subst) {
                    self.push_error(
                        DiagnosticCode::TypeError,
                        expr.1,
                        TypeError::Subtype {
                            lhs: rhs_ty.display_text(),
                            rhs: lhs_ty.display_text(),
                            constraint: None,
                        },
                    );
                }
                Ty::text("bool".to_string())
            }
            "&" | "|" | "^" => {
                // In Sail `&`, `|`, `^` are heavily overloaded across bool,
                // bits, and integer types. Without full overload resolution
                // we can't reliably pick the result type. Return bool when
                // both operands are clearly bool, otherwise return Unknown
                // to avoid false positives in assert / if conditions.
                let lhs_text = lhs_ty.display_text();
                let rhs_text = rhs_ty.display_text();
                if lhs_text == "bool" && rhs_text == "bool" {
                    Ty::text("bool".to_string())
                } else {
                    Ty::unknown()
                }
            }
            "<<" | ">>" | "<<<" | ">>>" => {
                // Shift operators preserve the lhs type when known.
                if lhs_ty.is_unknown() {
                    Ty::unknown()
                } else {
                    lhs_ty
                }
            }
            "+" | "-" | "*" | "/" => {
                // Sail's arithmetic operators are heavily overloaded:
                // int + int, real + real, bits + bits, range + range, etc.
                // The local checker doesn't know all overloads, so just pick
                // a sensible result type from the operand types. Resolve type
                // aliases (xlenbits → bits(64)) so we can recognize bitvector
                // operands.
                let lhs_resolved = self.env.resolve_alias(&lhs_ty);
                let rhs_resolved = self.env.resolve_alias(&rhs_ty);
                let lhs_text = lhs_resolved.display_text();
                let rhs_text = rhs_resolved.display_text();
                let is_bits = |t: &str| t.starts_with("bits(");
                if is_bits(&lhs_text) {
                    lhs_ty
                } else if is_bits(&rhs_text) {
                    rhs_ty
                } else if lhs_text == "real" || rhs_text == "real" {
                    Ty::text("real".to_string())
                } else if lhs_ty.is_unknown() && rhs_ty.is_unknown() {
                    Ty::unknown()
                } else if lhs_ty.is_unknown() {
                    // One side known, the other unknown — return the known
                    // side (which may be a custom type alias).
                    rhs_ty
                } else if rhs_ty.is_unknown() {
                    lhs_ty
                } else {
                    Ty::text("int".to_string())
                }
            }
            _ => Ty::unknown(),
        }
    }

    fn infer_match_cases(
        &mut self,
        scrutinee_ty: Ty,
        cases: &[Spanned<MatchCase>],
        locals: &mut LocalEnv,
    ) -> Ty {
        let mut case_ty = None;
        for case in cases {
            locals.push_scope();
            self.bind_pattern(&case.0.pattern, Some(scrutinee_ty.clone()), locals);
            if let Some(guard) = &case.0.guard {
                let guard_ty = self.infer_expr(guard, locals);
                let mut subst = Subst::default();
                if !unify(&Ty::text("bool".to_string()), &guard_ty, &mut subst) {
                    self.push_error(
                        DiagnosticCode::TypeError,
                        guard.1,
                        TypeError::Subtype {
                            lhs: guard_ty.display_text(),
                            rhs: "bool".to_string(),
                            constraint: None,
                        },
                    );
                }
                self.add_expr_constraint(locals, guard, true);
            }
            let body_ty = self.infer_expr(&case.0.body, locals);
            locals.pop_scope();
            match &case_ty {
                None => case_ty = Some(body_ty),
                Some(prev_ty) => {
                    // Skip if either side is Unknown — the case may call a
                    // cross-file function or be `exit()` which has unknown type.
                    if prev_ty.is_unknown() {
                        case_ty = Some(body_ty);
                        continue;
                    }
                    if body_ty.is_unknown() {
                        continue;
                    }
                    let mut subst = Subst::default();
                    if !self.unify_with_aliases(prev_ty, &body_ty, &mut subst) {
                        self.push_error(
                            DiagnosticCode::TypeError,
                            case.0.body.1,
                            TypeError::Subtype {
                                lhs: body_ty.display_text(),
                                rhs: prev_ty.display_text(),
                                constraint: None,
                            },
                        );
                    }
                }
            }
        }
        case_ty.unwrap_or(Ty::unknown())
    }

    fn check_match_cases(
        &mut self,
        scrutinee_ty: Ty,
        cases: &[Spanned<MatchCase>],
        expected: &Ty,
        locals: &mut LocalEnv,
    ) -> Ty {

        for case in cases {
            locals.push_scope();
            self.bind_pattern(&case.0.pattern, Some(scrutinee_ty.clone()), locals);
            if let Some(guard) = &case.0.guard {
                let guard_ty = self.infer_expr(guard, locals);
                self.expect_type(guard.1, &guard_ty, &Ty::text("bool".to_string()));
                self.add_expr_constraint(locals, guard, true);
            }
            self.check_expr(&case.0.body, expected, locals);
            locals.pop_scope();
        }
        self.check_match_exhaustiveness(&scrutinee_ty, cases);
        expected.clone()
    }

    /// Run the Maranget-style pattern usefulness check on a `match` and
    /// emit `IncompleteMatch` / `RedundantMatchArm` diagnostics. Pattern
    /// binding has already happened in `check_match_cases`.
    fn check_match_exhaustiveness(
        &mut self,
        scrutinee_ty: &Ty,
        cases: &[Spanned<MatchCase>],
    ) {
        if cases.is_empty() {
            return;
        }
        // Lower scrutinee type into the algorithm's MatchTy. We use the
        // resolved alias so cross-file `xlenbits = bits(64)` etc. don't
        // confuse the constructor lookup.
        let resolved = self.env.resolve_alias(scrutinee_ty);
        let scrutinee_match_ty = ty_to_match_ty(&resolved);

        // Lower the cases.
        let pattern_constants = &self.pattern_constants;
        let has_workspace = self.env.has_workspace_context;
        let lookup = |name: &str| -> bool {
            is_pattern_binding(name, pattern_constants, has_workspace)
        };
        // is_pattern_binding returns true for *binding-y* names. We need
        // the inverse — names that ARE constants.
        let is_constant = |name: &str| -> bool { !lookup(name) };
        let arms = match_check::lower_arms(cases, &is_constant);

        // Build a per-call constructor arity table from local + cross-file
        // constructor schemes. Empty schemes (no params) → arity 0.
        let mut arity_map: HashMap<String, usize> = HashMap::new();
        for (name, schemes) in &self.env.constructors {
            if let Some(scheme) = schemes.first() {
                let arity = match scheme.params.as_slice() {
                    [] => 0,
                    [single] => match single.kind() {
                        TyData::Tuple(items) => items.len(),
                        _ => 1,
                    },
                    many => many.len(),
                };
                arity_map.insert(name.clone(), arity);
            }
        }
        // Cross-file callable arities are recorded as `(min, max)` pairs
        // (Sail union variants accept both flattened and tuple forms).
        // The matrix algorithm wants a single arity per constructor, so
        // we take the larger value — that's the form most patterns use
        // when destructuring.
        for (name, arities) in &self.env.cross_file_function_arity {
            if arity_map.contains_key(name) {
                continue;
            }
            if let Some(&(_, max)) = arities.iter().max_by_key(|(_, max)| *max) {
                arity_map.insert(name.clone(), max);
            }
        }

        let cx = EnvCx {
            enums: &self.env.enums,
            unions: &self.env.unions,
            constructor_arity: &arity_map,
        };
        let report = match_check::compute_match_usefulness(&arms, &scrutinee_match_ty, &cx);

        // Only report when we can name a concrete missing constructor.
        // A witness of just `_` happens whenever the scrutinee type is
        // Unknown (we couldn't classify it) or Unlistable (numeric /
        // string literal universe with no wildcard arm). Either case
        // would generate noise: the former because we don't actually
        // know what's missing, the latter because Sail style commonly
        // uses literal-only matches on int and the user knows the call
        // sites are exhaustive.
        let has_concrete_witness = report
            .missing_witnesses
            .iter()
            .any(|w| !matches!(w, match_check::MatchPat::Wild));
        if has_concrete_witness {
            let anchor_span = cases[0].1;
            let range = tower_lsp::lsp_types::Range::new(
                self.file.source.position_at(anchor_span.start),
                self.file
                    .source
                    .position_at((anchor_span.start + 1).min(anchor_span.end)),
            );
            let missing = report
                .missing_witnesses
                .iter()
                .filter(|w| !matches!(w, match_check::MatchPat::Wild))
                .map(|w| w.display_text())
                .collect::<Vec<_>>()
                .join(", ");
            self.diagnostics.push(Diagnostic::new(
                DiagnosticCode::IncompleteMatch,
                format!("Non-exhaustive match: missing arm(s) for {missing}"),
                range,
                Severity::Warning,
            ));
        }
        // Redundancy reporting is intentionally disabled in this MVP.
        // The matrix algorithm sees `pma :: rest` and `[||]` as two
        // wildcards (we don't model list/struct/vector patterns yet), so
        // the second one looks redundant when it isn't. We'll re-enable
        // this once those pattern shapes are lowered properly.
        let _ = report.redundant;
    }

    fn mapping_call_arg_type(&self, arg_types: &[Ty]) -> Ty {
        match arg_types {
            [] => Ty::text("unit".to_string()),
            [arg] => arg.clone(),
            _ => Ty::tuple(arg_types.to_vec()),
        }
    }

    fn infer_mapping_call(
        &mut self,
        callee_name: &str,
        arg_types: &[Ty],
        expected_ret: Option<&Ty>,
        assumptions: &[ConstraintExpr],
        span: Span,
    ) -> Option<Ty> {
        let mappings = self.env.lookup_mappings(callee_name);
        if mappings.is_empty() {
            return None;
        }

        let actual_arg = self.mapping_call_arg_type(arg_types);
        let mut errors = Vec::new();
        for mapping in mappings {
            let sig = format_mapping_signature(mapping.as_ref());
            let mut forwards_subst = Subst::default();
            if unify(&mapping.lhs, &actual_arg, &mut forwards_subst) {
                let forwards_ret = apply_subst(&mapping.rhs, &forwards_subst);
                if let Some(expected_ret) = expected_ret {
                    if !unify(&forwards_ret, expected_ret, &mut forwards_subst) {
                        errors.push((
                            format!("{callee_name}_forwards"),
                            span,
                            Box::new(TypeError::Subtype {
                                lhs: forwards_ret.display_text(),
                                rhs: expected_ret.display_text(),
                                constraint: None,
                            }),
                        ));
                    } else if let Some(error) = self.instantiation_error_with_sig(
                        callee_name,
                        &mapping.quantifiers,
                        &mapping.constraints,
                        &forwards_subst,
                        assumptions,
                        Some(sig.clone()),
                    ) {
                        errors.push((format!("{callee_name}_forwards"), span, Box::new(error)));
                    } else {
                        return Some(apply_subst(&mapping.rhs, &forwards_subst));
                    }
                } else if let Some(error) = self.instantiation_error_with_sig(
                    callee_name,
                    &mapping.quantifiers,
                    &mapping.constraints,
                    &forwards_subst,
                    assumptions,
                    Some(sig.clone()),
                ) {
                    errors.push((format!("{callee_name}_forwards"), span, Box::new(error)));
                } else {
                    return Some(forwards_ret);
                }
            } else {
                errors.push((
                    format!("{callee_name}_forwards"),
                    span,
                    Box::new(TypeError::Subtype {
                        lhs: actual_arg.display_text(),
                        rhs: mapping.lhs.display_text(),
                        constraint: None,
                    }),
                ));
            }

            let mut backwards_subst = Subst::default();
            if unify(&mapping.rhs, &actual_arg, &mut backwards_subst) {
                let backwards_ret = apply_subst(&mapping.lhs, &backwards_subst);
                if let Some(expected_ret) = expected_ret {
                    if !unify(&backwards_ret, expected_ret, &mut backwards_subst) {
                        errors.push((
                            format!("{callee_name}_backwards"),
                            span,
                            Box::new(TypeError::Subtype {
                                lhs: backwards_ret.display_text(),
                                rhs: expected_ret.display_text(),
                                constraint: None,
                            }),
                        ));
                    } else if let Some(error) = self.instantiation_error_with_sig(
                        callee_name,
                        &mapping.quantifiers,
                        &mapping.constraints,
                        &backwards_subst,
                        assumptions,
                        Some(sig.clone()),
                    ) {
                        errors.push((format!("{callee_name}_backwards"), span, Box::new(error)));
                    } else {
                        return Some(apply_subst(&mapping.lhs, &backwards_subst));
                    }
                } else if let Some(error) = self.instantiation_error_with_sig(
                    callee_name,
                    &mapping.quantifiers,
                    &mapping.constraints,
                    &backwards_subst,
                    assumptions,
                    Some(sig),
                ) {
                    errors.push((format!("{callee_name}_backwards"), span, Box::new(error)));
                } else {
                    return Some(backwards_ret);
                }
            } else {
                errors.push((
                    format!("{callee_name}_backwards"),
                    span,
                    Box::new(TypeError::Subtype {
                        lhs: actual_arg.display_text(),
                        rhs: mapping.rhs.display_text(),
                        constraint: None,
                    }),
                ));
            }
        }

        self.push_error(
            DiagnosticCode::TypeError,
            span,
            TypeError::NoOverloading {
                id: callee_name.to_string(),
                errors,
            },
        );
        Some(Ty::unknown())
    }

    fn check_mapping_body(
        &mut self,
        body: &MappingBody,
        scheme: &MappingScheme,
        locals: &mut LocalEnv,
    ) {
        for arm in &body.arms {
            let (input_ty, output_ty) = match arm.0.direction {
                MappingArmDirection::Bidirectional | MappingArmDirection::Forwards => {
                    (scheme.lhs.clone(), scheme.rhs.clone())
                }
                MappingArmDirection::Backwards => (scheme.rhs.clone(), scheme.lhs.clone()),
            };

            let lhs_bindings = arm
                .0
                .lhs_pattern
                .as_ref()
                .map(|pattern| self.capture_pattern_bindings(pattern, input_ty.clone(), locals))
                .unwrap_or_default();
            let rhs_bindings = if matches!(arm.0.direction, MappingArmDirection::Bidirectional) {
                arm.0
                    .rhs_pattern
                    .as_ref()
                    .map(|pattern| {
                        self.capture_pattern_bindings(pattern, output_ty.clone(), locals)
                    })
                    .unwrap_or_default()
            } else {
                HashMap::new()
            };
            let shared_bindings = self.merge_mapping_bindings(arm.1, &lhs_bindings, &rhs_bindings);

            if matches!(arm.0.direction, MappingArmDirection::Bidirectional) {
                let left_mark = locals.snapshot();
                locals.push_scope();
                self.define_captured_bindings(locals, &rhs_bindings);
                if let Some(pattern) = &arm.0.lhs_pattern {
                    self.bind_pattern(pattern, Some(input_ty.clone()), locals);
                } else {
                    self.check_expr(&arm.0.lhs, &input_ty, locals);
                }
                locals.restore(left_mark);

                let right_mark = locals.snapshot();
                locals.push_scope();
                self.define_captured_bindings(locals, &lhs_bindings);
                if let Some(pattern) = &arm.0.rhs_pattern {
                    self.bind_pattern(pattern, Some(output_ty.clone()), locals);
                } else {
                    self.check_expr(&arm.0.rhs, &output_ty, locals);
                }
                locals.restore(right_mark);

                if let Some(guard) = &arm.0.guard {
                    let guard_mark = locals.snapshot();
                    locals.push_scope();
                    self.define_captured_bindings(locals, &shared_bindings);
                    let guard_ty = self.infer_expr(guard, locals);
                    self.expect_type(guard.1, &guard_ty, &Ty::text("bool".to_string()));
                    self.add_expr_constraint(locals, guard, true);
                    locals.restore(guard_mark);
                }
                continue;
            }

            let arm_mark = locals.snapshot();
            locals.push_scope();
            if let Some(pattern) = &arm.0.lhs_pattern {
                self.bind_pattern(pattern, Some(input_ty.clone()), locals);
            } else {
                self.check_expr(&arm.0.lhs, &input_ty, locals);
            }
            if let Some(guard) = &arm.0.guard {
                let guard_ty = self.infer_expr(guard, locals);
                self.expect_type(guard.1, &guard_ty, &Ty::text("bool".to_string()));
                self.add_expr_constraint(locals, guard, true);
            }
            if let Some(pattern) = &arm.0.rhs_pattern {
                self.bind_pattern(pattern, Some(output_ty), locals);
            } else {
                self.check_expr(&arm.0.rhs, &output_ty, locals);
            }
            locals.restore(arm_mark);
        }
    }

    fn check_mapping_definition(&mut self, def: &sail_parser::core_ast::CallableDefinition) {
        let scheme: Option<Arc<MappingScheme>> = self
            .env
            .mappings
            .get(&def.name.0)
            .and_then(|schemes| schemes.first().cloned())
            .or_else(|| {
                def.signature
                    .as_ref()
                    .and_then(|signature| mapping_from_type_expr(self.source, signature))
                    .map(Arc::new)
            });
        let Some(scheme) = scheme else {
            return;
        };

        let mut locals = LocalEnv::new(None);
        if let Some(body) = &def.mapping_body {
            self.check_mapping_body(body, &scheme, &mut locals);
        }
        for clause in &def.clauses {
            if let Some(body) = &clause.0.mapping_body {
                self.check_mapping_body(body, &scheme, &mut locals);
            }
        }
    }

    fn infer_call(
        &mut self,
        call: &sail_parser::Call,
        locals: &mut LocalEnv,
        expected_ret: Option<&Ty>,
    ) -> Ty {
        let mut injected_receiver = None;
        let callee_name = match &call.callee.0 {
            Expr::Field {
                expr: receiver,
                field,
            } => {
                let receiver_ty = self.infer_expr(receiver, locals);
                injected_receiver = Some((receiver_ty, receiver.1));
                format!("_mod_{}", field.0)
            }
            _ => {
                let Some(name) = expr_symbol(&call.callee) else {
                    self.infer_expr(&call.callee, locals);
                    return Ty::unknown();
                };
                name.to_string()
            }
        };
        if callee_name == "vector_access#" {
            return self.infer_vector_access_builtin_call(call, locals, expected_ret);
        }
        if callee_name == "vector_subrange#" {
            return self.infer_vector_subrange_builtin_call(call, locals, expected_ret);
        }
        if callee_name == "vector_update#" {
            return self.infer_vector_update_builtin_call(call, locals, expected_ret);
        }
        if callee_name == "vector_update_subrange#" {
            return self.infer_vector_update_subrange_builtin_call(call, locals, expected_ret);
        }

        let mut arg_types = call
            .args
            .iter()
            .map(|arg| self.infer_expr(arg, locals))
            .collect::<Vec<_>>();
        let mut arg_spans = call.args.iter().map(|arg| arg.1).collect::<Vec<_>>();
        if let Some((receiver_ty, receiver_span)) = injected_receiver {
            arg_types.insert(0, receiver_ty);
            arg_spans.insert(0, receiver_span);
        }
        let mut assumptions = Vec::new();
        self.fill_assumptions(locals, &mut assumptions);
        if callee_name == "slice" {
            return self.infer_slice_builtin_call(call, &arg_types, locals, expected_ret);
        }
        if let Some(mapping_ty) = self.infer_mapping_call(
            &callee_name,
            &arg_types,
            expected_ret,
            &assumptions,
            call.callee.1,
        ) {
            return mapping_ty;
        }
        let candidates = self.env.lookup_functions(&callee_name);

        // Cross-file arity check (B1, narrow scope). Even when we have
        // no LOCAL candidates AND we'd otherwise bail, we can still use
        // the cached cross-file arity table to catch obvious wrong-arg-
        // count bugs. We do this BEFORE the candidates.is_empty() bail
        // so it covers cross-file calls in files that don't define the
        // function locally.
        let cross_file_known = self.env.cross_file_function_names.contains(&callee_name)
            || self.env.cross_file_constructor_names.contains(&callee_name);
        if cross_file_known {
            let mut arities: SmallVec<[(usize, usize); 8]> = SmallVec::new();
            for c in &candidates {
                let total = c.params.len();
                let required = c
                    .implicit_params
                    .iter()
                    .filter(|implicit| !**implicit)
                    .count();
                arities.push((required, total));
            }
            if let Some(extra) = self.env.cross_file_function_arity.get(&callee_name) {
                arities.extend(extra.iter().copied());
            }
            let arg_count = arg_types.len();
            let lexp_offset = if self.in_lexp_call { 1usize } else { 0 };
            // Accept the call when any known overload's arity matches.
            // In lvalue context (`wX(idx) = data`), Sail's setter
            // desugaring removes the value arg, so the call site has
            // one fewer arg than the underlying signature — accept
            // `arg_count + 1` as well, but only there.
            let any_match = arities.iter().any(|(req, total)| {
                let lexp_candidate = arg_count + lexp_offset;
                (arg_count >= *req && arg_count <= *total)
                    || (lexp_candidate >= *req && lexp_candidate <= *total)
            });
            if !arities.is_empty() && !any_match {
                let (min_req, max_total) = arities.iter().fold(
                    (usize::MAX, 0usize),
                    |(min_req, max_total), (req, total)| {
                        (min_req.min(*req), max_total.max(*total))
                    },
                );
                self.push_error(
                    DiagnosticCode::MismatchedArgCount,
                    call.callee.1,
                    TypeError::other(if min_req == max_total {
                        format!("Expected {} arguments, found {}", max_total, arg_count)
                    } else {
                        format!(
                            "Expected {}-{} arguments, found {}",
                            min_req, max_total, arg_count
                        )
                    }),
                );
            }
            // Cross-file callee — don't try the local candidate
            // matching path; we just return Unknown and let upstream
            // diagnostics carry the day.
            return Ty::unknown();
        }

        if candidates.is_empty() {
            // No scheme available — could be a built-in primop, a Sail
            // standard-library function we don't parse, or a cross-file
            // callable that lacks a `val` declaration. Stay silent —
            // the strict unresolved-identifier check catches the truly
            // unknown case via `Expr::Ident`.
            return Ty::unknown();
        }

        let mut count_mismatch: Option<(usize, usize)> = None;
        let mut candidate_errors = Vec::new();
        for candidate in candidates {
            let required = candidate
                .implicit_params
                .iter()
                .filter(|is_implicit| !**is_implicit)
                .count();
            let total = candidate.params.len();
            if arg_types.len() < required || arg_types.len() > total {
                count_mismatch = Some(match count_mismatch {
                    Some((prev_required, prev_total)) => {
                        (prev_required.min(required), prev_total.max(total))
                    }
                    None => (required, total),
                });
                candidate_errors.push((
                    callee_name.clone(),
                    call.callee.1,
                    Box::new(TypeError::other(format!(
                        "Expected {}{} arguments, found {}",
                        required,
                        if required == total {
                            String::new()
                        } else {
                            format!("-{total}")
                        },
                        arg_types.len()
                    ))),
                ));
                continue;
            }

            let expected_params = if arg_types.len() == total {
                candidate.params.iter().collect::<Vec<_>>()
            } else {
                candidate
                    .params
                    .iter()
                    .zip(candidate.implicit_params.iter())
                    .filter_map(|(param, is_implicit)| (!is_implicit).then_some(param))
                    .collect::<Vec<_>>()
            };
            let mut subst = Subst::default();
            let mut ok = true;
            for (index, (expected, actual)) in
                expected_params.iter().zip(arg_types.iter()).enumerate()
            {
                if !unify(expected, actual, &mut subst) {
                    ok = false;
                    candidate_errors.push((
                        callee_name.clone(),
                        arg_spans[index],
                        Box::new(TypeError::FunctionArg {
                            span: arg_spans[index],
                            ty: expected.display_text(),
                            error: Box::new(TypeError::Subtype {
                                lhs: actual.display_text(),
                                rhs: expected.display_text(),
                                constraint: None,
                            }),
                        }),
                    ));
                    break;
                }
            }
            if ok {
                let ret = apply_subst(&candidate.ret, &subst);
                if let Some(expected_ret) = expected_ret {
                    if !unify(&ret, expected_ret, &mut subst) {
                        candidate_errors.push((
                            callee_name.clone(),
                            call.callee.1,
                            Box::new(TypeError::Subtype {
                                lhs: ret.display_text(),
                                rhs: expected_ret.display_text(),
                                constraint: None,
                            }),
                        ));
                        continue;
                    }
                }
                if let Some(error) = self.instantiation_error_with_sig(
                    &callee_name,
                    &candidate.quantifiers,
                    &candidate.constraints,
                    &subst,
                    &assumptions,
                    Some(format_scheme_signature(candidate.as_ref())),
                ) {
                    candidate_errors.push((callee_name.clone(), call.callee.1, Box::new(error)));
                    continue;
                }
                return apply_subst(&candidate.ret, &subst);
            }
        }

        // For overloaded functions, some variants may live in other files
        // and lack a `val` declaration so we never built a scheme for them.
        // If the call name is registered as an overload AND at least one
        // member has no scheme in the env, we can't reliably determine
        // arg-count mismatch — stay silent to avoid false positives.
        let is_partial_overload = self
            .env
            .overloads
            .get(&callee_name)
            .map(|members| {
                members
                    .iter()
                    .any(|m| !self.env.functions.contains_key(m))
            })
            .unwrap_or(false);

        // If any argument type is Unknown (typically from a cross-file call),
        // we can't reliably check overload resolution or quantifier
        // instantiation — suppress candidate errors to avoid false positives.
        let has_unknown_arg = arg_types.iter().any(|t| t.is_unknown());
        if has_unknown_arg {
            return Ty::unknown();
        }

        if let Some((expected, actual)) = count_mismatch {
            if !is_partial_overload {
                self.push_error(
                    DiagnosticCode::MismatchedArgCount,
                    call.callee.1,
                    TypeError::other(if expected == actual {
                        format!("Expected {} arguments, found {}", actual, arg_types.len())
                    } else {
                        format!(
                            "Expected {}-{} arguments, found {}",
                            expected,
                            actual,
                            arg_types.len()
                        )
                    }),
                );
            }
        } else if !is_partial_overload {
            self.push_error(
                DiagnosticCode::TypeError,
                call.callee.1,
                TypeError::NoOverloading {
                    id: callee_name,
                    errors: candidate_errors,
                },
            );
        }
        Ty::unknown()
    }
}

fn infer_collection_type(
    checker: &mut Checker<'_>,
    items: &[Spanned<Expr>],
    locals: &mut LocalEnv,
    name: &str,
) -> Ty {
    let mut item_ty = None;
    for item in items {
        let ty = checker.infer_expr(item, locals);
        if let Some(prev) = &item_ty {
            let mut subst = Subst::default();
            if !unify(prev, &ty, &mut subst) {
                return Ty::unknown();
            }
        } else {
            item_ty = Some(ty);
        }
    }
    let elem = item_ty.unwrap_or(Ty::unknown());
    match name {
        "vector" => vector_ty(items.len(), elem),
        "list" => {
            let text = format!("{name}({})", elem.display_text());
            Ty::app(name, vec![TyArg::Type(elem)], text)
        }
        _ => {
            let text = format!("{name}({})", elem.display_text());
            Ty::app(name, vec![TyArg::Type(elem)], text)
        }
    }
}

fn expr_symbol(expr: &Spanned<Expr>) -> Option<&str> {
    match &expr.0 {
        Expr::Ident(name) => Some(name.as_str()),
        Expr::Field { field, .. } => Some(field.0.as_str()),
        _ => None,
    }
}

fn build_env_from_files<'a, I>(files: I) -> TopLevelEnv
where
    I: IntoIterator<Item = &'a File>,
{
    let mut env = TopLevelEnv::default();
    for file in files {
        let Some(ast) = file.core_ast() else {
            continue;
        };
        let (mut file_env, _) = TopLevelEnv::from_ast(file.source.text(), ast);
        apply_callable_signature_metadata(file, &mut file_env);
        for (name, schemes) in file_env.functions {
            env.functions.entry(name).or_default().extend(schemes);
        }
        for (name, schemes) in file_env.mappings {
            env.mappings.entry(name).or_default().extend(schemes);
        }
        for (name, members) in file_env.overloads {
            env.overloads.entry(name).or_default().extend(members);
        }
        env.values.extend(file_env.values);
        env.registers.extend(file_env.registers);
        env.records.extend(file_env.records);
        env.bitfields.extend(file_env.bitfields);
        env.type_aliases.extend(file_env.type_aliases);
        env.global_constraints.extend(file_env.global_constraints);
        for (name, schemes) in file_env.constructors {
            env.constructors.entry(name).or_default().extend(schemes);
        }
    }
    env
}

pub(crate) fn check_file(file: &File) -> Option<TypeCheckResult> {
    let ast = file.core_ast()?;
    let (mut env, pattern_constants) = TopLevelEnv::from_ast(file.source.text(), ast);
    apply_callable_signature_metadata(file, &mut env);
    Some(Checker::new(file, env, pattern_constants).check_source_file(ast))
}

/// Cross-file aggregation result. Computed once per workspace fingerprint
/// and shared between every `check_file_with_workspace` call that sees the
/// same set of file content hashes. Without this cache, every per-file
/// typecheck would walk every workspace file's `core_ast.defs` from
/// scratch — O(N²) per workspace recompute pass.
#[derive(Clone, Debug, Default)]
pub(crate) struct WorkspaceContext {
    type_aliases: HashMap<String, Ty>,
    overloads: HashMap<String, Vec<String>>,
    known_field_names: HashSet<String>,
    cross_file_function_names: HashSet<String>,
    cross_file_constructor_names: HashSet<String>,
    cross_file_value_names: HashSet<String>,
    cross_file_register_names: HashSet<String>,
    /// Pattern constants contributed by cross-file enums/unions/scattered
    /// enum clauses. Merged into the per-file `pattern_constants` set
    /// during typechecking.
    cross_file_pattern_constants: HashSet<String>,
    /// Function schemes from `val f : ...` declarations in other files,
    /// merged into the local env by `apply_to` so `infer_call` can do
    /// real arity / argument-type checking on cross-file calls.
    cross_file_function_schemes: HashMap<String, Vec<Arc<TypeScheme>>>,
    /// Constructor schemes from union variants in other files, used by
    /// the same path so `Some(x, y)` calling a single-arg constructor
    /// gets a real arity-mismatch diagnostic instead of silence.
    cross_file_constructor_schemes: HashMap<String, Vec<Arc<TypeScheme>>>,
    /// Type-name → enum member list, aggregated across all workspace
    /// files. The pattern-exhaustiveness check uses this to enumerate
    /// constructors for cross-file enum types so it can report missing
    /// arms even when the enum is defined in a different file.
    enums: HashMap<String, Vec<String>>,
    /// Type-name → union variant list, aggregated across all workspace
    /// files. Same role as `enums` but for union types.
    unions: HashMap<String, Vec<String>>,
}

impl WorkspaceContext {
    fn build<'a>(files: impl IntoIterator<Item = &'a File>) -> Self {
        let mut ctx = WorkspaceContext::default();
        for f in files {
            let Some(other_ast) = f.core_ast() else { continue };
            let other_source = f.source.text();
            for (item, _) in &other_ast.defs {
                match &item.kind {
                    DefinitionKind::TypeAlias(def) => {
                        if let Some(target) = &def.target {
                            let underlying = type_from_type_expr(other_source, target);
                            ctx.type_aliases
                                .entry(def.name.0.clone())
                                .or_insert(underlying);
                        }
                    }
                    DefinitionKind::CallableSpec(spec) => {
                        ctx.cross_file_function_names.insert(spec.name.0.clone());
                        // Only `val ... -> ...` specs are reliable enough to
                        // share across files. We skip `mapping` specs here
                        // since mapping schemes have a different shape that
                        // the call-site checker doesn't yet understand
                        // bidirectionally.
                        if !matches!(spec.kind, sail_parser::CallableSpecKind::Mapping) {
                            let scheme =
                                Arc::new(scheme_from_type_expr(other_source, &spec.signature));
                            ctx.cross_file_function_schemes
                                .entry(spec.name.0.clone())
                                .or_default()
                                .push(scheme);
                        }
                    }
                    DefinitionKind::Callable(def) => {
                        ctx.cross_file_function_names.insert(def.name.0.clone());
                    }
                    DefinitionKind::Named(def) => match def.kind {
                        NamedDefKind::Enum => {
                            let entry = ctx.enums.entry(def.name.0.clone()).or_default();
                            for member in &def.members {
                                ctx.cross_file_pattern_constants.insert(member.0.clone());
                                ctx.cross_file_value_names.insert(member.0.clone());
                                if !entry.contains(&member.0) {
                                    entry.push(member.0.clone());
                                }
                            }
                            if let Some(NamedDefDetail::Enum { members, .. }) = &def.detail {
                                for m in members {
                                    ctx.cross_file_pattern_constants
                                        .insert(m.0.name.0.clone());
                                    ctx.cross_file_value_names.insert(m.0.name.0.clone());
                                    if !entry.contains(&m.0.name.0) {
                                        entry.push(m.0.name.0.clone());
                                    }
                                }
                            }
                        }
                        NamedDefKind::Union => {
                            if let Some(NamedDefDetail::Union { variants }) = &def.detail {
                                let entry =
                                    ctx.unions.entry(def.name.0.clone()).or_default();
                                for v in variants {
                                    if !entry.contains(&v.0.name.0) {
                                        entry.push(v.0.name.0.clone());
                                    }
                                }
                            }
                            if let Some(NamedDefDetail::Union { variants }) = &def.detail {
                                for v in variants {
                                    ctx.cross_file_constructor_names
                                        .insert(v.0.name.0.clone());
                                    // Build a real scheme from the variant
                                    // signature so cross-file `Some(x)` etc.
                                    // can be arity / arg-type checked.
                                    let scheme =
                                        scheme_from_union_variant(other_source, def, &v.0);
                                    ctx.cross_file_constructor_schemes
                                        .entry(v.0.name.0.clone())
                                        .or_default()
                                        .push(Arc::new(scheme));
                                }
                            }
                        }
                        NamedDefKind::Register => {
                            ctx.cross_file_register_names.insert(def.name.0.clone());
                            ctx.cross_file_value_names.insert(def.name.0.clone());
                        }
                        NamedDefKind::Let | NamedDefKind::Var => {
                            ctx.cross_file_value_names.insert(def.name.0.clone());
                        }
                        NamedDefKind::Struct => {
                            if let Some(NamedDefDetail::Struct { fields }) = &def.detail {
                                for field in fields {
                                    ctx.known_field_names.insert(field.0.name.0.clone());
                                }
                            }
                        }
                        NamedDefKind::Bitfield => {
                            if let Some(NamedDefDetail::Bitfield { fields }) = &def.detail {
                                for field in fields {
                                    ctx.known_field_names.insert(field.0.name.0.clone());
                                }
                            }
                        }
                        NamedDefKind::Overload => {
                            let entry = ctx.overloads.entry(def.name.0.clone()).or_default();
                            for m in &def.members {
                                if !entry.contains(&m.0) {
                                    entry.push(m.0.clone());
                                }
                            }
                            ctx.cross_file_function_names.insert(def.name.0.clone());
                        }
                        _ => {}
                    },
                    DefinitionKind::ScatteredClause(def)
                        if matches!(def.kind, sail_parser::ScatteredClauseKind::Enum) =>
                    {
                        ctx.cross_file_pattern_constants
                            .insert(def.member.0.clone());
                        ctx.cross_file_value_names.insert(def.member.0.clone());
                        let entry = ctx.enums.entry(def.name.0.clone()).or_default();
                        if !entry.contains(&def.member.0) {
                            entry.push(def.member.0.clone());
                        }
                    }
                    _ => {}
                }
            }
        }
        ctx
    }

    /// Apply this cached aggregation to a freshly built per-file env.
    /// Merges cross-file `val`-derived function schemes and union variant
    /// constructor schemes into the local env so `infer_call` can do real
    /// arity / argument-type checking on cross-file calls. The unifier
    /// (with depth limit + chain compression in `apply_subst`) is now
    /// safe against the recursion blow-ups that defeated the first try.
    fn apply_to(&self, env: &mut TopLevelEnv, pattern_constants: &mut HashSet<String>) {
        // Type aliases: merge but don't overwrite local definitions.
        for (name, ty) in &self.type_aliases {
            env.type_aliases
                .entry(name.clone())
                .or_insert_with(|| ty.clone());
        }
        // Overloads: union, preserving existing entries.
        for (name, members) in &self.overloads {
            let entry = env.overloads.entry(name.clone()).or_default();
            for m in members {
                if !entry.contains(m) {
                    entry.push(m.clone());
                }
            }
        }
        // Known field names: union.
        env.known_field_names
            .extend(self.known_field_names.iter().cloned());
        // Cross-file name sets: replace.
        env.cross_file_function_names = self.cross_file_function_names.clone();
        env.cross_file_constructor_names = self.cross_file_constructor_names.clone();
        env.cross_file_value_names = self.cross_file_value_names.clone();
        env.cross_file_register_names = self.cross_file_register_names.clone();
        // Enums / unions: union with locally-defined entries.
        for (name, members) in &self.enums {
            let entry = env.enums.entry(name.clone()).or_default();
            for m in members {
                if !entry.contains(m) {
                    entry.push(m.clone());
                }
            }
        }
        for (name, variants) in &self.unions {
            let entry = env.unions.entry(name.clone()).or_default();
            for v in variants {
                if !entry.contains(v) {
                    entry.push(v.clone());
                }
            }
        }
        // B1 (cross-file scheme merging) is intentionally NOT done via
        // `env.functions`/`env.constructors`. Doing so causes the unifier
        // to recurse pathologically when a cross-file scheme contains
        // quantified `forall 'n` types — even with a unify depth limit,
        // the recursion blow-up was reproducible on the sail-riscv
        // corpus and ate the 64 MiB worker stack.
        //
        // Instead we expose the cross-file schemes via dedicated arity-
        // check sets (see `cross_file_function_arity` /
        // `cross_file_constructor_arity` below). The arity check is
        // sound and safe — it only counts params, never invokes the
        // unifier on a quantified type.
        for (name, schemes) in &self.cross_file_function_schemes {
            let arities: Vec<(usize, usize)> = schemes
                .iter()
                .flat_map(|s| {
                    let total = s.params.len();
                    let required = s
                        .implicit_params
                        .iter()
                        .filter(|implicit| !**implicit)
                        .count();
                    let mut variants = vec![(required, total)];
                    // Sail allows calling `(A, B) -> C` either with one
                    // tuple arg or two flattened args. Accept both.
                    if s.params.len() == 1 {
                        if let TyData::Tuple(items) = s.params[0].kind() {
                            variants.push((items.len(), items.len()));
                        }
                    }
                    variants
                })
                .collect();
            env.cross_file_function_arity
                .entry(name.clone())
                .or_default()
                .extend(arities);
        }
        for (name, schemes) in &self.cross_file_constructor_schemes {
            // Sail union variants are typically declared with a single
            // tuple-typed param (e.g. `Step_Execute : (ExecutionResult,
            // instbits)`), but the call site can pass either one tuple
            // OR the flattened element list. Record BOTH arities so the
            // check accepts either form.
            let arities: Vec<(usize, usize)> = schemes
                .iter()
                .flat_map(|s| {
                    let mut variants = vec![(s.params.len(), s.params.len())];
                    if s.params.len() == 1 {
                        if let TyData::Tuple(items) = s.params[0].kind() {
                            variants.push((items.len(), items.len()));
                        }
                    }
                    variants
                })
                .collect();
            env.cross_file_function_arity
                .entry(name.clone())
                .or_default()
                .extend(arities);
        }
        // Pattern constants: union with cross-file contributions.
        pattern_constants.extend(self.cross_file_pattern_constants.iter().cloned());
        pattern_constants.extend(self.cross_file_constructor_names.iter().cloned());
    }
}

/// Process-global cache for the most recent `WorkspaceContext`. Keyed by
/// a fingerprint over the participating files' content hashes (sorted to
/// be order-independent). Workspace recompute storms (e.g. the
/// "rerun every open file after the disk scan finished" pass) get a
/// single aggregation pass instead of one per file.
struct WorkspaceContextCache {
    fingerprint: u64,
    ctx: Arc<WorkspaceContext>,
}

static WORKSPACE_CONTEXT_CACHE: OnceLock<Mutex<Option<WorkspaceContextCache>>> = OnceLock::new();

fn workspace_context_cache() -> &'static Mutex<Option<WorkspaceContextCache>> {
    WORKSPACE_CONTEXT_CACHE.get_or_init(|| Mutex::new(None))
}

/// Per-file inference cache. Maps `(file content hash, workspace
/// fingerprint)` → cached `TypeCheckResult`. The fingerprint guards
/// against stale results when the workspace exports change; the file
/// hash guards against stale results when the body changes.
///
/// This is the lightweight analogue of salsa's per-function `infer_query`
/// memoization (rust-analyzer's `InferenceResult::for_body`). It pays off
/// most when the worker re-runs typechecks for files that haven't
/// actually changed (e.g. the post-scan "refresh all open files" pass,
/// or reverse-dependency reschedules where the dependent file wasn't
/// itself edited).
///
/// Bounded at 256 entries with FIFO eviction so a long-running session
/// doesn't accumulate stale memory. Even at 256 sail-riscv files this
/// fits comfortably in memory because each cached `TypeCheckResult` is
/// already Arc-shared.
struct InferenceCacheEntry {
    file_hash: u64,
    workspace_fp: u64,
    workspace_complete: bool,
    result: Arc<TypeCheckResult>,
}

const INFERENCE_CACHE_CAPACITY: usize = 256;

static INFERENCE_CACHE: OnceLock<Mutex<Vec<InferenceCacheEntry>>> = OnceLock::new();

fn inference_cache() -> &'static Mutex<Vec<InferenceCacheEntry>> {
    INFERENCE_CACHE.get_or_init(|| Mutex::new(Vec::new()))
}

fn inference_cache_lookup(
    file_hash: u64,
    workspace_fp: u64,
    workspace_complete: bool,
) -> Option<Arc<TypeCheckResult>> {
    let cache = inference_cache().lock().unwrap();
    cache
        .iter()
        .rev()
        .find(|e| {
            e.file_hash == file_hash
                && e.workspace_fp == workspace_fp
                && e.workspace_complete == workspace_complete
        })
        .map(|e| e.result.clone())
}

fn inference_cache_store(
    file_hash: u64,
    workspace_fp: u64,
    workspace_complete: bool,
    result: Arc<TypeCheckResult>,
) {
    let mut cache = inference_cache().lock().unwrap();
    // Evict any prior entry for the same file (different workspace fp or
    // completeness flag) so the cache stays bounded under typical
    // "user keeps editing one file" workloads.
    cache.retain(|e| e.file_hash != file_hash);
    cache.push(InferenceCacheEntry {
        file_hash,
        workspace_fp,
        workspace_complete,
        result,
    });
    if cache.len() > INFERENCE_CACHE_CAPACITY {
        let drop_count = cache.len() - INFERENCE_CACHE_CAPACITY;
        cache.drain(0..drop_count);
    }
}

/// Order-independent fingerprint over the file content hashes. Two
/// snapshots with the same set of files (regardless of iteration order)
/// produce the same fingerprint.
fn fingerprint_files<'a>(files: impl IntoIterator<Item = &'a File>) -> u64 {
    let mut hashes: Vec<u64> = files.into_iter().map(|f| f.content_hash()).collect();
    hashes.sort_unstable();
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    hashes.hash(&mut hasher);
    hasher.finish()
}

/// Look up — and on miss build + memoize — the cached `WorkspaceContext`
/// for `files`. The cache holds a single slot, which is enough for the
/// typical "one workspace per process" use case.
fn cached_workspace_context<'a, I>(files: I) -> Arc<WorkspaceContext>
where
    I: IntoIterator<Item = &'a File> + Clone,
{
    let fp = fingerprint_files(files.clone());
    let cell = workspace_context_cache();
    {
        let guard = cell.lock().unwrap();
        if let Some(slot) = guard.as_ref() {
            if slot.fingerprint == fp {
                return slot.ctx.clone();
            }
        }
    }
    let ctx = Arc::new(WorkspaceContext::build(files));
    let mut guard = cell.lock().unwrap();
    *guard = Some(WorkspaceContextCache {
        fingerprint: fp,
        ctx: ctx.clone(),
    });
    ctx
}

/// Type-check a file with selective cross-file context. We deliberately
/// merge ONLY data that is safe and unambiguous:
///   - Type aliases (so `xlenbits` resolves to `bits(64)`)
///   - Pattern-constant names (so `mRET`, `Data`, `ShadowStack` aren't
///     treated as new bindings or duplicate bindings)
///   - Cross-file function/overload NAME existence (consulted via a
///     `cross_file_function_names` set so `is_partial_overload` and
///     "function not found" suppression work without merging full schemes)
///
/// We deliberately do NOT merge:
///   - Function schemes from other files (deep unification recursion)
///   - Constructor schemes from other files (arity mismatch false positives)
///   - Enum/union variant lists (pattern completeness false positives —
///     since the cross-file enums often have many variants the local file
///     legitimately doesn't need to handle)
pub(crate) fn check_file_with_workspace<'a, I>(
    file: &File,
    all_files: I,
    workspace_complete: bool,
    cancel: CancellationToken,
) -> Option<TypeCheckResult>
where
    I: IntoIterator<Item = &'a File> + Clone,
{
    let ast = file.core_ast()?;

    // C2: per-file inference cache. Try to reuse a previous result for
    // the same (file content, workspace exports) combination. This pays
    // off when the worker re-runs typechecks for files that didn't
    // actually change — most commonly the post-scan refresh of every
    // open file, and reverse-dependency reschedules where the dependent
    // file's body wasn't itself edited.
    let workspace_fp = fingerprint_files(all_files.clone());
    let file_hash = file.content_hash();
    if file_hash != 0 {
        if let Some(cached) =
            inference_cache_lookup(file_hash, workspace_fp, workspace_complete)
        {
            // Cache hits don't need to honour cancellation — we're
            // returning instantly anyway.
            return Some((*cached).clone());
        }
    }

    // Start from the local file env.
    let (mut env, mut pattern_constants) =
        TopLevelEnv::from_ast(file.source.text(), ast);
    apply_callable_signature_metadata(file, &mut env);

    // Look up (or build) the cached cross-file aggregation. The same
    // workspace fingerprint hits the cache; the heavy `WorkspaceContext`
    // build only runs when the file set or any file's content changes.
    let workspace_ctx = cached_workspace_context(all_files);
    workspace_ctx.apply_to(&mut env, &mut pattern_constants);

    // Add own constructors to pattern_constants (so they aren't bindings).
    for name in env.constructors.keys() {
        pattern_constants.insert(name.clone());
    }

    // Only enable the strict unresolved-identifier check if the caller
    // confirmed the snapshot represents the full workspace. Otherwise
    // (e.g. during the race window before the disk scan completes) we'd
    // flag every cross-file reference as unresolved.
    env.has_workspace_context = workspace_complete;

    let result = Checker::with_cancel(file, env, pattern_constants, cancel.clone())
        .check_source_file(ast);

    // Only cache complete results — partial output from a cancelled
    // checker would otherwise poison subsequent lookups.
    if !cancel.is_cancelled() && file_hash != 0 {
        inference_cache_store(
            file_hash,
            workspace_fp,
            workspace_complete,
            Arc::new(result.clone()),
        );
    }
    Some(result)
}

pub(crate) fn infer_expr_type_text_in_files<'a, I>(
    files: I,
    current_file: &File,
    expr: &Spanned<Expr>,
) -> Option<String>
where
    I: IntoIterator<Item = &'a File>,
{
    if let Some(result) = current_file.type_check() {
        if let Some(ty) = result.expr_type_text(expr.1) {
            return Some(ty.to_string());
        }
    }

    let env = build_env_from_files(files);
    let pattern_constants = current_file
        .core_ast()
        .map(|ast| TopLevelEnv::from_ast(current_file.source.text(), ast).1)
        .unwrap_or_default();
    let mut checker = Checker::new(current_file, env, pattern_constants);
    let mut locals = LocalEnv::new(None);
    let ty = checker.infer_expr(expr, &mut locals);
    if ty.is_unknown() {
        None
    } else {
        Some(ty.display_text())
    }
}

#[cfg(test)]
mod c1_intern_tests {
    use super::*;

    #[test]
    fn primitive_text_types_share_arcs() {
        let a = Ty::text("int");
        let b = Ty::text("int");
        // Both calls go through the intern pool, so they share the
        // same `Arc<TyData>` instance — equality is a pointer compare.
        assert!(Arc::ptr_eq(&a.0, &b.0));
        assert_eq!(a, b);
    }

    #[test]
    fn unknown_is_interned() {
        let a = Ty::unknown();
        let b = Ty::unknown();
        assert!(Arc::ptr_eq(&a.0, &b.0));
    }

    #[test]
    fn non_primitive_text_is_not_interned() {
        let a = Ty::text("Minterrupts");
        let b = Ty::text("Minterrupts");
        // Custom names go through `Arc::new` each time. They still
        // compare equal structurally — just not via pointer-equality.
        assert!(!Arc::ptr_eq(&a.0, &b.0));
        assert_eq!(a, b);
    }

    #[test]
    fn nested_clone_is_cheap() {
        // Building a deep type and cloning it should bump exactly one
        // refcount on the outer Arc — no recursion into the inner data.
        let inner = Ty::tuple(vec![Ty::text("int"), Ty::text("bool")]);
        let outer = Ty::function(vec![inner.clone(), Ty::text("unit")], Ty::text("int"));
        let cloned = outer.clone();
        assert!(Arc::ptr_eq(&outer.0, &cloned.0));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unify_value_skips_self_bindings() {
        let mut subst = Subst::default();
        assert!(unify_value("'n", "'n", &mut subst));
        assert!(subst.values.is_empty());
    }

    #[test]
    fn subst_numeric_expr_handles_self_referential_value_bindings() {
        let mut subst = Subst::default();
        subst.values.insert("'n".to_string(), "'n".to_string());
        assert_eq!(
            subst_numeric_expr(&NumericExpr::Var("'n".to_string()), &subst),
            NumericExpr::Var("'n".to_string())
        );
    }
}
