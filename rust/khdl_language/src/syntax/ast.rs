use crate::syntax::parser::RecoveredParseError;
use crate::syntax::pos::{HasSpan, Pos, Span, Spanned};
use crate::syntax::source::SourceDatabase;
use crate::syntax::token::TokenType;
use crate::util::arena::Arena;
use crate::{impl_has_span, new_index_type};
use itertools::Itertools;

new_index_type!(pub ExpressionKindIndex);

#[derive(Debug)]
pub struct FileContent {
    pub span: Span,
    pub items: Vec<Item>,

    pub arena_expressions: ArenaExpressions,
}

pub type ArenaExpressions = Arena<ExpressionKindIndex, ExpressionKind>;

#[derive(Debug, Copy, Clone)]
pub enum Visibility<S = Span> {
    Public { span: S },
    Private,
}

// TODO add "doc comment" field to items?
// TODO rename to ItemDef or maybe FileItem
#[derive(Debug, Clone)]
pub enum Item {
    // non-declaring items
    Import(ItemImport),
    // common declarations that are allowed anywhere
    CommonDeclaration(Spanned<CommonDeclaration<Visibility>>),
    // declarations that are only allowed top-level
    // TODO turn all of these into common declarations, even the imports
    ModuleInternal(ItemDefModuleInternal),
    ModuleExternal(ItemDefModuleExternal),
    Interface(ItemDefInterface),
}

// TODO rename, not all of these are actually declarations
#[derive(Debug, Clone)]
pub enum CommonDeclaration<V> {
    Named(CommonDeclarationNamed<V>),
    ConstBlock(ConstBlock),
}

#[derive(Debug, Clone)]
pub struct CommonDeclarationNamed<V> {
    pub vis: V,
    pub kind: CommonDeclarationNamedKind,
}

#[derive(Debug, Clone)]
pub enum CommonDeclarationNamedKind {
    Type(TypeDeclaration),
    Const(ConstDeclaration),
    Struct(StructDeclaration),
    Enum(EnumDeclaration),
    Function(FunctionDeclaration),
}

#[derive(Debug, Clone)]
pub struct ConstBlock {
    pub span_keyword: Span,
    pub block: Block<BlockStatement>,
}

#[derive(Debug, Clone)]
pub struct ItemImport {
    pub span: Span,
    pub steps: Spanned<Vec<SimpleIdentifier>>,
    pub final_: Spanned<ImportFinalKind>,
}

#[derive(Debug, Clone)]
pub enum ImportFinalKind {
    Single(ImportEntry),
    Multi(Vec<ImportEntry>),
}

#[derive(Debug, Clone)]
pub struct ImportEntry {
    pub span: Span,
    pub id: SimpleIdentifier,
    pub as_: Option<MaybeSimpleIdentifier>,
}

#[derive(Debug, Clone)]
pub struct StructDeclaration {
    pub span: Span,
    pub span_body: Span,
    pub id: MaybeIdentifier,
    pub params: Option<Parameters>,
    pub items: ExtraList<StructBodyItem>,
}

#[derive(Debug, Clone)]
pub enum StructBodyItem {
    Field(StructField),
    Method(FunctionDeclaration<ParameterSelf>),
}

#[derive(Debug, Clone)]
pub struct StructField {
    pub span: Span,
    pub ref_: Option<Span>,
    pub id: Identifier,
    pub ty: Expression,
}

#[derive(Debug, Clone)]
pub struct EnumDeclaration {
    pub span: Span,
    pub id: MaybeIdentifier,
    pub params: Option<Parameters>,
    pub items: ExtraList<EnumBodyItem>,
}

#[derive(Debug, Clone)]
pub enum EnumBodyItem {
    Variant(EnumVariant),
    Method(FunctionDeclaration<ParameterSelf>),
}

#[derive(Debug, Clone)]
pub struct EnumVariant {
    pub span: Span,
    pub id: SimpleIdentifier,
    pub payload: Option<Expression>,
}

#[derive(Debug, Clone)]
pub struct FunctionDeclaration<S = ()> {
    pub span: Span,
    pub id: MaybeIdentifier,
    pub params: Parameters<S>,
    pub ret_ty: Option<Expression>,
    pub body: Block<BlockStatement>,
}

#[derive(Debug, Clone)]
pub struct ItemDefModuleInternal {
    pub span: Span,
    pub vis: Visibility,
    pub id: MaybeIdentifier,
    pub params: Option<Parameters>,
    pub ports: Spanned<ExtraList<ModulePortItem>>,
    pub body: Spanned<ExtraList<ModuleStatement>>,
}

#[derive(Debug, Clone)]
pub struct ItemDefModuleExternal {
    pub span: Span,
    pub vis: Visibility,
    pub span_ext: Span,
    pub id: SimpleIdentifier,
    pub params: Option<Parameters>,
    pub ports: Spanned<ExtraList<ModulePortItem>>,
}

#[derive(Debug, Clone)]
pub struct ItemDefInterface {
    pub span: Span,
    pub vis: Visibility,
    pub id: MaybeIdentifier,
    pub params: Option<Parameters>,
    pub span_body: Span,
    pub body: ExtraList<InterfaceListItem>,
}

#[derive(Debug, Clone)]
pub enum InterfaceListItem {
    Signal(InterfaceSignal),
    View(InterfaceView),
}

#[derive(Debug, Copy, Clone)]
pub struct InterfaceSignal {
    pub id: Identifier,
    pub ty: Expression,
}

#[derive(Debug, Clone)]
pub struct InterfaceView {
    pub span: Span,
    pub id: MaybeIdentifier,
    pub port_dirs: ExtraList<(Identifier, Spanned<PortDirection>)>,
}

#[derive(Debug, Clone)]
pub struct Parameters<S = ()> {
    pub span: Span,
    pub slf: S,
    pub items: ExtraList<Parameter>,
}

pub type ParameterSelf = Spanned<ParameterSelfKind>;

#[derive(Debug, Copy, Clone)]
pub enum ParameterSelfKind {
    Slf,
    RefSlf,
}

#[derive(Debug, Clone)]
pub struct Parameter {
    pub span: Span,
    pub id: Identifier,
    pub ty: Expression,
    pub default: Option<Expression>,
}

/// A list of (often comma separated) items which also allows inline declarations and conditional branches.
/// This adds a lot of flexibility to port lists, function parameters, module statements and similar constructs.
#[derive(Debug, Clone)]
pub struct ExtraList<T> {
    pub span: Span,
    pub items: Vec<ExtraListItem<T>>,
}

#[derive(Debug, Clone)]
pub struct ExtraListBlock<T> {
    pub span: Span,
    pub items: Vec<ExtraListItem<T>>,
}

#[derive(Debug, Clone)]
pub enum ExtraListItem<T> {
    // leaf node
    Leaf(T),
    // common declaration
    Declaration(CommonDeclaration<()>),

    // control flow
    If(IfStatement<ExtraListBlock<T>>),
    Match(MatchStatement<ExtraListBlock<T>>),
    For(ForStatement<ExtraListBlock<T>>),
}

impl<T> ExtraList<T> {
    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    pub fn for_each_leaf(&self, f: &mut impl FnMut(&T)) {
        fn visit_items<T>(items: &[ExtraListItem<T>], f: &mut impl FnMut(&T)) {
            for item in items {
                match item {
                    ExtraListItem::Leaf(item) => f(item),
                    ExtraListItem::Declaration(_) => {}
                    ExtraListItem::If(stmt) => {
                        let IfStatement {
                            span: _,
                            initial_if,
                            else_ifs,
                            final_else,
                        } = stmt;
                        let mut visit_pair = |pair: &IfCondBlockPair<ExtraListBlock<T>>| {
                            let IfCondBlockPair {
                                span: _,
                                span_if: _,
                                cond: _,
                                block,
                            } = pair;
                            visit_block(block, f)
                        };
                        visit_pair(initial_if);
                        for else_if in else_ifs {
                            visit_pair(else_if);
                        }
                        if let Some(final_else) = final_else {
                            visit_block(final_else, f);
                        }
                    }
                    ExtraListItem::Match(stmt) => {
                        let MatchStatement {
                            span_keyword: _,
                            target: _,
                            branches,
                            pos_end: _,
                        } = stmt;
                        for branch in branches {
                            let MatchBranch { pattern: _, block } = branch;
                            visit_block(block, f);
                        }
                    }
                    ExtraListItem::For(stmt) => {
                        let ForStatement {
                            span_keyword: _,
                            index: _,
                            index_ty: _,
                            iter: _,
                            body,
                        } = stmt;
                        visit_block(body, f);
                    }
                }
            }
        }
        fn visit_block<T>(block: &ExtraListBlock<T>, f: &mut impl FnMut(&T)) {
            let ExtraListBlock { span: _, items } = block;
            visit_items(items, f)
        }

        let ExtraList { span: _, items } = self;
        visit_items(items, f)
    }
}

#[derive(Debug, Clone)]
pub enum ModulePortItem {
    Single(ModulePortSingle),
    DomainBlock(ModulePortDomainBlock),
}

#[derive(Debug, Clone)]
pub struct ModulePortSingle {
    pub span: Span,
    pub id: Identifier,
    pub kind: ModulePortSingleKind,
}

#[derive(Debug, Clone)]
pub struct ModulePortDomainBlock {
    pub span: Span,
    pub domain: Spanned<DomainKind<Expression>>,
    pub ports: ExtraListBlock<ModulePortInBlock>,
}

#[derive(Debug, Clone)]
pub struct ModulePortInBlock {
    pub span: Span,
    pub id: Identifier,
    pub kind: ModulePortInBlockKind,
}

#[derive(Debug, Clone)]
pub enum ModulePortSingleKind {
    Port {
        direction: Spanned<PortDirection>,
        kind: PortSingleKindInner,
    },
    Interface {
        span_keyword: Span,
        domain: Spanned<DomainKind<Expression>>,
        interface: Expression,
    },
}

#[derive(Debug, Copy, Clone)]
pub enum PortSingleKindInner {
    Clock {
        span_clock: Span,
    },
    Normal {
        domain: Spanned<DomainKind<Expression>>,
        ty: Expression,
    },
}

#[derive(Debug, Copy, Clone)]
pub enum ModulePortInBlockKind {
    Port {
        direction: Spanned<PortDirection>,
        ty: Expression,
    },
    Interface {
        span_keyword: Span,
        interface: Expression,
    },
}

// TODO rename to HardwareDomain and include clock here?
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum DomainKind<S> {
    Const,
    Async,
    Sync(SyncDomain<S>),
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct SyncDomain<S> {
    // TODO do we even need names here, is this not just a set of posedge sensitivities?
    pub clock: S,
    /// No reset means there is no separate sensitivity for a reset signal.
    /// This can be cause there is no reset, or because the reset is synchronous.
    pub reset: Option<S>,
}

impl<S> DomainKind<S> {
    pub fn map_signal<U>(self, f: impl FnMut(S) -> U) -> DomainKind<U> {
        match self {
            DomainKind::Const => DomainKind::Const,
            DomainKind::Async => DomainKind::Async,
            DomainKind::Sync(sync) => DomainKind::Sync(sync.map_signal(f)),
        }
    }
}

impl<S> SyncDomain<S> {
    pub fn as_ref(&self) -> SyncDomain<&S> {
        SyncDomain {
            clock: &self.clock,
            reset: self.reset.as_ref(),
        }
    }

    pub fn map_signal<U>(self, mut f: impl FnMut(S) -> U) -> SyncDomain<U> {
        SyncDomain {
            clock: f(self.clock),
            reset: self.reset.map(f),
        }
    }

    pub fn try_map_signal<U, E>(self, mut f: impl FnMut(S) -> Result<U, E>) -> Result<SyncDomain<U>, E> {
        Ok(SyncDomain {
            clock: f(self.clock)?,
            reset: self.reset.map(f).transpose()?,
        })
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum PortDirection {
    Input,
    Output,
}

impl PortDirection {
    pub fn diagnostic_string(self) -> &'static str {
        match self {
            PortDirection::Input => "input",
            PortDirection::Output => "output",
        }
    }

    pub fn token(self) -> TokenType {
        match self {
            PortDirection::Input => TokenType::In,
            PortDirection::Output => TokenType::Out,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Block<S> {
    pub span: Span,
    pub statements: Vec<S>,
}

#[derive(Debug, Clone)]
pub struct BlockExpression {
    pub statements: Vec<BlockStatement>,
    pub expression: Expression,
}

pub type ModuleStatement = Spanned<ModuleStatementKind>;
pub type BlockStatement = Spanned<BlockStatementKind>;

#[derive(Debug, Clone)]
pub enum ModuleStatementKind {
    ParseError(RecoveredParseError),

    WireDeclaration(WireDeclaration),

    CombinatorialProcess(CombinatorialProcess),
    ClockedProcess(ClockedProcess),
    Instance(ModuleInstance),
}

#[derive(Debug, Clone)]
pub enum BlockStatementKind {
    // declarations
    CommonDeclaration(CommonDeclaration<()>),
    VariableDeclaration(VariableDeclaration),
    RegisterDeclaration(RegisterDeclaration),

    // basic statements
    Assignment(Assignment),
    // TODO remove expressions, maybe with exception for function calls?
    Expression(Expression),

    // control flow
    Block(Block<BlockStatement>),
    If(IfStatement<Block<BlockStatement>>),
    Match(MatchStatement<Block<BlockStatement>>),

    For(ForStatement<Block<BlockStatement>>),
    While(WhileStatement),

    // control flow terminators
    Return(ReturnStatement),
    Break { span: Span },
    Continue { span: Span },
}

#[derive(Debug, Clone)]
pub struct IfStatement<B> {
    pub span: Span,
    pub initial_if: IfCondBlockPair<B>,
    pub else_ifs: Vec<IfCondBlockPair<B>>,
    pub final_else: Option<B>,
}

#[derive(Debug, Clone)]
pub struct IfCondBlockPair<B> {
    pub span: Span,
    pub span_if: Span,
    pub cond: Expression,
    pub block: B,
}

#[derive(Debug, Clone)]
pub struct MatchStatement<B> {
    pub span_keyword: Span,
    pub target: Expression,
    // TODO re-instate some variant of ExtraList that does not support match itself
    pub branches: Vec<MatchBranch<B>>,
    pub pos_end: Pos,
}

#[derive(Debug, Clone)]
pub struct MatchBranch<B> {
    pub pattern: Spanned<MatchPattern>,
    pub block: B,
}

#[derive(Debug, Copy, Clone)]
pub enum MatchPattern {
    Wildcard,
    WildcardVal(MaybeIdentifier),
    EqualTo(Expression),
    InRange {
        span_in: Span,
        range: Expression,
    },
    IsEnumVariant {
        variant: SimpleIdentifier,
        payload_id: Option<MaybeIdentifier>,
    },
}

#[derive(Debug, Clone)]
pub struct WhileStatement {
    pub span_keyword: Span,
    pub cond: Expression,
    pub body: Block<BlockStatement>,
}

#[derive(Debug, Clone)]
pub struct ForStatement<B> {
    pub span_keyword: Span,
    pub index: MaybeIdentifier,
    pub index_ty: Option<Expression>,
    pub iter: Expression,
    pub body: B,
}

#[derive(Debug, Clone)]
pub struct ReturnStatement {
    pub span_return: Span,
    pub value: Option<Expression>,
}

#[derive(Debug, Clone)]
pub struct WireDeclaration {
    pub vis: Visibility,
    pub span_keyword: Span,
    pub id: MaybeIdentifier,
    pub kind: WireDeclarationKind,
}

#[derive(Debug, Copy, Clone)]
pub enum WireDeclarationKind {
    Normal {
        domain_ty: WireDeclarationDomainTyKind,
        assign_span_and_value: Option<(Span, Expression)>,
    },
    Interface {
        domain: Option<Spanned<DomainKind<Expression>>>,
        span_keyword: Span,
        interface: Expression,
    },
}

#[derive(Debug, Copy, Clone)]
pub enum WireDeclarationDomainTyKind {
    Clock {
        span_clock: Span,
    },
    Normal {
        domain: Option<Spanned<DomainKind<Expression>>>,
        ty: Option<Expression>,
    },
}

#[derive(Debug, Clone)]
pub struct TypeDeclaration {
    pub span: Span,
    pub id: MaybeIdentifier,
    pub params: Option<Parameters>,
    pub body: Expression,
}

#[derive(Debug, Clone)]
pub struct ConstDeclaration {
    pub span: Span,
    pub id: MaybeIdentifier,
    pub ty: Option<Expression>,
    pub value: Expression,
}

#[derive(Debug, Clone)]
pub struct VariableDeclaration {
    pub span: Span,
    pub mutable: bool,
    pub id: MaybeIdentifier,
    pub ty: Option<Expression>,
    pub init: Option<Expression>,
}

#[derive(Debug, Clone)]
pub struct RegisterDeclaration {
    pub span_keyword: Span,
    pub kind: RegisterDeclarationKind,
    pub reset: Expression,
}

#[derive(Debug, Copy, Clone)]
pub enum RegisterDeclarationKind {
    Wire(RegisterDeclarationWire),
    New(RegisterDeclarationNew),
}

#[derive(Debug, Copy, Clone)]
pub struct RegisterDeclarationWire {
    pub span_keyword_wire: Span,
    pub target: Expression,
}

#[derive(Debug, Copy, Clone)]
pub struct RegisterDeclarationNew {
    pub id: Identifier,
    pub ty: Option<Expression>,
}

#[derive(Debug, Clone)]
pub struct Assignment {
    pub span: Span,
    pub op: Spanned<Option<AssignBinaryOp>>,
    pub target: Expression,
    pub value: Expression,
}

#[derive(Debug, Clone)]
pub struct CombinatorialProcess {
    pub span_keyword: Span,
    pub block: Block<BlockStatement>,
}

#[derive(Debug, Clone)]
pub struct ClockedProcess {
    pub span_keyword: Span,
    pub span_domain: Span,
    pub clock: Expression,
    /// No reset means this block does not have a reset.
    pub reset: Option<Spanned<ClockedProcessReset<Expression>>>,
    pub block: Block<BlockStatement>,
}

#[derive(Debug, Copy, Clone)]
pub struct ClockedProcessReset<S> {
    pub kind: Spanned<ResetKind>,
    pub signal: S,
}

impl<S> ClockedProcessReset<S> {
    pub fn map_signal<U>(self, f: impl FnOnce(S) -> U) -> ClockedProcessReset<U> {
        ClockedProcessReset {
            kind: self.kind,
            signal: f(self.signal),
        }
    }

    pub fn as_ref(&self) -> ClockedProcessReset<&S> {
        ClockedProcessReset {
            kind: self.kind,
            signal: &self.signal,
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub enum ResetKind {
    Async,
    Sync,
}

impl ResetKind {
    pub fn token(self) -> TokenType {
        match self {
            ResetKind::Async => TokenType::Async,
            ResetKind::Sync => TokenType::Sync,
        }
    }
}

#[derive(Debug, Clone)]
pub struct ModuleInstanceItem {
    pub span: Span,
    pub span_keyword: Span,
    pub module: Expression,
}

#[derive(Debug, Clone)]
pub struct ModuleInstance {
    pub name: Option<Identifier>,
    pub span_keyword: Span,
    pub module: Expression,
    pub port_connections: Spanned<ExtraList<PortConnection>>,
}

#[derive(Debug, Clone)]
pub struct PortConnection {
    pub id: Identifier,
    pub expr: PortConnectionExpression,
}

// TODO find a way to avoid this expression representation weirdness
#[derive(Debug, Copy, Clone)]
pub enum PortConnectionExpression {
    FakeId(Expression),
    Real(Expression),
}

impl PortConnectionExpression {
    pub fn expr(&self) -> Expression {
        match *self {
            PortConnectionExpression::FakeId(expr) => expr,
            PortConnectionExpression::Real(expr) => expr,
        }
    }
}

// TODO we're using Box<Spanned<ExpressionKind>> a lot, but maybe
//   Spanned<Box<ExpressionKind>> is better?
pub type Expression = Spanned<ExpressionKindIndex>;

#[derive(Debug, Clone)]
pub enum ExpressionKind {
    ParseError(RecoveredParseError),

    // Miscellaneous
    Dummy,
    Undefined,
    Type,
    Slf,
    Builtin {
        span_keyword: Span,
        args: Spanned<Vec<Expression>>,
    },

    /// Wrapped just means an expression that's surrounded by parenthesis.
    /// It has to be a dedicated expression to ensure it gets a separate span.
    Wrapped(Expression),

    Block(BlockExpression),
    Id(Identifier),

    // Literals
    IntLiteral(IntLiteral),
    BoolLiteral(bool),
    StringLiteral(Vec<StringPiece<Span, Expression>>),

    // Structures
    ArrayLiteral(Vec<ArrayLiteralElement<Expression>>),
    TupleLiteral(Vec<Expression>),
    RangeLiteral(RangeLiteral),
    ArrayComprehension(ArrayComprehension),

    // Operations
    UnaryOp(Spanned<UnaryOp>, Expression),
    BinaryOp(Spanned<BinaryOp>, Expression, Expression),

    // Indexing
    ArrayType {
        span_brackets: Span,
        lengths: Vec<ArrayLiteralElement<Expression>>,
        inner_ty: Expression,
    },
    ArrayIndex {
        span_brackets: Span,
        base: Expression,
        indices: Vec<ArrayLiteralElement<Expression>>,
    },
    DotIndex(Expression, DotIndexKind),

    // Calls
    Call(Expression, Args),
    UnsafeValueWithDomain(Expression, Spanned<DomainKind<Expression>>),
    Ref(Span, Expression),
    Deref(Span, Expression),
}

#[derive(Debug, Copy, Clone)]
pub enum DotIndexKind {
    Id(Identifier),
    Int { span: Span },
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum StringPiece<L, E> {
    Literal(L),
    Substitute(E),
}

pub type Args<N = Option<Identifier>, T = Expression> = ExtraList<Arg<N, T>>;

#[derive(Debug, Copy, Clone)]
pub struct Arg<N = Option<Identifier>, T = Expression> {
    pub span: Span,
    pub name: N,
    pub value: T,
}

#[derive(Debug, Copy, Clone)]
pub enum ArrayLiteralElement<V> {
    Single(V),
    Spread(Span, V),
}

impl<V> ArrayLiteralElement<V> {
    pub fn map_inner<W>(self, f: impl FnOnce(V) -> W) -> ArrayLiteralElement<W> {
        match self {
            ArrayLiteralElement::Single(value) => ArrayLiteralElement::Single(f(value)),
            ArrayLiteralElement::Spread(span, value) => ArrayLiteralElement::Spread(span, f(value)),
        }
    }

    pub fn value(&self) -> &V {
        match self {
            ArrayLiteralElement::Single(value) => value,
            ArrayLiteralElement::Spread(_, value) => value,
        }
    }
}

impl<T, E> ArrayLiteralElement<Result<T, E>> {
    pub fn transpose(self) -> Result<ArrayLiteralElement<T>, E> {
        match self {
            ArrayLiteralElement::Single(value) => Ok(ArrayLiteralElement::Single(value?)),
            ArrayLiteralElement::Spread(span, value) => Ok(ArrayLiteralElement::Spread(span, value?)),
        }
    }
}

// TODO allow multiple sequential for loops
#[derive(Debug, Clone)]
pub struct ArrayComprehension {
    pub body: ArrayLiteralElement<Expression>,
    pub index: MaybeIdentifier,
    pub span_keyword: Span,
    pub iter: Expression,
}

#[derive(Debug, Copy, Clone)]
pub enum RangeLiteral {
    ExclusiveEnd {
        op_span: Span,
        start: Option<Expression>,
        end: Option<Expression>,
    },
    InclusiveEnd {
        op_span: Span,
        start: Option<Expression>,
        end_inc: Expression,
    },
    Length {
        op_span: Span,
        start: Expression,
        length: Expression,
    },
}

#[derive(Debug, Clone)]
pub struct SyncExpression {
    pub clock: Expression,
    pub body: Block<BlockStatement>,
}

// TODO allow: undefined, wildcard, 0, 1, hex, decimal, ...
// TODO wildcard symbol: `_`, `?`, `*`, `#`?
//     `*` is a bad idea
// (don't allow any of the fancy stuff stuff for decimal ofc)
#[derive(Debug, Clone)]
pub enum IntLiteral {
    // 0b[01_]+
    Binary { span: Span },
    // [0-9_]+
    Decimal { span: Span },
    // 0x[0-9a-fA-F_]+
    Hexadecimal { span: Span },
}

#[derive(Debug, Copy, Clone)]
pub struct SimpleIdentifier {
    pub span: Span,
}

#[derive(Debug, Copy, Clone)]
pub enum Identifier {
    Simple(SimpleIdentifier),
    FromString(Span, Expression),
}

#[derive(Debug, Copy, Clone)]
pub enum MaybeIdentifier<I = Identifier> {
    Dummy { span: Span },
    Identifier(I),
}

pub type MaybeSimpleIdentifier = MaybeIdentifier<SimpleIdentifier>;

// TODO move to parser utilities module
pub fn build_binary_op(
    arena_expressions: &mut Arena<ExpressionKindIndex, ExpressionKind>,
    op_span: Span,
    op: BinaryOp,
    left: Spanned<ExpressionKind>,
    right: Spanned<ExpressionKind>,
) -> ExpressionKind {
    ExpressionKind::BinaryOp(
        Spanned {
            span: op_span,
            inner: op,
        },
        left.map_inner(|e| arena_expressions.push(e)),
        right.map_inner(|e| arena_expressions.push(e)),
    )
}

#[derive(Debug, Copy, Clone)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    FloorDiv,
    CeilDiv,
    Mod,
    Pow,

    BitAnd,
    BitOr,
    BitXor,
    BoolAnd,
    BoolOr,
    BoolXor,

    Shl,
    Shr,

    CmpEq,
    CmpNeq,
    CmpLt,
    CmpLte,
    CmpGt,
    CmpGte,

    In,
}

// TODO add a test that checks that the parser matches these levels
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum BinaryOpLevel {
    Add,
    Mul,
    Pow,
    Bit,
    Bool,
    Shift,
    Cmp,
    In,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum AssignBinaryOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    // TODO add boolean and shift operators
    BitAnd,
    BitOr,
    BitXor,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum UnaryOp {
    Plus,
    Neg,
    Not,
}

impl SimpleIdentifier {
    pub fn str(self, source: &SourceDatabase) -> &str {
        source.span_str(self.span)
    }

    pub fn spanned_str(self, source: &SourceDatabase) -> Spanned<&str> {
        Spanned::new(self.span, self.str(source))
    }

    pub fn spanned_string(self, source: &SourceDatabase) -> Spanned<String> {
        self.spanned_str(source).map_inner(str::to_owned)
    }
}

impl<I> MaybeIdentifier<I> {
    pub fn map_id<J>(self, f: impl FnOnce(I) -> J) -> MaybeIdentifier<J> {
        match self {
            MaybeIdentifier::Dummy { span } => MaybeIdentifier::Dummy { span },
            MaybeIdentifier::Identifier(id) => MaybeIdentifier::Identifier(f(id)),
        }
    }

    pub fn as_ref(&self) -> MaybeIdentifier<&I> {
        match self {
            &MaybeIdentifier::Dummy { span } => MaybeIdentifier::Dummy { span },
            MaybeIdentifier::Identifier(id) => MaybeIdentifier::Identifier(id),
        }
    }
}

impl<I, R> MaybeIdentifier<Result<I, R>> {
    pub fn transpose(self) -> Result<MaybeIdentifier<I>, R> {
        match self {
            MaybeIdentifier::Dummy { span } => Ok(MaybeIdentifier::Dummy { span }),
            MaybeIdentifier::Identifier(id) => Ok(MaybeIdentifier::Identifier(id?)),
        }
    }
}

#[derive(Debug)]
pub struct ItemInfo {
    pub span_full: Span,
    pub span_short: Span,
    pub declaration: Option<ItemDeclarationInfo>,
}

#[derive(Debug)]
pub struct ItemDeclarationInfo {
    pub vis: Visibility,
    pub id: MaybeIdentifier,
}

impl Item {
    pub fn info(&self) -> ItemInfo {
        match self {
            Item::Import(item) => ItemInfo {
                span_full: item.span,
                span_short: item.span,
                declaration: None,
            },
            Item::CommonDeclaration(item) => ItemInfo {
                span_full: item.span,
                span_short: item.inner.span_short(),
                declaration: match &item.inner {
                    CommonDeclaration::Named(decl) => Some(ItemDeclarationInfo {
                        vis: decl.vis,
                        id: decl.kind.id(),
                    }),
                    CommonDeclaration::ConstBlock(_) => None,
                },
            },
            Item::ModuleInternal(item) => ItemInfo {
                span_full: item.span,
                span_short: item.id.span(),
                declaration: Some(ItemDeclarationInfo {
                    vis: item.vis,
                    id: item.id,
                }),
            },
            Item::ModuleExternal(item) => ItemInfo {
                span_full: item.span,
                span_short: item.id.span(),
                declaration: Some(ItemDeclarationInfo {
                    vis: item.vis,
                    id: item.id.into(),
                }),
            },
            Item::Interface(item) => ItemInfo {
                span_full: item.span,
                span_short: item.id.span(),
                declaration: Some(ItemDeclarationInfo {
                    vis: item.vis,
                    id: item.id,
                }),
            },
        }
    }
}

impl<V> CommonDeclaration<V> {
    pub fn span_short(&self) -> Span {
        match self {
            CommonDeclaration::Named(decl) => decl.kind.id().span(),
            CommonDeclaration::ConstBlock(block) => block.span_keyword,
        }
    }
}

impl CommonDeclarationNamedKind {
    pub fn id(&self) -> MaybeIdentifier {
        match self {
            CommonDeclarationNamedKind::Type(decl) => decl.id,
            CommonDeclarationNamedKind::Const(decl) => decl.id,
            CommonDeclarationNamedKind::Struct(decl) => decl.id,
            CommonDeclarationNamedKind::Enum(decl) => decl.id,
            CommonDeclarationNamedKind::Function(decl) => decl.id,
        }
    }
}

impl UnaryOp {
    pub fn token(self) -> TokenType {
        match self {
            UnaryOp::Plus => TokenType::Plus,
            UnaryOp::Neg => TokenType::Minus,
            UnaryOp::Not => TokenType::Bang,
        }
    }
}

impl BinaryOp {
    pub fn token(self) -> TokenType {
        match self {
            BinaryOp::Add => TokenType::Plus,
            BinaryOp::Sub => TokenType::Minus,
            BinaryOp::Mul => TokenType::Star,
            BinaryOp::FloorDiv => TokenType::Slash,
            BinaryOp::CeilDiv => TokenType::PlusSlash,
            BinaryOp::Mod => TokenType::Percent,
            BinaryOp::Pow => TokenType::StarStar,
            BinaryOp::BitAnd => TokenType::Amper,
            BinaryOp::BitOr => TokenType::Pipe,
            BinaryOp::BitXor => TokenType::Caret,
            BinaryOp::BoolAnd => TokenType::AmperAmper,
            BinaryOp::BoolOr => TokenType::PipePipe,
            BinaryOp::BoolXor => TokenType::CaretCaret,
            BinaryOp::Shl => TokenType::LtLt,
            BinaryOp::Shr => TokenType::GtGt,
            BinaryOp::CmpEq => TokenType::EqEq,
            BinaryOp::CmpNeq => TokenType::Neq,
            BinaryOp::CmpLt => TokenType::Lt,
            BinaryOp::CmpLte => TokenType::Lte,
            BinaryOp::CmpGt => TokenType::Gt,
            BinaryOp::CmpGte => TokenType::Gte,
            BinaryOp::In => TokenType::In,
        }
    }

    pub fn level(self) -> BinaryOpLevel {
        match self {
            BinaryOp::Add | BinaryOp::Sub => BinaryOpLevel::Add,
            BinaryOp::Mul | BinaryOp::FloorDiv | BinaryOp::CeilDiv | BinaryOp::Mod => BinaryOpLevel::Mul,
            BinaryOp::Pow => BinaryOpLevel::Pow,
            BinaryOp::BitAnd | BinaryOp::BitOr | BinaryOp::BitXor => BinaryOpLevel::Bit,
            BinaryOp::BoolAnd | BinaryOp::BoolOr | BinaryOp::BoolXor => BinaryOpLevel::Bool,
            BinaryOp::Shl | BinaryOp::Shr => BinaryOpLevel::Shift,
            BinaryOp::CmpEq
            | BinaryOp::CmpNeq
            | BinaryOp::CmpLt
            | BinaryOp::CmpLte
            | BinaryOp::CmpGt
            | BinaryOp::CmpGte => BinaryOpLevel::Cmp,
            BinaryOp::In => BinaryOpLevel::In,
        }
    }
}

impl AssignBinaryOp {
    pub fn token(self) -> TokenType {
        match self {
            AssignBinaryOp::Add => TokenType::PlusEq,
            AssignBinaryOp::Sub => TokenType::MinusEq,
            AssignBinaryOp::Mul => TokenType::StarEq,
            AssignBinaryOp::Div => TokenType::SlashEq,
            AssignBinaryOp::Mod => TokenType::PercentEq,
            AssignBinaryOp::BitAnd => TokenType::AmperEq,
            AssignBinaryOp::BitOr => TokenType::PipeEq,
            AssignBinaryOp::BitXor => TokenType::CaretEq,
        }
    }

    pub fn to_binary_op(self) -> BinaryOp {
        match self {
            AssignBinaryOp::Add => BinaryOp::Add,
            AssignBinaryOp::Sub => BinaryOp::Sub,
            AssignBinaryOp::Mul => BinaryOp::Mul,
            AssignBinaryOp::Div => BinaryOp::FloorDiv,
            AssignBinaryOp::Mod => BinaryOp::Mod,
            AssignBinaryOp::BitAnd => BinaryOp::BitAnd,
            AssignBinaryOp::BitOr => BinaryOp::BitOr,
            AssignBinaryOp::BitXor => BinaryOp::BitXor,
        }
    }
}

impl<B> IfStatement<B> {
    pub fn map_block<C>(self, mut f: impl FnMut(B) -> C) -> IfStatement<C> {
        let IfStatement {
            span,
            initial_if,
            else_ifs,
            final_else,
        } = self;

        IfStatement {
            span,
            initial_if: initial_if.map_block(&mut f),
            else_ifs: else_ifs.into_iter().map(|p| p.map_block(&mut f)).collect_vec(),
            final_else: final_else.map(&mut f),
        }
    }
}

impl<B> IfCondBlockPair<B> {
    pub fn map_block<C>(self, mut f: impl FnMut(B) -> C) -> IfCondBlockPair<C> {
        let IfCondBlockPair {
            span,
            span_if,
            cond,
            block,
        } = self;
        IfCondBlockPair {
            span,
            span_if,
            cond,
            block: f(block),
        }
    }
}

// TODO this could be reduced a bit with a derive macro, eg. for enums it could automatically combine the branches
impl_has_span!(SimpleIdentifier);
impl_has_span!(Parameter);
impl_has_span!(ModulePortInBlock);
impl_has_span!(StructField);
impl_has_span!(EnumDeclaration);
impl_has_span!(EnumVariant);

impl<T> HasSpan for FunctionDeclaration<T> {
    fn span(&self) -> Span {
        self.span
    }
}

impl<T> HasSpan for ExtraList<T> {
    fn span(&self) -> Span {
        self.span
    }
}

impl<T> HasSpan for ExtraListBlock<T> {
    fn span(&self) -> Span {
        self.span
    }
}

impl HasSpan for WhileStatement {
    fn span(&self) -> Span {
        self.span_keyword.join(self.body.span)
    }
}

impl<B: HasSpan> HasSpan for ForStatement<B> {
    fn span(&self) -> Span {
        self.span_keyword.join(self.body.span())
    }
}

impl<B> HasSpan for IfStatement<B> {
    fn span(&self) -> Span {
        self.span
    }
}

impl<B> HasSpan for MatchStatement<B> {
    fn span(&self) -> Span {
        self.span_keyword.join(Span::empty_at(self.pos_end))
    }
}

impl HasSpan for ModulePortItem {
    fn span(&self) -> Span {
        match self {
            ModulePortItem::Single(port) => port.span,
            ModulePortItem::DomainBlock(block) => block.span,
        }
    }
}

impl<V> HasSpan for ArrayLiteralElement<Spanned<V>> {
    fn span(&self) -> Span {
        match self {
            ArrayLiteralElement::Spread(span, value) => span.join(value.span),
            ArrayLiteralElement::Single(value) => value.span,
        }
    }
}

impl<V> HasSpan for ArrayLiteralElement<Box<Spanned<V>>> {
    fn span(&self) -> Span {
        match self {
            ArrayLiteralElement::Spread(span, value) => span.join(value.span),
            ArrayLiteralElement::Single(value) => value.span,
        }
    }
}

impl<T: HasSpan> HasSpan for MaybeIdentifier<T> {
    fn span(&self) -> Span {
        match self {
            &MaybeIdentifier::Dummy { span } => span,
            MaybeIdentifier::Identifier(id) => id.span(),
        }
    }
}

impl HasSpan for Identifier {
    fn span(&self) -> Span {
        match self {
            Identifier::Simple(id) => id.span,
            Identifier::FromString(span, _) => *span,
        }
    }
}

impl<V> HasSpan for CommonDeclaration<V> {
    fn span(&self) -> Span {
        match self {
            CommonDeclaration::Named(decl) => decl.kind.span(),
            CommonDeclaration::ConstBlock(decl) => decl.span(),
        }
    }
}

impl HasSpan for ConstBlock {
    fn span(&self) -> Span {
        let ConstBlock { span_keyword, block } = self;
        span_keyword.join(block.span)
    }
}

impl HasSpan for CommonDeclarationNamedKind {
    fn span(&self) -> Span {
        match self {
            CommonDeclarationNamedKind::Type(decl) => decl.span,
            CommonDeclarationNamedKind::Const(decl) => decl.span,
            CommonDeclarationNamedKind::Struct(decl) => decl.span,
            CommonDeclarationNamedKind::Enum(decl) => decl.span,
            CommonDeclarationNamedKind::Function(decl) => decl.span,
        }
    }
}

impl<B: HasSpan> HasSpan for MatchBranch<B> {
    fn span(&self) -> Span {
        let MatchBranch { pattern, block } = self;
        pattern.span.join(block.span())
    }
}

impl<B> HasSpan for Block<B> {
    fn span(&self) -> Span {
        self.span
    }
}

impl<B: HasSpan> HasSpan for SyncDomain<B> {
    fn span(&self) -> Span {
        let SyncDomain { clock, reset } = self;
        match reset {
            Some(reset) => clock.span().join(reset.span()),
            None => clock.span(),
        }
    }
}

impl HasSpan for DotIndexKind {
    fn span(&self) -> Span {
        match self {
            DotIndexKind::Id(id) => id.span(),
            &DotIndexKind::Int { span } => span,
        }
    }
}

impl HasSpan for InterfaceListItem {
    fn span(&self) -> Span {
        match self {
            InterfaceListItem::Signal(signal) => {
                let InterfaceSignal { id, ty } = signal;
                id.span().join(ty.span)
            }
            InterfaceListItem::View(view) => view.span,
        }
    }
}

impl HasSpan for PortConnection {
    fn span(&self) -> Span {
        let PortConnection { id, expr } = self;
        id.span().join(expr.expr().span)
    }
}

impl From<SimpleIdentifier> for Identifier {
    fn from(value: SimpleIdentifier) -> Self {
        Identifier::Simple(value)
    }
}

impl From<SimpleIdentifier> for MaybeIdentifier {
    fn from(value: SimpleIdentifier) -> Self {
        MaybeIdentifier::Identifier(Identifier::Simple(value))
    }
}

impl From<MaybeSimpleIdentifier> for MaybeIdentifier {
    fn from(value: MaybeSimpleIdentifier) -> Self {
        value.map_id(Identifier::Simple)
    }
}

impl<I> From<I> for MaybeIdentifier<I> {
    fn from(i: I) -> Self {
        MaybeIdentifier::Identifier(i)
    }
}

pub trait MaybeParameterSelf: Copy {
    fn as_parameter_self(&self) -> Option<ParameterSelf>;
}
impl MaybeParameterSelf for () {
    fn as_parameter_self(&self) -> Option<ParameterSelf> {
        None
    }
}
impl MaybeParameterSelf for ParameterSelf {
    fn as_parameter_self(&self) -> Option<ParameterSelf> {
        Some(*self)
    }
}

pub trait MaybeVisibility: Copy {
    fn as_visibility(&self) -> Option<Visibility>;
}
impl MaybeVisibility for () {
    fn as_visibility(&self) -> Option<Visibility> {
        None
    }
}
impl MaybeVisibility for Visibility {
    fn as_visibility(&self) -> Option<Visibility> {
        Some(*self)
    }
}
