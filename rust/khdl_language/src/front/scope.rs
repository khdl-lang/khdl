use crate::front::compile::CompileRefs;
use crate::front::diagnostic::{DiagError, DiagResult, DiagnosticError, Diagnostics};
use crate::front::expression::LeftInterfaceInfo;
use crate::front::flow::{Flow, Variable};
use crate::front::signal::Signal;
use crate::front::value::{CompileValue, ReferenceWrapper, Value};
use crate::syntax::ast::MaybeIdentifier;
use crate::syntax::parsed::AstRefItem;
use crate::syntax::pos::{HasSpan, Span, Spanned};
use crate::util::ResultExt;
use crate::util::edit_distance::hint_options_by_edit_distance;
use crate::util::intern::{Id, Interner};
use indexmap::map::{Entry, IndexMap};
use khdl_util::constants::MAX_IDENTIFIER_SUGGESTIONS;
use std::cell::RefCell;
use std::fmt::Debug;
use std::sync::Arc;

#[derive(Debug)]
pub struct FrozenScope {
    parent: Option<Arc<FrozenScope>>,
    content: ScopeContent,
}

#[derive(Debug)]
pub struct Scope<'p> {
    parent: ScopeParent<'p>,
    content: RefCell<ScopeContent>,
}

#[derive(Debug)]
pub enum ScopeParent<'p> {
    Frozen(Arc<FrozenScope>),
    Normal(&'p Scope<'p>),
}

// TODO use string interning to avoid a bunch of string equality checks and hashing
#[derive(Debug)]
pub struct ScopeContent {
    span: Span,
    values: IndexMap<ScopeKey<Id, ()>, DeclaredValue>,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum ScopeKey<I, S> {
    Id(I),
    Slf(S),
}

// TODO do we actually still need clone bounds here?
#[derive(Debug, Clone)]
pub enum ScopedEntry {
    /// Indirection though an item, the item should be evaluated.
    Item(AstRefItem),
    /// A named value: port, register, wire, variable.
    /// These are not fully evaluated immediately, they might be used symbolically
    ///   as assignment targets or in domain expressions.
    Named(NamedValue),
    /// Captured value, no longer directly connected to the original declaration.
    Captured(CapturedValue),
    /// Simple value.
    Value(Value),
    /// A receiver alias, retaining target identity when the scope is captured.
    Alias(ReferenceWrapper),
}

#[derive(Debug, Clone)]
pub enum NamedValue {
    Variable(Variable),
    Signal(Signal),
    Interface(LeftInterfaceInfo),
}

#[derive(Debug, Clone)]
pub struct CapturedValue {
    pub span_capture: Span,
    pub value: Result<Arc<CompileValue>, CaptureFailed>,
}

#[derive(Debug, Copy, Clone)]
pub enum CaptureFailed {
    NotCompile,
    NotFullyInitialized,
}

// TODO simplify all of this: we might only only need to report errors on the first re-declaration,
//   which means we can remove that branch entirely
// TODO we store the span twice, why?
#[derive(Debug)]
enum DeclaredValue {
    Once { value: DiagResult<ScopedEntry>, span: Span },
    Multiple { spans: Vec<Span>, err: DiagError },
    Error(DiagError),
}

#[derive(Debug, Copy, Clone)]
pub enum DeclaredValueSingle<S = ScopedEntry> {
    Value { span: Span, value: S },
    Error(DiagError),
}

#[derive(Debug)]
pub struct ScopeFound {
    pub span_decl: Span,
    pub value: ScopedEntry,
}

impl FrozenScope {
    pub fn new(span: Span) -> Self {
        FrozenScope {
            parent: None,
            content: ScopeContent::new(span),
        }
    }

    pub fn as_scope(self: Arc<FrozenScope>) -> Scope<'static> {
        Scope::new(self.content.span, ScopeParent::Frozen(self))
    }

    pub fn new_child(self: Arc<FrozenScope>, span: Span) -> Scope<'static> {
        Scope::new(span, ScopeParent::Frozen(self))
    }

    pub fn declare(
        &mut self,
        diags: &Diagnostics,
        interner: &Interner,
        key: impl Into<ScopeKey<MaybeIdentifier<Spanned<Id>>, Span>>,
        value: DiagResult<ScopedEntry>,
    ) {
        self.content.declare(diags, interner, key, value);
    }

    pub fn declare_already_checked(&mut self, id: Id, value: DeclaredValueSingle) {
        self.content.declare_already_checked(id, value);
    }

    pub fn find(
        &self,
        diags: &Diagnostics,
        interner: &Interner,
        key: impl Into<ScopeKey<Spanned<Id>, Span>>,
    ) -> DiagResult<ScopeFound> {
        // find
        let key = key.into();
        if let Some(found) = self.try_find(key.without_span())? {
            return Ok(found);
        }

        // failed, report err
        let mut options = vec![];
        self.collect_options(&mut options);
        Err(error_not_found(interner, self.content.span, key, options).report(diags))
    }

    fn try_find(&self, key: ScopeKey<Id, ()>) -> DiagResult<Option<ScopeFound>> {
        let mut curr = self;
        loop {
            if let Some(found) = curr.content.try_find(key)? {
                return Ok(Some(found));
            }
            curr = match &curr.parent {
                Some(parent) => parent,
                None => return Ok(None),
            }
        }
    }

    fn collect_options(&self, options: &mut Vec<ScopeKey<Id, ()>>) {
        let mut curr = self;
        loop {
            options.extend(curr.content.values.keys().copied());
            curr = match &curr.parent {
                Some(parent) => parent,
                None => break,
            }
        }
    }

    pub fn for_each_immediate_entry(&self, f: impl FnMut(ScopeKey<Id, ()>, DeclaredValueSingle<&ScopedEntry>)) {
        self.content.for_each_immediate_entry(f);
    }

    pub fn has_immediate_entry(&self, key: impl Into<ScopeKey<Id, ()>>) -> bool {
        self.content.has_immediate_entry(key)
    }
}

impl<'p> Scope<'p> {
    pub fn new_child(&'p self, span: Span) -> Self {
        Scope::new(span, ScopeParent::Normal(self))
    }

    fn new(span: Span, parent: ScopeParent<'p>) -> Self {
        Scope {
            parent,
            content: RefCell::new(ScopeContent::new(span)),
        }
    }

    pub fn restore_from_content(parent: ScopeParent<'p>, content: ScopeContent) -> Self {
        Scope {
            parent,
            content: RefCell::new(content),
        }
    }

    pub fn into_content(self) -> ScopeContent {
        self.content.into_inner()
    }

    pub fn for_each_immediate_entry(&self, f: impl FnMut(ScopeKey<Id, ()>, DeclaredValueSingle<&ScopedEntry>)) {
        self.content.borrow().for_each_immediate_entry(f);
    }

    /// Declare a value in this scope.
    ///
    /// Allows shadowing identifiers in the parent scope, but not in the local scope.
    ///
    /// This function always appears to succeed, errors are instead reported as diags.
    /// This also tracks identifiers that have erroneously been declared multiple times,
    /// so that [Scope::find] can return an error for those cases.
    pub fn declare(
        &mut self,
        refs: CompileRefs,
        key: impl Into<ScopeKey<MaybeIdentifier<Spanned<Id>>, Span>>,
        value: DiagResult<ScopedEntry>,
    ) {
        self.content
            .get_mut()
            .declare(refs.diags, &refs.shared.interner, key, value)
    }

    /// The same as [Self::declare], but does not require `&mut self`.
    ///
    /// This should only be used in cases where a declaration needs to happen in a borrowed parent scope.
    /// We don't want to use this as the default declare method, since usually that is an error.
    pub fn declare_non_mut(
        &self,
        refs: CompileRefs,
        key: impl Into<ScopeKey<MaybeIdentifier<Spanned<Id>>, Span>>,
        value: DiagResult<ScopedEntry>,
    ) {
        self.content
            .borrow_mut()
            .declare(refs.diags, &refs.shared.interner, key, value)
    }

    pub fn declare_already_checked(&mut self, id: Id, value: DeclaredValueSingle) {
        self.content.borrow_mut().declare_already_checked(id, value);
    }

    pub fn find(&self, refs: CompileRefs, key: impl Into<ScopeKey<Spanned<Id>, Span>>) -> DiagResult<ScopeFound> {
        // find
        let key = key.into();
        if let Some(found) = self.try_find(key.without_span())? {
            return Ok(found);
        }

        // failed, report err
        let mut options = vec![];
        self.collect_options(&mut options);
        Err(error_not_found(&refs.shared.interner, self.content.borrow().span, key, options).report(refs.diags))
    }

    fn try_find(&self, key: ScopeKey<Id, ()>) -> DiagResult<Option<ScopeFound>> {
        let mut curr = self;
        loop {
            let content = curr.content.borrow();
            if let Some(found) = content.try_find(key)? {
                return Ok(Some(found));
            }
            curr = match &curr.parent {
                ScopeParent::Normal(parent) => parent,
                ScopeParent::Frozen(parent) => return parent.try_find(key),
            };
        }
    }

    fn collect_options(&self, options: &mut Vec<ScopeKey<Id, ()>>) {
        let mut curr = self;
        loop {
            let content = curr.content.borrow();
            options.extend(content.values.keys());
            curr = match &curr.parent {
                ScopeParent::Normal(parent) => parent,
                ScopeParent::Frozen(parent) => {
                    parent.collect_options(options);
                    return;
                }
            };
        }
    }

    pub fn try_find_for_diagnostic(&self, key: impl Into<ScopeKey<Id, ()>>) -> DiagResult<Option<Span>> {
        let key = key.into();

        let mut curr = self;
        loop {
            if let Some(span) = curr.content.borrow().try_find_for_diagnostic(key)? {
                return Ok(Some(span));
            }

            curr = match &curr.parent {
                ScopeParent::Normal(parent) => parent,
                ScopeParent::Frozen(parent) => {
                    let mut curr = parent;
                    loop {
                        if let Some(span) = curr.content.try_find_for_diagnostic(key)? {
                            return Ok(Some(span));
                        }

                        curr = match &curr.parent {
                            Some(parent) => parent,
                            None => return Ok(None),
                        }
                    }
                }
            }
        }
    }

    pub fn capture(&self, flow: &impl Flow, span_capture: Span) -> FrozenScope {
        // walk up scopes, starting from the current scope up to the root
        //   try to capture all values that have not yet been shadowed by a child scope
        let mut captured_values: IndexMap<ScopeKey<Id, ()>, DeclaredValue> = IndexMap::new();

        let mut curr = self;
        let final_parent = loop {
            let curr_content = curr.content.borrow();

            curr_content.for_each_immediate_entry(|id, value| {
                // skip entries already captured by child scopes
                let child_values_entry = match captured_values.entry(id.to_owned()) {
                    Entry::Occupied(_) => return,
                    Entry::Vacant(child_values_entry) => child_values_entry,
                };

                let captured = match value {
                    DeclaredValueSingle::Value { span, value } => {
                        let captured_entry = match value {
                            &ScopedEntry::Item(item) => Ok(ScopedEntry::Item(item)),
                            ScopedEntry::Named(named) => match *named {
                                NamedValue::Variable(var) => {
                                    flow.var_capture(Spanned::new(span_capture, var)).map(|value| {
                                        ScopedEntry::Captured(CapturedValue {
                                            span_capture,
                                            value: value.map(Arc::new),
                                        })
                                    })
                                }
                                NamedValue::Signal(_) | NamedValue::Interface(_) => {
                                    Ok(ScopedEntry::Captured(CapturedValue {
                                        span_capture,
                                        value: Err(CaptureFailed::NotCompile),
                                    }))
                                }
                            },
                            // we're re-capturing, discard the original spans
                            ScopedEntry::Captured(cap) => Ok(ScopedEntry::Captured(CapturedValue {
                                span_capture,
                                value: cap.value.clone(),
                            })),
                            ScopedEntry::Value(v) => Ok(ScopedEntry::Value(v.clone())),
                            ScopedEntry::Alias(rf) => Ok(ScopedEntry::Alias(rf.clone())),
                        };

                        DeclaredValue::Once {
                            span,
                            value: captured_entry,
                        }
                    }
                    DeclaredValueSingle::Error(e) => DeclaredValue::Error(e),
                };

                child_values_entry.insert(captured);
            });

            curr = match &curr.parent {
                ScopeParent::Frozen(parent) => break parent,
                ScopeParent::Normal(parent) => parent,
            };
        };

        FrozenScope {
            parent: Some(Arc::clone(final_parent)),
            content: ScopeContent {
                span: self.content.borrow().span,
                values: captured_values,
            },
        }
    }

    pub fn any_declare_key_error(&self) -> DiagResult {
        for (_, v) in &self.content.borrow().values {
            match v {
                DeclaredValue::Once { .. } => {}
                &DeclaredValue::Multiple { spans: _, err } => return Err(err),
                &DeclaredValue::Error(e) => return Err(e),
            }
        }
        Ok(())
    }
}

impl ScopeContent {
    pub fn new(span: Span) -> ScopeContent {
        ScopeContent {
            span,
            values: IndexMap::new(),
        }
    }

    fn declare(
        &mut self,
        diags: &Diagnostics,
        interner: &Interner,
        key: impl Into<ScopeKey<MaybeIdentifier<Spanned<Id>>, Span>>,
        value: DiagResult<ScopedEntry>,
    ) {
        let key = match key.into() {
            ScopeKey::Id(id) => match id {
                MaybeIdentifier::Dummy { span: _ } => return,
                MaybeIdentifier::Identifier(id) => Spanned::new(id.span, ScopeKey::Id(id.inner)),
            },
            ScopeKey::Slf(span) => Spanned::new(span, ScopeKey::Slf(())),
        };
        self.declare_impl(diags, interner, key, value);
    }

    fn declare_impl(
        &mut self,
        diags: &Diagnostics,
        interner: &Interner,
        key: Spanned<ScopeKey<Id, ()>>,
        value: DiagResult<ScopedEntry>,
    ) {
        match self.values.entry(key.inner) {
            Entry::Occupied(mut entry) => {
                // already declared, report error
                let declared = entry.get_mut();

                // get all spans
                let mut spans = match declared {
                    DeclaredValue::Once { value: _, span } => vec![*span],
                    DeclaredValue::Multiple { spans, err: _ } => std::mem::take(spans),
                    DeclaredValue::Error(_) => return,
                };

                // report error
                // TODO this creates O(n^2) lines of errors, ideally we only want to report the final O(n) one
                let title = match key.inner {
                    ScopeKey::Id(id) => {
                        let id_str = id.str(interner);
                        format!("identifier `{id_str}` declared multiple times")
                    }
                    ScopeKey::Slf(()) => "self declared multiple times".to_string(),
                };
                let mut diag = DiagnosticError::new(title, key.span, "declared again here");
                for span in &spans {
                    diag = diag.add_info(*span, "previously declared here");
                }
                let err = diag.report(diags);

                // insert error value into scope to avoid downstream errors
                //   caused by only considering the first declared value
                spans.push(key.span);
                *declared = DeclaredValue::Multiple { spans, err };
            }
            Entry::Vacant(entry) => {
                entry.insert(DeclaredValue::Once { value, span: key.span });
            }
        }
    }

    // TODO do we really need this?
    pub fn declare_already_checked(&mut self, id: Id, value: DeclaredValueSingle) {
        match self.values.entry(ScopeKey::Id(id)) {
            Entry::Occupied(_) => panic!("identifier `{:?}` already declared in scope {:?}", id, self.span),
            Entry::Vacant(entry) => {
                let declared = match value {
                    DeclaredValueSingle::Value { value, span } => DeclaredValue::Once { value: Ok(value), span },
                    DeclaredValueSingle::Error(err) => DeclaredValue::Error(err),
                };
                entry.insert(declared);
            }
        }
    }

    fn try_find(&self, key: ScopeKey<Id, ()>) -> DiagResult<Option<ScopeFound>> {
        if let Some(declared) = self.values.get(&key) {
            let (value, span_decl) = match *declared {
                DeclaredValue::Once { ref value, span } => (value.as_ref_ok()?, span),
                DeclaredValue::Multiple { spans: _, err } => return Err(err),
                DeclaredValue::Error(err) => return Err(err),
            };

            Ok(Some(ScopeFound {
                span_decl,
                value: value.clone(),
            }))
        } else {
            Ok(None)
        }
    }

    fn try_find_for_diagnostic(&self, key: ScopeKey<Id, ()>) -> DiagResult<Option<Span>> {
        let result = if let Some(value) = self.values.get(&key) {
            match value {
                &DeclaredValue::Once { value: _, span } => Some(span),
                DeclaredValue::Multiple { spans, err: _ } => Some(spans[0]),
                &DeclaredValue::Error(e) => return Err(e),
            }
        } else {
            None
        };
        Ok(result)
    }

    pub fn for_each_immediate_entry(&self, mut f: impl FnMut(ScopeKey<Id, ()>, DeclaredValueSingle<&ScopedEntry>)) {
        for (&k, v) in &self.values {
            let v = match *v {
                DeclaredValue::Once { ref value, span } => match value {
                    Ok(value) => DeclaredValueSingle::Value { span, value },
                    &Err(e) => DeclaredValueSingle::Error(e),
                },
                DeclaredValue::Multiple { spans: _, err } => DeclaredValueSingle::Error(err),
                DeclaredValue::Error(err) => DeclaredValueSingle::Error(err),
            };
            f(k, v)
        }
    }

    pub fn has_immediate_entry(&self, key: impl Into<ScopeKey<Id, ()>>) -> bool {
        self.values.contains_key(&key.into())
    }
}

impl<S: Clone> DeclaredValueSingle<&S> {
    pub fn cloned(&self) -> DeclaredValueSingle<S> {
        match *self {
            DeclaredValueSingle::Value { span, value } => {
                let value = value.clone();
                DeclaredValueSingle::Value { span, value }
            }
            DeclaredValueSingle::Error(e) => DeclaredValueSingle::Error(e),
        }
    }
}

fn error_not_found(
    interner: &Interner,
    initial_scope_span: Span,
    key: ScopeKey<Spanned<Id>, Span>,
    options: Vec<ScopeKey<Id, ()>>,
) -> DiagnosticError {
    let (title, span, hint) = match key {
        ScopeKey::Id(id) => {
            let id_str = id.inner.str(interner);
            let options_str = options.iter().filter_map(|id| match id {
                ScopeKey::Id(id) => Some(id.str(interner)),
                ScopeKey::Slf(_) => None,
            });
            let hint = hint_options_by_edit_distance(id_str, options_str, MAX_IDENTIFIER_SUGGESTIONS);
            (format!("undeclared identifier `{}`", id_str), id.span, hint)
        }
        ScopeKey::Slf(span) => ("self is not bound in this scope".to_string(), span, None),
    };

    let mut diag = DiagnosticError::new(title, span, "trying to access here").add_info(
        Span::empty_at(initial_scope_span.start()),
        "searched in the scope starting here and its parents",
    );
    if let Some(hint) = hint {
        diag = diag.add_footer_hint(hint);
    }
    diag
}

impl CaptureFailed {
    pub fn to_diag_error(self, span_decl: Span, span_capture: Span, span_use: Span) -> DiagnosticError {
        let reason = match self {
            CaptureFailed::NotCompile => "is not a compile-time value",
            CaptureFailed::NotFullyInitialized => "was not fully initialized",
        };
        DiagnosticError::new(
            format!("cannot access captured value because it {reason}"),
            span_use,
            "trying to access captured value here",
        )
        .add_info(span_decl, "value declared here")
        .add_info(span_capture, "value captured here")
    }
}

impl<I> ScopeKey<Spanned<I>, Span> {
    fn without_span(self) -> ScopeKey<I, ()> {
        match self {
            ScopeKey::Id(id) => ScopeKey::Id(id.inner),
            ScopeKey::Slf(_span) => ScopeKey::Slf(()),
        }
    }
}

impl<I, F> From<I> for ScopeKey<I, F> {
    fn from(id: I) -> Self {
        ScopeKey::Id(id)
    }
}

impl<S: HasSpan, F: HasSpan> HasSpan for ScopeKey<S, F> {
    fn span(&self) -> Span {
        match self {
            ScopeKey::Id(id) => id.span(),
            ScopeKey::Slf(span) => span.span(),
        }
    }
}
