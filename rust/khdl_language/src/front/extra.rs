use crate::front::block::ElaboratedForHeader;
use crate::front::compile::{CompileItemContext, CompileRefs};
use crate::front::diagnostic::DiagResult;
use crate::front::flow::Flow;
use crate::front::scope::{Scope, ScopeContent, ScopeParent, ScopedEntry};
use crate::syntax::ast::{ExtraList, ExtraListBlock, ExtraListItem, ForStatement, MaybeIdentifier};
use crate::syntax::pos::{HasSpan, Spanned};
use crate::util::intern::Id;

pub struct ExtraScope<'s, 'p> {
    root_scope: Option<&'p Scope<'p>>,
    scope: &'s mut Scope<'p>,
}

impl<'s, 'p> ExtraScope<'s, 'p> {
    pub fn as_scope(&mut self) -> &mut Scope<'p> {
        self.scope
    }

    pub fn new_child<'c, 'f>(&'f self, child_scope: &'c mut Scope<'f>) -> ExtraScope<'c, 'f> {
        ExtraScope {
            root_scope: Some(self.root_scope.unwrap_or(self.scope)),
            scope: child_scope,
        }
    }

    pub fn declare_root(
        &mut self,
        refs: CompileRefs,
        id: impl Into<MaybeIdentifier<Spanned<Id>>>,
        entry: DiagResult<ScopedEntry>,
    ) {
        let id = id.into();

        // slight code duplication to avoid redundant clone but respect order
        if let Some(root_scope) = self.root_scope {
            self.scope.declare(refs, id, entry.clone());
            root_scope.declare_non_mut(refs, id, entry);
        } else {
            self.scope.declare(refs, id, entry);
        }
    }
}

impl CompileItemContext<'_, '_> {
    pub fn elaborate_extra_list<'a, F: Flow, T>(
        &mut self,
        scope_parent: &mut Scope,
        flow: &mut F,
        list: &'a ExtraList<T>,
        common_decl_in_root_scope: bool,
        f: &mut impl FnMut(&mut Self, &mut ExtraScope, &mut F, &'a T) -> DiagResult,
    ) -> DiagResult {
        let ExtraList { span: _, items } = list;

        let scope_cursor = ExtraScope {
            root_scope: None,
            scope: scope_parent,
        };
        let mut cursor = ExtraCursor::new(scope_cursor, items, common_decl_in_root_scope);

        while let Some(()) = cursor.next(self, flow, &mut *f)? {}

        Ok(())
    }

    pub fn elaborate_extra_list_block<'a, F: Flow, T>(
        &mut self,
        scope_parent: &mut ExtraScope,
        flow: &mut F,
        block: &'a ExtraListBlock<T>,
        common_decl_in_root_scope: bool,
        f: &mut impl FnMut(&mut Self, &mut ExtraScope, &mut F, &'a T) -> DiagResult,
    ) -> DiagResult {
        let &ExtraListBlock { span, ref items } = block;

        let mut scope_cursor = scope_parent.scope.new_child(span);
        let scope_cursor = scope_parent.new_child(&mut scope_cursor);
        let mut cursor = ExtraCursor::new(scope_cursor, items, common_decl_in_root_scope);

        while let Some(()) = cursor.next(self, flow, &mut *f)? {}

        Ok(())
    }
}

pub struct ExtraCursor<'a, 's, 'p, T> {
    root_scope: ExtraScope<'s, 'p>,
    common_decl_in_root_scope: bool,
    stack_frames: Vec<Frame<'a, T>>,
    stack_scopes: Vec<Option<ScopeContent>>,
}

enum Frame<'a, T> {
    List {
        scopes_before: usize,
        items: std::slice::Iter<'a, ExtraListItem<T>>,
    },
    For {
        stmt: &'a ForStatement<ExtraListBlock<T>>,
        header: ElaboratedForHeader,
    },
}

enum FramePush<'a, T> {
    Block(Option<ScopeContent>, &'a ExtraListBlock<T>),
    For(&'a ForStatement<ExtraListBlock<T>>, ElaboratedForHeader),
}

impl<'a, 's, 'p, T> ExtraCursor<'a, 's, 'p, T> {
    pub fn new(root_scope: ExtraScope<'s, 'p>, list: &'a [ExtraListItem<T>], common_decl_in_root_scope: bool) -> Self {
        let frame = Frame::List {
            items: list.iter(),
            scopes_before: 0,
        };
        ExtraCursor {
            root_scope,
            common_decl_in_root_scope,
            stack_frames: vec![frame],
            stack_scopes: vec![],
        }
    }

    pub fn next<'c, 'h, R, F: Flow>(
        &mut self,
        ctx: &mut CompileItemContext<'c, 'h>,
        flow: &mut F,
        mut f: impl FnMut(&mut CompileItemContext<'c, 'h>, &mut ExtraScope, &mut F, &'a T) -> DiagResult<R>,
    ) -> DiagResult<Option<R>> {
        let refs = ctx.refs;

        loop {
            // get the top frame if any
            let Some(frame) = self.stack_frames.last_mut() else {
                return Ok(None);
            };

            match frame {
                Frame::List {
                    items,
                    scopes_before: _,
                } => {
                    // get next item if any
                    let item = match items.next() {
                        None => {
                            self.pop();
                            continue;
                        }
                        Some(item) => item,
                    };

                    // handle item
                    let (push, eval) = with_scope(&mut self.root_scope, &mut self.stack_scopes, |scope| match item {
                        ExtraListItem::Leaf(item) => {
                            let eval = f(ctx, scope, flow, item)?;
                            Ok((None, Some(eval)))
                        }
                        ExtraListItem::Declaration(decl) => {
                            let eval = ctx.eval_declaration(scope.scope, flow, decl)?;

                            if let Some(eval) = eval {
                                let id = eval.id;
                                let entry = eval.value_into_entry(refs, flow)?;

                                if self.common_decl_in_root_scope {
                                    scope.declare_root(refs, id, Ok(entry));
                                } else {
                                    scope.scope.declare(refs, id, Ok(entry));
                                }
                            }

                            Ok((None, None))
                        }
                        ExtraListItem::If(stmt) => {
                            let block = ctx.compile_if_statement_choose_block(scope.scope, flow, stmt)?;
                            let push = block.map(|block| FramePush::Block(None, block));
                            Ok((push, None))
                        }
                        ExtraListItem::Match(stmt) => {
                            let (declare, block) =
                                ctx.compile_match_statement_choose_branch(scope.scope, flow, stmt)?;

                            let mut scope_child = scope.scope.new_child(block.span);
                            if let Some(declare) = declare {
                                declare.declare(ctx, &mut scope_child, flow)?;
                            }

                            let push = Some(FramePush::Block(Some(scope_child.into_content()), block));
                            Ok((push, None))
                        }
                        ExtraListItem::For(stmt) => {
                            let header = ctx.elaborate_for_statement_header(scope.scope, flow, stmt)?;
                            let push = Some(FramePush::For(stmt, header));
                            Ok((push, None))
                        }
                    })?;

                    // handle results
                    match push {
                        None => {}
                        Some(FramePush::Block(scope_extra, block)) => self.push_block(scope_extra, block),
                        Some(FramePush::For(stmt, header)) => self.stack_frames.push(Frame::For { stmt, header }),
                    }
                    if let Some(eval) = eval {
                        return Ok(Some(eval));
                    }
                }
                Frame::For { stmt, header } => {
                    let stmt = &**stmt;
                    let ElaboratedForHeader {
                        index_id,
                        ref index_ty,
                        ref mut iter,
                    } = *header;

                    // get next value if any
                    let Some(index_value) = iter.next() else {
                        self.pop();
                        continue;
                    };
                    refs.check_should_stop(stmt.span_keyword)?;

                    // run iteration
                    let scope_iter = with_scope(&mut self.root_scope, &mut self.stack_scopes, |scope| {
                        let mut scope_iter = scope.scope.new_child(stmt.span());

                        ctx.elaborate_for_statement_iteration(
                            &mut scope_iter,
                            flow,
                            stmt,
                            index_id,
                            index_ty,
                            index_value,
                        )?;

                        Ok(scope_iter.into_content())
                    })?;

                    self.push_block(Some(scope_iter), &stmt.body);
                }
            }
        }
    }

    fn push_block(&mut self, scope_extra: Option<ScopeContent>, block: &'a ExtraListBlock<T>) {
        let &ExtraListBlock { span, ref items } = block;

        // remember how many scopes there were
        let scopes_before = self.stack_scopes.len();

        // optionally push the extra scope
        if let Some(scope_extra) = scope_extra {
            self.stack_scopes.push(Some(scope_extra));
        }
        // always push a new scope
        self.stack_scopes.push(Some(ScopeContent::new(span)));

        // actually push the frame
        self.stack_frames.push(Frame::List {
            items: items.iter(),
            scopes_before,
        });
    }

    fn pop(&mut self) {
        match self.stack_frames.pop().unwrap() {
            Frame::List {
                items: _,
                scopes_before,
            } => {
                self.stack_scopes.truncate(scopes_before);
            }
            Frame::For { stmt: _, header: _ } => {}
        }
    }
}

fn with_scope<R>(
    parent: &mut ExtraScope,
    stack: &mut Vec<Option<ScopeContent>>,
    f: impl FnOnce(&mut ExtraScope) -> R,
) -> R {
    fn with_scope_impl<'s, R>(
        parent: &mut ExtraScope,
        mut stack: impl Iterator<Item = &'s mut Option<ScopeContent>>,
        result: &mut Option<R>,
        f: impl FnOnce(&mut ExtraScope) -> R,
    ) {
        // get next item from stack if any
        let Some(next_slot) = stack.next() else {
            assert!(result.is_none());
            *result = Some(f(parent));
            return;
        };

        // restore scope from content
        let next_content = Option::take(next_slot).unwrap();
        let mut next_scope = Scope::restore_from_content(ScopeParent::Normal(parent.scope), next_content);

        // wrap in extra and recurse
        let mut next_extra = parent.new_child(&mut next_scope);
        with_scope_impl(&mut next_extra, stack, result, f);

        // restore scope content
        assert!(next_slot.is_none());
        *next_slot = Some(next_scope.into_content());
    }

    let mut result = None;
    with_scope_impl(parent, stack.iter_mut(), &mut result, f);
    result.unwrap()
}
