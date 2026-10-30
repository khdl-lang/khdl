use crate::front::compile::CompileItemContext;
use crate::front::diagnostic::{DiagResult, DiagnosticError, Diagnostics};
use crate::front::flow::FlowCompile;
use crate::front::item::{UniqueDeclaration, debug_info_name_including_params};
use crate::front::scope::Scope;
use crate::front::types::HardwareType;
use crate::front::value::CompileValue;
use crate::syntax::ast::{
    InterfaceListItem, InterfaceSignal, InterfaceView, ItemDefInterface, MaybeIdentifier, PortDirection,
};
use crate::syntax::parsed::AstRefInterface;
use crate::syntax::pos::{HasSpan, Spanned};
use crate::util::ResultDoubleExt;
use crate::util::intern::{Id, Interner};
use crate::util::iter::IterExt;
use indexmap::IndexMap;
use indexmap::map::Entry;
use itertools::Itertools;

#[derive(Debug)]
pub struct ElaboratedInterfaceInfo {
    pub id: MaybeIdentifier,
    pub debug_info_name: String,
    pub signals: IndexMap<Id, ElaboratedInterfaceSignalInfo>,
    pub views: IndexMap<Id, ElaboratedInterfaceViewInfo>,
}

impl ElaboratedInterfaceInfo {
    pub fn get_view(
        &self,
        diags: &Diagnostics,
        interner: &Interner,
        index: Spanned<Id>,
    ) -> DiagResult<(usize, &ElaboratedInterfaceViewInfo)> {
        match self.views.get_index_of(&index.inner) {
            None => {
                let title = format!("view `{}` not found in interface", index.inner.str(interner));
                let info = format!("interface `{}` declared here", self.debug_info_name);

                let footer = if self.views.is_empty() {
                    "this interface does not declare any views".to_owned()
                } else {
                    let available = self.views.keys().map(|id| format!("`{}`", id.str(interner))).join(", ");
                    format!("available views: {available}")
                };

                let diag = DiagnosticError::new(title, index.span, "unknown view used here")
                    .add_info(self.id.span(), info)
                    .add_footer_hint(footer)
                    .report(diags);
                Err(diag)
            }
            Some(index) => Ok((index, &self.views[index])),
        }
    }
}

#[derive(Debug)]
pub struct ElaboratedInterfaceSignalInfo {
    pub id: Spanned<Id>,
    pub ty: DiagResult<Spanned<HardwareType>>,
}

#[derive(Debug)]
pub struct ElaboratedInterfaceViewInfo {
    pub id: MaybeIdentifier<Spanned<Id>>,
    pub debug_info_name: String,
    pub port_dirs: DiagResult<Vec<(Spanned<Id>, Spanned<PortDirection>)>>,
}

struct InterfaceViewPartialElab {
    pub id: MaybeIdentifier<Spanned<Id>>,
    pub ports_dirs: Vec<(Spanned<Id>, Spanned<PortDirection>)>,
}

impl CompileItemContext<'_, '_> {
    pub fn elaborate_interface_new(
        &mut self,
        scope_params: &Scope,
        flow: &mut FlowCompile,
        unique: UniqueDeclaration,
        params: &Option<Vec<(Spanned<Id>, CompileValue)>>,
        ast_ref: AstRefInterface,
    ) -> DiagResult<ElaboratedInterfaceInfo> {
        let refs = self.refs;
        let diags = refs.diags;
        let elab = &refs.shared.elaboration_arenas;

        let &ItemDefInterface {
            span: _,
            vis: _,
            id: ref interface_id,
            params: _,
            span_body,
            ref body,
        } = &refs.fixed.parsed[ast_ref];

        // elaborate extra list, collect signal types and view directions immediately,
        //   then later actually whether the views signals match the actual signals
        let mut scope_body = scope_params.new_child(span_body);
        let mut signal_map = IndexMap::new();
        let mut views_partial: Vec<InterfaceViewPartialElab> = vec![];

        self.elaborate_extra_list(&mut scope_body, flow, body, true, &mut |slf, scope, flow, item| {
            match item {
                &InterfaceListItem::Signal(signal) => {
                    let InterfaceSignal {
                        id: signal_id,
                        ty: signal_ty,
                    } = signal;

                    let signal_id = slf.eval_id(scope.as_scope(), flow, signal_id)?;

                    let ty_eval = slf
                        .eval_expression_as_ty(scope.as_scope(), flow, signal_ty)
                        .and_then(|ty| match ty.inner.as_hardware_type(elab) {
                            Ok(ty_hw) => Ok(Spanned::new(ty.span, ty_hw)),
                            Err(_) => Err(diags.report_error_simple(
                                "interface signals must have hardware types",
                                ty.span,
                                format!("got non-hardware type `{}`", ty.inner.value_string(refs)),
                            )),
                        });

                    match signal_map.entry(signal_id.inner) {
                        Entry::Occupied(mut entry) => {
                            let prev: &mut ElaboratedInterfaceSignalInfo = entry.get_mut();
                            let signal_str = signal_id.inner.str(&refs.shared.interner);
                            let e = DiagnosticError::new(
                                "signal declared twice",
                                signal_id.span(),
                                format!("signal `{signal_str}` redeclared here"),
                            )
                            .add_info(prev.id.span, format!("signal `{signal_str}` previously declared here"))
                            .report(diags);
                            prev.ty = Err(e);
                        }
                        Entry::Vacant(entry) => {
                            entry.insert(ElaboratedInterfaceSignalInfo {
                                id: signal_id,
                                ty: ty_eval,
                            });
                        }
                    }
                }
                InterfaceListItem::View(view) => {
                    let &InterfaceView {
                        span: _,
                        id: view_id,
                        ref port_dirs,
                    } = view;

                    let view_id = slf.eval_maybe_id(scope.as_scope(), flow, view_id)?;

                    let mut port_dirs_partial = vec![];
                    slf.elaborate_extra_list(
                        scope.as_scope(),
                        flow,
                        port_dirs,
                        true,
                        &mut |slf, scope, flow, port| {
                            let (port_id, port_dir) = port.inner;
                            let port_id = slf.eval_id(scope.as_scope(), flow, port_id)?;
                            port_dirs_partial.push((port_id, port_dir));
                            Ok(())
                        },
                    )?;

                    views_partial.push(InterfaceViewPartialElab {
                        id: view_id,
                        ports_dirs: port_dirs_partial,
                    });
                }
            }

            Ok(())
        })?;

        // check views
        let mut view_map: IndexMap<Id, ElaboratedInterfaceViewInfo> = IndexMap::new();
        for view in views_partial {
            let InterfaceViewPartialElab {
                id: view_id,
                ports_dirs,
            } = view;

            let mut port_dir_vec: Vec<Option<DiagResult<(Spanned<Id>, Spanned<PortDirection>)>>> =
                vec![None; signal_map.len()];
            let mut any_view_err = Ok(());

            for (port_id, port_dir) in ports_dirs {
                if let Some(port_index) = signal_map.get_index_of(&port_id.inner) {
                    let slot = &mut port_dir_vec[port_index];
                    if let Some(prev) = &*slot {
                        if let Ok((prev_id, _)) = prev {
                            let port_str = port_id.inner.str(&refs.shared.interner);
                            let e = DiagnosticError::new(
                                "port direction set twice",
                                port_id.span(),
                                format!("direction of port `{port_str}` set again here"),
                            )
                            .add_info(
                                prev_id.span(),
                                format!("direction of port `{port_str}` previously set here"),
                            )
                            .report(diags);
                            *slot = Some(Err(e));
                        }
                    } else {
                        *slot = Some(Ok((port_id, port_dir)));
                    }
                } else {
                    let port_str = port_id.inner.str(&refs.shared.interner);
                    any_view_err = Err(diags.report_error_simple(
                        "port not found in this interface",
                        port_id.span(),
                        format!("attempt to set direction of unknown port `{port_str}` here"),
                    ));
                }
            }

            let port_dir_vec = any_view_err.and_then(|()| {
                port_dir_vec
                    .into_iter()
                    .enumerate()
                    .map(|(port_index, dir)| {
                        dir.ok_or_else(|| {
                            let port_info = &signal_map[port_index];
                            let port_str = port_info.id.inner.str(&refs.shared.interner);
                            DiagnosticError::new(
                                format!("missing direction for port `{port_str}`"),
                                interface_id.span(),
                                "this interface does not set a direction for this port",
                            )
                            .add_info(port_info.id.span(), "port declared here")
                            .report(diags)
                        })
                        .flatten_err()
                    })
                    .try_collect_all_vec()
            });

            let debug_info_name = view_id
                .spanned_string(&refs.shared.interner)
                .inner
                .unwrap_or_else(|| "_".to_owned());
            let view_eval = ElaboratedInterfaceViewInfo {
                id: view_id,
                debug_info_name,
                port_dirs: port_dir_vec,
            };
            if let MaybeIdentifier::Identifier(view_id) = &view_id {
                let view_str = view_id.inner.str(&refs.shared.interner);
                if let Some(prev) = signal_map.get(&view_id.inner) {
                    let _ = DiagnosticError::new(
                        "view name conflicts with port name",
                        view_id.span,
                        format!("view `{view_str}` declared here"),
                    )
                    .add_info(prev.id.span(), format!("port `{view_str}` declared here"))
                    .report(diags);
                }

                match view_map.entry(view_id.inner) {
                    Entry::Occupied(mut entry) => {
                        let e = DiagnosticError::new(
                            "view name already declared",
                            view_id.span,
                            format!("view `{view_str}` redeclared here"),
                        )
                        .add_info(
                            entry.get().id.span(),
                            format!("view `{view_str}` previously declared here"),
                        )
                        .report(diags);
                        entry.get_mut().port_dirs = Err(e);
                    }
                    Entry::Vacant(entry) => {
                        entry.insert(view_eval);
                    }
                }
            }
        }

        let debug_info_name = debug_info_name_including_params(refs, &unique, params);

        Ok(ElaboratedInterfaceInfo {
            id: *interface_id,
            debug_info_name,
            signals: signal_map,
            views: view_map,
        })
    }
}
