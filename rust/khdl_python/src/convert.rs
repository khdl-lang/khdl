use crate::{Compile, EnumValue, Module, Range, StructValue, Value};
use itertools::Itertools;
use khdl_language::front::function::EvaluatedArgs;
use khdl_language::front::implication::ValueWithImplications;
use khdl_language::front::types::Type as RustType;
use khdl_language::front::value::{CompileCompoundValue, CompileValue, SimpleCompileValue, Value as RustValue};
use khdl_language::syntax::ast::Arg;
use khdl_language::syntax::pos::{Span, Spanned};
use khdl_language::util::big_int::BigInt;
use khdl_language::util::intern::Interner;
use khdl_language::util::range::Range as RustRange;
use khdl_language::util::range_multi::MultiRange;
use khdl_util::constants::KHDL_LANGUAGE_NAME;
use pyo3::exceptions::{PyException, PyValueError};
use pyo3::types::{PyAnyMethods, PyBool, PyDict, PyInt, PyList, PyTuple, PyTupleMethods, PyType};
use pyo3::{Bound, IntoPyObjectExt, Py, PyAny, PyClassInitializer, PyRef, PyResult, Python};
use std::sync::Arc;

pub fn compile_value_to_py(py: Python, state: &Py<Compile>, value: &CompileValue) -> PyResult<Py<PyAny>> {
    let fallback = || {
        Value {
            compile: state.clone_ref(py),
            value: value.clone(),
        }
        .into_py_any(py)
    };

    match value {
        CompileValue::Simple(value) => match value {
            SimpleCompileValue::Bool(x) => x.into_py_any(py),
            SimpleCompileValue::Int(x) => x.clone().into_num_bigint().into_py_any(py),
            SimpleCompileValue::Array(x) => {
                let items: Vec<_> = x
                    .iter()
                    .map(|item| compile_value_to_py(py, state, item))
                    .try_collect()?;
                items.into_py_any(py)
            }
            &SimpleCompileValue::Module(m) => {
                let init = PyClassInitializer::from(Value {
                    compile: state.clone_ref(py),
                    value: RustValue::Simple(SimpleCompileValue::Module(m)),
                })
                .add_subclass(Module { module: m });
                Py::new(py, init).map(Py::into_any)
            }
            SimpleCompileValue::Type(_)
            | SimpleCompileValue::Function(_)
            | SimpleCompileValue::Interface(_)
            | SimpleCompileValue::InterfaceArray(_, _)
            | SimpleCompileValue::InterfaceView(_)
            | SimpleCompileValue::InterfaceViewArray(_, _)
            | SimpleCompileValue::Reference(_)
            | SimpleCompileValue::Package(_) => fallback(),
        },
        CompileValue::Compound(value) => match value {
            CompileCompoundValue::String(x) => x.as_str().into_py_any(py),
            CompileCompoundValue::Range(x) => Range { range: x.clone() }.into_py_any(py),
            CompileCompoundValue::Tuple(x) => {
                let items: Vec<_> = x
                    .iter()
                    .map(|item| compile_value_to_py(py, state, item))
                    .try_collect()?;
                PyTuple::new(py, items)?.into_py_any(py)
            }
            CompileCompoundValue::Struct(x) => {
                let init = PyClassInitializer::from(Value {
                    compile: state.clone_ref(py),
                    value: RustValue::Compound(value.clone()),
                })
                .add_subclass(StructValue { value: x.clone() });
                Py::new(py, init).map(Py::into_any)
            }
            CompileCompoundValue::Enum(x) => {
                let init = PyClassInitializer::from(Value {
                    compile: state.clone_ref(py),
                    value: RustValue::Compound(value.clone()),
                })
                .add_subclass(EnumValue { value: x.clone() });
                Py::new(py, init).map(Py::into_any)
            }
            CompileCompoundValue::BoundMethod(_) => fallback(),
        },
        CompileValue::Hardware(n) => n.unreachable(),
    }
}

pub fn compile_value_from_py(value: &Bound<PyAny>, expected_compile: Option<&Py<Compile>>) -> PyResult<CompileValue> {
    let py = value.py();

    // TODO should we use downcast or extract here?
    //   https://pyo3.rs/v0.22.3/performance#extract-versus-downcast
    // unwrap our own python wrappers
    if let Ok(value) = value.extract::<PyRef<Value>>() {
        check_same_compile_context(expected_compile, &value.compile, py)?;
        return Ok(value.value.clone());
    }
    if let Ok(value) = value.extract::<PyRef<Range>>() {
        return Ok(CompileValue::Compound(CompileCompoundValue::Range(value.range.clone())));
    }
    if let Ok(module) = value.extract::<PyRef<Module>>() {
        check_same_compile_context(expected_compile, &module.as_super().compile, py)?;
        return Ok(CompileValue::Simple(SimpleCompileValue::Module(module.module)));
    }

    // convert some python values with obvious equivalents
    if let Ok(value) = value.extract::<bool>() {
        return Ok(CompileValue::new_bool(value));
    }
    if let Ok(value) = value.extract::<num_bigint::BigInt>() {
        return Ok(CompileValue::new_int(BigInt::from_num_bigint(value)));
    }
    if let Ok(value) = value.extract::<String>() {
        return Ok(CompileValue::Compound(CompileCompoundValue::String(Arc::new(value))));
    }
    if let Ok(value) = value.cast::<PyTuple>() {
        let items: Vec<_> = value
            .iter()
            .map(|v| compile_value_from_py(&v, expected_compile))
            .try_collect()?;
        return Ok(CompileValue::Compound(CompileCompoundValue::Tuple(items)));
    }
    if let Ok(value) = value.cast::<PyList>() {
        let items: Vec<_> = value
            .into_iter()
            .map(|v| compile_value_from_py(&v, expected_compile))
            .try_collect()?;
        return Ok(CompileValue::Simple(SimpleCompileValue::Array(Arc::new(items))));
    }

    // convert some python types with obvious equivalents
    if let Ok(py_type) = value.cast::<PyType>() {
        if py_type.is(py.get_type::<PyBool>()) {
            return Ok(CompileValue::new_ty(RustType::Bool));
        }
        if py_type.is(py.get_type::<PyInt>()) {
            return Ok(CompileValue::new_ty(RustType::Int(MultiRange::from(RustRange::OPEN))));
        }
        if py_type.is(py.get_type::<PyAny>()) {
            return Ok(CompileValue::new_ty(RustType::Any));
        }
    }

    Err(PyException::new_err(format!(
        "cannot convert value of type `{}` to {} value",
        value.get_type(),
        KHDL_LANGUAGE_NAME,
    )))
}

fn check_same_compile_context(expected: Option<&Py<Compile>>, actual: &Py<Compile>, py: Python) -> PyResult<()> {
    if let Some(expected_compile) = expected {
        if !actual.bind(py).is(expected_compile.bind(py)) {
            return Err(PyValueError::new_err(
                "cannot mix values from different Compile instances",
            ));
        }
    }
    Ok(())
}

pub fn convert_python_args_and_kwargs_to_args(
    compile: &Py<Compile>,
    interner: &Interner,
    args: &Bound<'_, PyTuple>,
    kwargs: Option<&Bound<'_, PyDict>>,
    dummy_span: Span,
) -> PyResult<EvaluatedArgs> {
    let mut args_inner = vec![];
    for value in args {
        let value = compile_value_from_py(&value, Some(compile))?;
        args_inner.push(Arg {
            span: dummy_span,
            id: None,
            value: Spanned::new(dummy_span, ValueWithImplications::from(value)),
        });
    }
    if let Some(kwargs) = kwargs {
        for (name, value) in kwargs {
            let name = name.extract::<String>()?;
            let id = interner.push(&name);

            let value = compile_value_from_py(&value, Some(compile))?;

            args_inner.push(Arg {
                span: dummy_span,
                id: Some(Spanned::new(dummy_span, id)),
                value: Spanned::new(dummy_span, ValueWithImplications::from(value)),
            });
        }
    }

    Ok(EvaluatedArgs {
        span: dummy_span,
        inner: args_inner.into_iter(),
    })
}
