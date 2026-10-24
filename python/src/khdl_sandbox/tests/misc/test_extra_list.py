import pytest

from khdl_sandbox.common.util import compile_custom, diag_error


def test_extra_list_in_interface():
    src = """
    interface foo(X: bool, Y: bool, Z: bool, V: bool) {
        if (X) { x: bool }
        if (Y) { y: bool }

        view view_0 {
            if (X) { x: in }
            if (Y) { y: out }

            // cause error
            if (Z) { z: out }
        }

        if (V) {
            // cause error
            view view_1 { d: out }
        }
    }
    """
    foo = compile_custom(src).resolve("top.foo")

    foo(X=False, Y=False, Z=False, V=False)
    foo(X=True, Y=False, Z=False, V=False)
    foo(X=False, Y=True, Z=False, V=False)

    with diag_error("port not found in this interface"):
        foo(X=False, Y=False, Z=True, V=False)
    with diag_error("port not found in this interface"):
        foo(X=False, Y=False, Z=False, V=True)


@pytest.mark.xfail
def test_extra_list_in_match():
    src = """
    fn f(c: bool, x: int) -> int {
        match (x) {
            if (c) {
                1 => { return 1; }
            }
            2 => { return 2; }
            _ => { return -x; }  
        }
    }
    """
    f = compile_custom(src).resolve("top.f")

    assert f(True, 1) == 1
    assert f(True, 2) == 2
    assert f(True, 3) == -3

    assert f(False, 1) == -1
    assert f(False, 2) == 2
    assert f(False, 3) == -3


def test_extra_list_in_module_ports():
    src = """
    module top(c: bool) ports(
        x0: in async bool,
        if (c) {
            y0: in async bool,
        }
        
        async {
            x1: in bool,
            if (c) {
                y1: in bool,
            }            
        }
        
        if (c) {
            async {
                y2: in bool,
            }
        }
    ) {
        comb {
            val _ = x0;
            val _ = x1;
            if (c) {
                val _ = y0;
                val _ = y1;
                val _ = y2;
            }
        }
    }
    """

    top = compile_custom(src).resolve("top.top")
    top(c=False)
    top(c=True)


def test_extra_list_in_module_instance():
    src = """
    module child ports(x: in async bool) {}
    module parent(c: bool) ports() {
        instance child ports(
            x=false,
            if (c) {
                y=true,
            }
        );
    }
    """
    parent = compile_custom(src).resolve("top.parent")

    parent(False)
    with diag_error("connection does not match any port"):
        parent(True)


def test_extra_list_in_params():
    src = """
    fn f(c: bool, if (c) { x: int }) -> int {
        if (c) {
            return x;
        } else {
            return 0;
        }
    }
    fn g(c: bool, d: bool, x: int) -> int {
        return f(c, if (d) { x=x });
    }
    """
    g = compile_custom(src).resolve("top.g")

    assert g(False, False, 0) == 0
    assert g(False, False, 1) == 0

    assert g(True, True, 0) == 0
    assert g(True, True, 1) == 1

    with diag_error("argument does not match any parameter"):
        assert g(False, True, 0) == 0
    with diag_error("missing argument for parameter `x`"):
        assert g(True, False, 0) == 0


def test_extra_list_params_conflict():
    src = "fn f(const c = false; c: bool) {}"
    f = compile_custom(src).resolve("top.f")
    with diag_error("identifier `c` declared multiple times"):
        f(c=False)


def test_extra_list_scopes():
    # TODO also test this for modules, where scopes are restored later
    # TODO test for loops
    src = """
    fn f(
        c: bool,
        d: bool,
        e: bool,
        
        // top-level scope is visible everywhere, including the function body
        const A = 4;
        
        if (c) {
            // branches have local, non-conflicting scopes
            const B = 4;
            b: uint(B),
            
            const C = 8;
        } else {
            const B = 2;
            b: uint(B),
        }
        
        // things declared in branches are visible in other branches and in the function body
        if (e) {
            const B = 4;
        }
        if (d) {
            const { print(C); } 
        }
    ) -> int {
        return A;
    }
    """
    f = compile_custom(src).resolve("top.f")

    # top-level visible
    assert f(c=True, d=False, e=False, b=0) == 4

    # branches local
    f(c=True, d=False, e=False, b=2 ** 4 - 1)
    f(c=True, d=False, e=False, b=2 ** 2 - 1)
    with diag_error("type mismatch"):
        f(c=False, d=False, e=False, b=2 ** 4 - 1)
    f(c=False, d=False, e=False, b=2 ** 2 - 1)

    # reuse
    with diag_error("identifier `B` declared multiple times"):
        f(c=True, d=False, e=True, b=0)

    # no leaking
    f(c=True, d=True, e=False, b=0)
    with diag_error("undeclared identifier `C`"):
        f(c=False, d=True, e=False, b=0)


def test_extra_item_kind_decl():
    src = """
    fn f(const x: int = 4;) -> int { return x; }
    """
    f = compile_custom(src).resolve("top.f")
    assert f() == 4


def test_extra_item_kind_if():
    src = """
    fn f(if (true) { x: int } else { y: int }) -> int { return x; }
    """
    f = compile_custom(src).resolve("top.f")
    assert f(x=4) == 4


def test_extra_item_kind_for():
    src = """
    fn f(for (i in 0..1) { x: int }) -> int { return x; }
    """
    f = compile_custom(src).resolve("top.f")
    assert f(x=4) == 4


def test_extra_item_kind_match():
    src = """
    fn f(match (0) { 0 => { x: int } }) -> int { return x; }
    """
    f = compile_custom(src).resolve("top.f")
    assert f(x=4) == 4


def test_extra_list_nested_scopes():
    src = """
    fn f(
        for (i in 0..3) {
            for (i in 0..2) {
                const { print(i); }
            }
            match (i) {
                2 => {
                    for (j in 0..2) {
                        if (j == 1) {
                            const C = i * 10 + j;
                            x: int(C..C+1),
                        }
                    }
                }
                val v => {
                    const { print(v); }
                }
            }
        }
    ) -> int {
        return x;
    }
    """
    f = compile_custom(src).resolve("top.f")
    assert f(x=21) == 21
    with diag_error("type mismatch"):
        f(x=20)


def test_extra_list_side_effects():
    src = """
    fn f() -> any {
        var array = [];
        var index = 0;
        var array_ref = ref(array);
        var index_ref = ref(index);
        fn effect(i: uint, v: any) -> any {
            deref(array_ref) = [*deref(array_ref), (i, deref(index_ref))];
            deref(index_ref) += 1;
            return v;
        }

        fn g(
            a: effect(2, int) = effect(3, 0),
            const { effect(4, 0); }
            for (i: effect(5, int) in effect(6, 0..2)) {
                if (effect(7, i == 0)) {
                    b: effect(8, int) = effect(9, 0),
                } else if (effect(10, false)) {
                } else {
                    match (effect(11, i)) {
                        1 => { c: effect(12, int) = effect(13, 0), }
                    }
                }
            }
        ) {}

        g(effect(0, 1), c=effect(1, 2));
        return array;
    }
    """
    f = compile_custom(src).resolve("top.f")
    expected = [0, 1, 2, 4, 5, 6, 7, 8, 9, 7, 10, 11, 12]
    assert f() == [(e, i) for i, e in enumerate(expected)]
