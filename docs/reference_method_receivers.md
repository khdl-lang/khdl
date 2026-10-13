# Reference method receivers

A method can borrow its caller's mutable variable instead of receiving a copy:

```kh
struct State {
    active: bool,
    fn begin(ref self) { self.active = true; }
    fn end(ref self) { self.active = false; }
    fn is_active(self) -> bool { return self.active; }
}

fn example() {
    var state = State.new(active=false);
    state.begin();
    assert(state.is_active());
    state.end();
}
```

`self` denotes the caller's object in a `ref self` method. Assignments are
immediately visible to the caller and through other aliases; there is no
copy-in/copy-out. Ordinary `self` methods keep their value semantics. A stored
ordinary bound method captures a snapshot; a stored reference bound method
retains the original variable and observes its state when called. The receiver's
lifetime, mutability, and current type are checked again at invocation.

The first implementation accepts only mutable whole variables, including
whole variables reached through `deref(reference)` or a transparent ref field.
It rejects temporary values such as `make().update()`, immutable receivers,
signal/port receivers, and targets with steps such as `items[i].update()` or
`outer.inner.update()`. It does not allocate a hidden temporary. Enum reference
methods are not supported yet. These restrictions leave stepped references and
temporary lifetimes for future extensions.

Helpers must receive references if they should modify the original object:

```kh
fn begin_state(state: any) { deref(state).begin(); }
// Within the caller:
// begin_state(ref(state));
```

Passing a struct by value still copies ordinary fields, even when its methods
use reference receivers. Existing transparent ref fields keep their aliasing
behavior. No exclusive-borrow rules are introduced; other aliases may still be
used while a bound method exists.

Receiver expressions are evaluated once. Method lookup retains an available
assignment target while discovering the receiver type, then chooses value or
reference binding. A function-produced receiver is evaluated normally and is
rejected if the selected method requires a reference target.

An existing assignment limitation remains: hardware-valued partial assignments
to structs containing references require the entire struct to have a hardware
representation and therefore fail. This also happens with direct field writes
outside methods. Pure hardware structs and compile-time bookkeeping alongside
reference fields work; runtime scratch fields in mixed structs need a separate
assignment extension. Reference receivers themselves add no register state or
backend operations.
