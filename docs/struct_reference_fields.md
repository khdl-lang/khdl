# Reference fields in structs

A `ref` field binds a struct member to an existing variable, signal, or
interface. Construct it with an explicit reference; accessing the field then
accesses the target directly:

```kh
struct Slot(T: type) {
    ref value: T,
    ref occupied: bool,
    fn push(self, value: T) {
        assert(!self.occupied);
        self.value = value;
        self.occupied = true;
    }
}
```

For example, inside a clocked process:

```kh
reg r_value: uint(8) = undef;
reg r_occupied: bool = false;
val slot = Slot(uint(8)).new(value=ref(r_value), occupied=ref(r_occupied));
if (!slot.occupied) { slot.push(42); }
```

`ref name: T` stores the same binding as an ordinary field of type `Ref(T)`;
`ref channel: Channel(T)` stores a `RefInterface(Channel(T))` binding. The
`ref` modifier changes how field access works, not how constructors receive
arguments. Ordinary `name: Ref(T)` fields still need explicit `deref`.
Interface views are not supported as reference-field annotations.

Interface arrays use the same syntax: `ref channels: [3][2]Channel(T)` stores
a `RefInterface([3][2]Channel(T))` binding. Indexing and slicing the field selects
interfaces while preserving their shape and port view. Whole arrays and slices
can be forwarded with `ref(...)`, connected, or passed to module interface ports.
As with ordinary interface arrays, indices and slice starts must be compile-time
values; hardware selection of an interface is not supported.

Reads, writes, compound assignments, and further indexing operate on the
target. `ref(slot.value)` obtains a reference to the target again; it does not
refer to an internal struct storage slot. The same rules apply outside methods
and to copied or nested structs. Taking references to array elements retains
the existing reference-expression limitations.

An immutable wrapper can write through its fields, but cannot override the
target's own immutability, port directions, clock domain, or lifetime. Field
assignment never rebinds the reference. Copying a whole struct preserves its
aliases; assigning a replacement whole struct to a mutable wrapper replaces
its bindings. Reference fields are not hardware pointers and cannot be
selected dynamically in hardware or passed across module boundaries as
module parameters. Use normal interface ports between modules.

A field dereferences exactly one binding. For example, `ref pointer: Ref(T)`
denotes a variable that itself holds a reference; reading `object.pointer`
returns that reference and still needs `deref` to access its ultimate target.

Member projections on variables are deferred until the target is consumed.
Selector expressions (array indices, slice bounds, and generated field names)
are evaluated once, in source order, before the assignment's right-hand side.
For plain `=`, the target's reference fields are resolved after the right-hand
side. Thus, if the right-hand side replaces a wrapper, the assignment uses the
replacement wrapper's bindings:

```kh
struct Alias { ref value: uint(8) }
const {
    var x: uint(8) = 0;
    var y: uint(8) = 0;
    var alias = Alias.new(value=ref(x));
    alias.value = { alias = Alias.new(value=ref(y)); 5 };
    assert(x == 0 && y == 5);
}
```

A compound assignment resolves its reference fields before reading the left
side and retains those target identities while evaluating the right side.
Explicit `ref(...)` and `deref(...)` resolve when those expressions are evaluated;
`deref(ref(alias.value)) = ...` therefore captures the binding before the right
side. These rules also apply to fields beneath `any`, tuples, and arrays.

Struct field declarations remain constraints on every nested update, regardless
of the wrapper's declaration hint. See [assignment invariants](assignment_invariants.md)
for the update rule and its preservation argument.
