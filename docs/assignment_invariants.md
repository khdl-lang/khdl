# Assignment invariants

The declaration of a struct field constrains every value stored in that field.
This is independent of the declaration hint of a variable containing the struct.
An `any` annotation permits different kinds of values, including different
structs; it does not permit malformed instances of any particular struct.

There are three different pieces of information:

* A declaration hint constrains the permitted contents of a variable or field.
* The current value describes what is stored now, including the actual nominal
  identities beneath `any` and inside heterogeneous arrays.
* A hardware type determines a concrete representation and bounds the possible
  values of hardware expressions.

None can generally substitute for the others. In particular, the inferred type
of a current integer value is not a permanent write constraint. Unannotated
variables and structural components can change type. The union type of an array
can also lose its individual elements' nominal identities.

## Checked updates

Call a value well formed if its children are well formed and every nominal
struct field satisfies its declaration. Nominal enum payloads and hardware
values retain the contracts established by their respective constructors and
operations. References retain their invariant referent contract; following a
reference also checks its context and lifetime. Well-formedness does not mean
recursively traversing the reference graph.

Initial struct construction checks all field contracts. Type-preserving
conversions and checked bit decoding preserve well-formedness. Every subsequent
compile-time partial write goes through `TargetSteps::set_compile_value`.

The setter uses the constraint-propagation strategy from
[Karel's fix, e0264ac3](https://github.com/khdl-lang/khdl/commit/e0264ac34ae56e046483134b6bd0e65f419dcbe1).
It walks the actual target value while carrying an optional `expected_ty`:

* A struct-field step obtains the field's declaration from the actual struct's
  nominal identity and sets the carried constraint to that declaration.
* An array index, slice, or tuple index projects the carried constraint through
  the selector, if a constraint has been encountered.
* At the final destination, the setter checks the RHS against the carried
  constraint before replacing any payload. Slice assignments also check length.

Here `expected_ty` is an authoritative field contract, rather than an optional
variable hint or the inferred type of the current contents. For example,
`s.array[0]` in a struct with field `array: [3]uint(0..4)` checks the replacement
against `uint(0..4)`; it does not need to recompute the entire array's type.
Traversal through `s.value.pair.y`, where `value: any`, still encounters the
actual nested pair and discovers its `y` declaration. `any` does not stop the
value traversal or prevent later discovery of intrinsic nominal constraints.

The variable's declaration hint, if present, is checked separately by projecting
that declaration through the resolved target's selectors and checking the RHS.
These checks preserve both intrinsic nominal invariants and the root declaration
without rechecking the reconstructed root. Unconstrained structural components
retain their ability to change type.

The preservation argument is induction on the update path, starting with
well-formed target and RHS values:

1. An array or tuple selector projects its enclosing constraint onto the
   selected portion. Bounds and slice-length checks preserve aggregate shape.
   Unchanged portions retain their contracts.
2. A struct selector introduces the selected field's intrinsic declaration.
   Replacing the carried constraint here is sufficient because KHDL structs are
   nominal: the incoming constraint accepts either this exact struct identity
   or an unconstrained type such as `any`. There are no additional per-instance
   field refinements to lose.
3. The final replacement check establishes the selected portion's contract.
   Together with the unchanged portions, this preserves every enclosing
   aggregate's contract and well-formedness.
4. The separate projected root-declaration check preserves the variable's
   additional contract by the same argument.

Starting from checked construction, induction over successful updates therefore
preserves well-formedness. A nominal type comparison may rely on the struct tag
because mutation cannot invalidate the payload behind that tag. The final
payload write happens only after validation; a failed update cannot expose an
invalid intermediate value for a subsequent assignment to repair. Array
copy-on-write detachment during traversal does not change logical contents.

Hardware partial assignments check the RHS against the destination obtained from
the concrete hardware layout, including dynamic selectors and their bounds,
before emitting IR or performing unchecked representation conversions. Their
compile-time flow cache uses the same checked setter. This argument assumes the
compiler's primitive hardware operations have sound result types; explicitly
unsafe language operations retain their existing semantics.

## Copying and validation cost

The callers retain the root clone used by the previous assignment
implementation. Structs and tuples contain owned vectors, so cloning them
recursively copies their inline contents. Arrays use `Arc` and retain their
shared storage until an update calls `Arc::make_mut`; detaching an array clones
its element vector. Thus this representation does not provide general sharing
of untouched struct/tuple subtrees.

Constraint propagation adds selector/type projections and one final replacement
check, without reconstructing or rescanning enclosing fields for validation.
The cost of checking a composite RHS can still depend on that RHS's size. This
keeps the update's existing copying behavior while avoiding the extra parent
validation work of reconstruction-based checking.

Logical reference-field resolution also snapshots a variable receiver. It reuses
that snapshot while walking ordinary projections, restarting at reference
crossings. This avoids cloning the root once per named field, although it can
still add a root snapshot relative to assignments that needed no logical-field
resolution previously. Signal targets do not take this snapshot.

## Deferred logical fields

Building a variable target records its root identity and evaluated selector
values. It does not load that variable or force a signal's type. A plain
assignment can consequently initialize its receiver on its RHS:

```kh
struct Pair { x: bool, y: uint(0..4) }
const {
    var p;
    p.y = { p = Pair.new(x=false, y=0); 3 };
}
```

When a target is consumed, `LrValue::resolve_reference_fields` walks its logical
projections using the actual receiver's metadata. Reference fields redirect to
the referent's identity, without loading the referent. Physical signals cannot
contain reference bindings, so they retain ordinary deferred projections.
Reads, assignments, reference-taking, register declarations and interface
connections share this resolution operation. Already evaluated struct values
use the same logical projection helper.

For `=`, consume the target after the RHS. For a compound assignment, consume it
before reading the LHS and keep the resolved reference identities across the
RHS. Any ordinary path left within the resolved target is checked against its
current receiver at the store; a stale pre-RHS value cannot authorize a write
that violates its replacement's contracts.

An RHS expected type is only a suggestion derived from declarations, including
the logical type of a transparent field. Missing shape information gives `any`.
This suggestion neither reads the current receiver nor authorizes the eventual
write. In particular, unknown information is never interpreted as proof that a
field is ordinary.
