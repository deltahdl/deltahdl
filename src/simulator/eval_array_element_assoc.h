#pragma once

namespace delta {

struct AssocArrayObject;
struct Expr;
class SimContext;
class Arena;

// §7.8 with §7.4 (printed pages 162 and 153): an associative array whose
// element type is an associative array, `int m[string][int]`, holds an
// associative array in each element, and `sel`, a select of one element of
// it, `m["a"]`, designates that element's array. The array is found in the
// one the base of `sel` designates (AssocArrayObject::int_element_assocs and
// str_element_assocs) and made the first time the element is reached. Null
// where the base designates no array whose elements are associative arrays,
// and where an integral index holds an x or z bit (§7.8.6).
//
// `allocate` says whether the element is being written, as a write to one of
// its own entries, `m["a"][1] = 41`, writes it. §7.8.7 allocates a missing
// entry when it is the target of a write, so with `allocate` the entry is
// made, and with it the element's array starts empty whatever a deleted entry
// of the key held. Read alone, a missing entry allocates nothing and is an
// empty array.
AssocArrayObject* ElementAssocOfSelect(const Expr* sel, SimContext& ctx,
                                       Arena& arena, bool allocate);

}  // namespace delta
