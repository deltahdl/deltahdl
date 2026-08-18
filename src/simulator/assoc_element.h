#pragma once

#include "common/types.h"

namespace delta {

struct Expr;
struct AssocArrayObject;
class SimContext;
class Arena;

// §7.8.7 — the value a newly allocated element of `aa` starts at. The
// user-specified initial value written as '{default:...} comes first, then the
// element type's own initial value (the member initializers of a packed
// struct), and failing both the uninitialized value for the element type: x
// for a 4-state element, 0 for a 2-state one.
//
// This is not the value a read of a nonexistent entry yields. Table 7-1 (see
// §7.4.5) gives that one, and it names only integral, real, string and handle
// types, so a struct element reads back as 'x or '0 whatever its members
// initialize to. AssocDefault in eval_select.cpp answers that question.
Logic4Vec AssocAllocValue(const AssocArrayObject* aa, Arena& arena);

// §7.8.7 — the stored element `sel` names, allocated with AssocAllocValue
// when the array holds no entry under that key. `sel` is a select whose base
// names an associative array; returns null when it is not one, and when the
// index expression contains an x or z bit, which §7.8.6 makes an invalid write
// rather than an allocation.
//
// The returned pointer is into the array's own map and is invalidated by any
// later insertion, so a caller writes through it before allocating again.
Logic4Vec* AssocEntryForWrite(const Expr* sel, SimContext& ctx, Arena& arena);

// §7.8.7 — writes `rhs_val` into the member `lhs` names of an associative
// array element, as in the subclause's own `b[2].x = 5`, allocating the
// element first so the members the write does not name hold the initial value
// the element type gives them. Returns false when `lhs` is not a member access
// on an element of an associative array of a packed struct.
bool TryWriteAssocMemberField(const Expr* lhs, const Logic4Vec& rhs_val,
                              SimContext& ctx, Arena& arena);

// §7.8.7 — reads the member `expr` names of an associative array element, so
// that `b[2].x` reads back what `b[2].x = 5` wrote. A nonexistent element is
// read, not allocated: the element value comes from the ordinary select path,
// which applies §7.8.6 and Table 7-1. Returns false when `expr` is not a
// member access on an element of an associative array of a packed struct.
bool TryEvalAssocMemberField(const Expr* expr, SimContext& ctx, Arena& arena,
                             Logic4Vec& out);

// §7.8.7 — writes the bit-select or part-select `lhs` names within an
// associative array element, as in `aa[3][7:0] = v`, allocating the element
// first. Returns false when `lhs` does not select within an element of an
// associative array.
bool TryWriteAssocElementBits(const Expr* lhs, const Logic4Vec& rhs_val,
                              SimContext& ctx, Arena& arena);

// §7.8.7 — allocates the element `lhs` names before the read a construct
// performing both a read and a write in one statement makes, so that an
// increment or a compound assignment sees the initial value the element is
// allocated with instead of Table 7-1's nonexistent-entry value. Does nothing
// when `lhs` does not name an associative array element, or when the entry
// already exists.
void AllocateAssocEntryForModify(const Expr* lhs, SimContext& ctx,
                                 Arena& arena);

}  // namespace delta
