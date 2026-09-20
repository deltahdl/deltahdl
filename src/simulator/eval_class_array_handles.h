#pragma once

#include <string_view>

#include "common/types.h"

namespace delta {

struct Expr;
struct Stmt;
class SimContext;
class Arena;

// §7.4.2 lets an unpacked array be made of any data type and §8.5 puts no
// restriction on a property's type, so `Node kids[2]` is a property whose
// elements are class handles (§8.4), held on the object one by one as
// eval_class_array.h describes. These are the two operations a handle element
// has that a value element does not: it is written by constructing an object
// of the element's declared class, and a member is read through it.

// §8.4/§8.7: `stmt` as `a[i] = new`, `a[i] = new(args)` or §8.12's `a[i] =
// new src`, where `a` is an array property whose elements are class handles
// -- named bare in a method (§8.11), as `this.a` or through a handle. A bare
// `new` names no class of its own, so evaluating it as an expression
// constructs nothing; the element's declared class is what is constructed,
// and the handle is stored in the element. False where the target is no such
// select or the value no `new`. An index that addresses no element writes
// nothing (§7.4.6).
bool TryClassArrayElementNewAssign(const Stmt* stmt, SimContext& ctx,
                                   Arena& arena);

// §8.4/§7.4.2: `expr` as `a[i].v`, the property `v` of the object the element
// `a[i]` of an array property of class handles refers to, read into `out`.
// False for a member access of any other shape, one on an array property
// whose elements are no handles, or an element that refers to no object.
bool TryEvalClassArrayElementMember(const Expr* expr, SimContext& ctx,
                                    Arena& arena, Logic4Vec& out);

// §8.4/§8.12: the handle the `new` expression `rhs` yields for an element
// whose declared class is `class_type`: a shallow copy of the object `new src`
// names, else the object the class's constructor makes with the call's
// actuals. Shared with the associative array of handles
// (eval_assoc_class_handles.h), whose element is constructed the same way.
Logic4Vec ConstructElementObject(const Expr* rhs, std::string_view class_type,
                                 SimContext& ctx, Arena& arena);

// The member read through an element of a container of handles: a queue's
// (TryEvalQueueElementMember), an array property's, or a declared associative
// array's (TryEvalAssocElementMember), whichever the base of the select names.
// False where none answers.
bool TryEvalElementObjectMember(const Expr* expr, SimContext& ctx, Arena& arena,
                                Logic4Vec& out);

}  // namespace delta
