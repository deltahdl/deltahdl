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

// §8.6 (printed page 183): `expr` as `a[i].f(...)`, the method `f` run on the
// object the element `a[i]` refers to, where `a` is a declared fixed-size or
// dynamic array of handles or a queue of them, declared or a property, and
// §7.4.2 (printed 153-154) and §7.10 (printed 169) make the element a handle
// like any other. Dispatched by the element's declared class where the
// array's declaration recorded one, as a call through a variable of that
// class is (§8.20), and by the object's own class for a queue property. The
// associative array's element is served by TryEvalAssocElementMethodCall
// (eval_assoc_class_handles.h), which asks this for every other container.
// False for a call of any other shape, one on a container whose elements are
// no handles, an element that refers to no object, or a method the object's
// class does not have. Before this the call had no dispatch: `arr[0].get()`
// read 0 and the task enable `arr[0].run();` ran nothing.
bool TryEvalElementObjectMethodCall(const Expr* expr, SimContext& ctx,
                                    Arena& arena, Logic4Vec& out);

}  // namespace delta
