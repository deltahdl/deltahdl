#pragma once

#include "common/types.h"

namespace delta {

struct Expr;
struct Stmt;
class SimContext;
class Arena;

// §7.8 lets an associative array's element type be any type a fixed-size
// array may have, and §7.4.2 admits any data type there, so `C m[string]`
// declared in a module is a lookup table of class handles (§8.4): an element
// is written by constructing an object of the array's declared class and
// stores its handle, and a member or a method selected on the element applies
// to the object the handle refers to. The three below serve those forms for
// an array a module or a block declares under its bare name; the entries
// themselves live in the AssocArrayObject every other write and read of the
// array uses, and `m.num()` counts them as it did.

// §8.4/§8.7: `stmt` as `m[k] = new`, `m[k] = new(args)` or §8.12's `m[k] =
// new src`, where `m` is a declared associative array whose element type is
// a class. A bare `new` names no class of its own, so evaluating it as an
// expression constructs nothing; the array's declared element class is what
// is constructed, and the handle is stored under the key (§7.8, an entry
// allocated by being the target of an assignment). False where the target is
// no such select or the value no `new`. An index carrying an unknown bit
// writes nothing (§7.8.6).
bool TryAssocElementNewAssign(const Stmt* stmt, SimContext& ctx, Arena& arena);

// §8.4/§7.8: `expr` as `m[k].v`, the property `v` of the object the element
// `m[k]` of a declared associative array of class handles refers to, read
// into `out`. False for a member access of any other shape, one on an array
// whose elements are no handles, or an element that refers to no object.
bool TryEvalAssocElementMember(const Expr* expr, SimContext& ctx, Arena& arena,
                               Logic4Vec& out);

// §8.4/§7.8: `expr` as `m[k].f(...)`, the method `f` run on the object the
// element `m[k]` of a declared associative array of class handles refers to,
// dispatched by the array's declared element class as a call through a
// variable of that class is (§8.20). A call on an element of any other
// container of handles -- a declared fixed-size or dynamic array, a queue --
// is handed to TryEvalElementObjectMethodCall (eval_class_array_handles.h),
// so the one site the method-call evaluator asks (TryDispatchMethodOrLet in
// eval_function.cpp) serves every element. False for a call of any other
// shape, one on a container whose elements are no handles, an element that
// refers to no object, or a method the object's class does not have.
bool TryEvalAssocElementMethodCall(const Expr* expr, SimContext& ctx,
                                   Arena& arena, Logic4Vec& out);

}  // namespace delta
