#pragma once

#include <cstdint>
#include <optional>
#include <string>
#include <vector>

#include "common/types.h"

namespace delta {

struct Expr;
struct Stmt;
class SimContext;
class Arena;

// §13.4.1: a nonvoid function call used as an expression is an implicit
// variable of the function's return type, so what applies to a variable of
// that type applies to the call: a member selected on a call returning a class
// handle, `n.self().v` or `n.mk(1).mk(2).v` (§8.6), a method called on it,
// `c.some_method(7).who()`, a method or an index applied to a call returning a
// queue, a dynamic array or a fixed-size unpacked array, `fq().size()` or
// `fa()[1]` (§7.10, §7.5, §7.4), and a member of a call returning a structure,
// `mk().a` (§7.2). None of these is denoted by a name -- the result exists
// once the call has run -- so the paths that resolve a member access, a method
// call or a select by the variable on its base side answer for none of them;
// the functions below evaluate the call instead and read or dispatch on what it
// returned.

// The elements the implicit variable of a call holds when the body returned a
// queue, a dynamic array or a fixed-size unpacked array, copied out of the
// callee's object before the callee's scope goes: a queue and a dynamic array
// are indexed from 0, and a fixed-size array from the bound its declaration
// gave it (§7.4.5), which `lo` and `is_descending` carry in the way
// ArrayInfo's do. The width and state of an element decide what an index the
// aggregate has no element at reads (Table 7-1 in §7.4.5).
struct ReturnedAggregate {
  std::vector<Logic4Vec> elements;
  uint32_t elem_width = 32;
  uint32_t lo = 0;
  bool is_descending = false;
  bool is_4state = true;
};

// A function body's registration for the aggregate it returns and for the tag
// of a tagged union value it returns: constructed by ExecFunctionBody for the
// body's whole run, so the `return` inside it has a record to fill and the
// completion of the body is what hands the record to the evaluation of the
// call, whichever call path ran the body.
class FunctionBodyResultScope {
 public:
  FunctionBodyResultScope();
  ~FunctionBodyResultScope();
  FunctionBodyResultScope(const FunctionBodyResultScope&) = delete;
  FunctionBodyResultScope& operator=(const FunctionBodyResultScope&) = delete;
};

// Records, for the innermost running body, the elements of the queue, dynamic
// array or fixed-size unpacked array `returned` names -- the expression of the
// `return` statement ExecFuncReturn is carrying out -- and records nothing for
// an expression naming no such aggregate, or while no evaluation below is
// asking for one.
void RecordReturnedAggregate(const Expr* returned, SimContext& ctx,
                             Arena& arena);

// Evaluates `expr` and answers its value; where `expr` is a call whose body
// returned an aggregate, `returned` holds that aggregate's elements, and it is
// empty otherwise -- for an expression that is no call, for a call the
// simulator answers without running a body (a DPI import, a built-in) and for
// a body that returned a vector, a string or a handle.
Logic4Vec EvalWithReturnedAggregate(const Expr* expr, SimContext& ctx,
                                    Arena& arena,
                                    std::optional<ReturnedAggregate>& returned);

// §7.3.2 with §13.4.1: a tagged union value carries its tag beside the member's
// bits, and a `return tagged M v` gives the implicit variable of the call
// that value, tag included. Records, for the innermost running body, the
// member `returned` -- the expression of the `return` ExecFuncReturn is
// carrying out -- names where it is a tagged union expression, and records
// nothing for another expression, or while no evaluation below is asking.
void RecordReturnedTag(const Expr* returned);

// §7.3.2 with §13.4.1: `return v` for a tagged union variable v gives the
// implicit variable of the call v's value, and that value is v's tag beside
// the member's bits -- the tag standing in the table under the key v's
// storage was created by (TagKeyOfName), never in the vector the return
// evaluates to. Records, for the innermost running body, that tag where
// `returned` -- the expression of the `return` ExecFuncReturn is carrying out
// -- is a bare identifier whose layout is a union and which holds a tag, and
// records nothing for another expression, for a union holding no tag, or
// while no evaluation below is asking.
void RecordReturnedVariableTag(const Expr* returned, SimContext& ctx);

// Evaluates `expr` and answers its value; where `expr` is a call whose body
// returned a tagged union expression, `tag` is the member that expression
// named, and it is empty otherwise -- for an expression that is no call, for
// a call the simulator answers without running a body and for a body that
// returned anything else.
Logic4Vec EvalWithReturnedTag(const Expr* expr, SimContext& ctx, Arena& arena,
                              std::string& tag);

// §7.3.2 with §13.4.1 and §11.9: the right-hand side of the blocking
// assignment `stmt`, evaluated with the target as its context as
// EvalRhsWithStructContext evaluates it, and, where the right-hand side is a
// call whose body returned a tagged union expression and the target is a
// tagged union variable named by a bare identifier, the target's tag set to
// the member that expression named, since the tag travels beside the bits
// the call hands back and no vector carries it. The tag stands under the key
// the target's storage was created by (TagKeyOfName), which a `u = tagged M
// v` writes and every member read of u checks against. Where the target is
// a member of a variable that is itself a tagged union, `s.u`, the member's
// tag is set under the variable's key followed by the member path, "s.u",
// from a `tagged M v` right-hand side or a call's returned tag alike, since
// the member store sees the bits alone. A call that returned anything else,
// and every other right-hand side, leaves the target's tag as it was. Shared
// by the procedural and the subroutine-body executors of the blocking
// assignment, which §10.4 gives one set of assignments.
Logic4Vec EvalRhsCarryingReturnedTag(const Stmt* stmt, SimContext& ctx,
                                     Arena& arena);

// Whether the member access `lhs`, `s.u` or `s.p.u`, names a tagged union
// member of a variable, and in `key` what that member's tag stands under: the
// key the variable's storage was created by (TagKeyOfName) followed by the
// member path, "s.u" for a top-level s and "m.s.u" for one inside instance m.
// False, with `key` unspecified, for a path a scope resolution starts, a
// member of a class object, a member no layout answers, and a member below a
// tagged union whose current tag is another member, whose write §11.9
// (printed page 304) has the store report. Shared by the blocking store
// above and the nonblocking one (statement_assign_nonblocking.cpp), which
// sets the same key when its update lands.
bool TaggedUnionMemberKey(const Expr* lhs, SimContext& ctx, std::string& key);

// The element at the declared index `idx` of `returned`, or what §7.4.5's
// Table 7-1 gives a read of a nonexistent element -- x for a 4-state element
// type, 0 for a 2-state one -- where the aggregate has none there.
Logic4Vec ElementOfReturnedAggregate(const ReturnedAggregate& returned,
                                     int64_t idx, Arena& arena);

// The property `expr->rhs` of the object the base side of the member access
// `expr` evaluates to, where that side is a method call or a member path that
// starts at one, or the member of the structure a call returned, its window
// read off the layout registered for the return type's name. False for any
// other base, and for a call that returned the null handle, which the
// remaining member-access paths answer as they did.
bool TryEvalCallResultMember(const Expr* expr, SimContext& ctx, Arena& arena,
                             Logic4Vec& out);

// The method call `expr`, `<call>.m(...)` or `<call>.p.m(...)`, run on the
// object its base side evaluates to, or `size()` answered for the queue or
// dynamic array a call returned (§7.10.2.1, §7.5.2). §8.20 dispatches a
// virtual method by the object's own type, which is the type the handle is
// read with here: the return type the call declares is a base of it at most
// (§8.20's covariant return), and a non-virtual method it shadows is not told
// apart. False for a base side that starts at no call, for a null result, for
// a method the object's class does not have and for a method other than
// size() on an aggregate.
bool TryEvalCallResultMethodCall(const Expr* expr, SimContext& ctx,
                                 Arena& arena, Logic4Vec& out);

}  // namespace delta
