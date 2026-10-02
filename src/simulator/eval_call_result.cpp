#include "simulator/eval_call_result.h"

#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/types.h"
#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/covergroup_instance.h"
#include "simulator/eval_array_class_queue.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/eval_function_hier.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/struct_string_member.h"

namespace delta {

namespace {

// Whether `expr` selects a named member, `.m`, the dot no package's scope
// resolution.
bool SelectsNamedMember(const Expr* expr) {
  return expr != nullptr && expr->kind == ExprKind::kMemberAccess &&
         !expr->is_scope_resolution && expr->rhs != nullptr &&
         expr->rhs->kind == ExprKind::kIdentifier;
}

// A.8.4: a system function call is a primary a method is called on as a
// subroutine call is, `$sformatf("%s", s).len()`.
bool IsCall(const Expr* expr) {
  return expr->kind == ExprKind::kCall || expr->kind == ExprKind::kSystemCall;
}

// Whether `side`, the handle side of a member access, is a method call or a
// member path down from one, `f()` or `f().p.q`: the object it denotes is the
// one the call returned, which no name resolves. A path from a name is left to
// the resolvers that own it, and a select on the way to the element paths.
bool RootedAtCall(const Expr* side) {
  if (side == nullptr) return false;
  if (IsCall(side)) return true;
  return SelectsNamedMember(side) && RootedAtCall(side->lhs);
}

// Whether `expr` selects a named member, `.m`, of something RootedAtCall.
bool SelectsMemberOfCallResult(const Expr* expr) {
  return SelectsNamedMember(expr) && RootedAtCall(expr->lhs);
}

// The call a method call's receiver starts at, through the members it selects
// and the elements it indexes: `pk()` of `pk()`, `pk().kid` and `pk().a[1]`.
// Null where the receiver starts at anything else, a name among them.
const Expr* CallReceiverStartsAt(const Expr* side) {
  while (side != nullptr && !IsCall(side)) {
    if (SelectsNamedMember(side)) {
      side = side->lhs;
    } else if (side->kind == ExprKind::kSelect && side->index != nullptr) {
      side = side->base;
    } else {
      return nullptr;
    }
  }
  return side;
}

// The method `name` of `obj` by the object's own type: a virtual one through
// the vtable (§8.20), else the one the class or a base of it declares.
ModuleItem* ResolveMethodOnObject(const ClassObject* obj, std::string_view name,
                                  const ClassTypeInfo** owner) {
  ModuleItem* method = obj->ResolveVirtualMethod(name, owner);
  if (method == nullptr)
    method = obj->ResolveMethodForType(name, obj->type, owner);
  return method;
}

// §13.4.1's implicit variable for an aggregate return type has no storage of
// its own: EvalFunctionCall and ExecClassMethod create it one element wide,
// and a `return q` copies that variable's value, not q's elements, so the
// elements a call returned reached the caller by no path at all. The callee's
// queue or array lives in the callee's scope and goes with it, so the copy has
// to be taken while the body runs, at the `return`, and handed over once the
// call machinery has unwound. This register is that handover: one record per
// running body, innermost last, which the body's `return` fills, and the
// record the body that completed last left, which the evaluation that ran the
// call takes. It is asked for only while such an evaluation is in progress,
// so `x = fq()` copies nothing it did not before.
//
// The evaluation that ran the call is what takes the record because a body's
// completion is the last thing the call does before its value comes back: the
// bodies of the call's arguments and of the calls the body makes each complete
// earlier and are overwritten, and a call answered without a body -- a DPI
// import, a built-in -- completes none, which the reset before the call
// leaves as no record.
//
// §7.3.2 (printed page 151) has a tagged union value carry its tag beside
// the member's bits, and the tag a `return tagged M v` gives the implicit
// variable (§13.4.1, printed 342) reaches the caller by the same handover:
// the value comes back as a vector, which holds no tag, and the callee's
// variable, whose tag table entry would, goes with the callee's scope.
struct ReturnedRecord {
  std::optional<ReturnedAggregate> aggregate;
  std::string tag;
};

struct ReturnedAggregateRegister {
  std::vector<ReturnedRecord> bodies;
  ReturnedRecord completed;
  int evaluations = 0;
  // The base a CallResultReceiverScope holds, and the aggregate its call
  // returned.
  const Expr* held_base = nullptr;
  std::optional<ReturnedAggregate> held_aggregate;
};

// One register per thread, as eval_let.cpp keeps its expansion set: a body
// never suspends (§13.4 lets a function consume no time), so the stack is
// the running thread's own and needs no lock.
ReturnedAggregateRegister& Register() {
  static thread_local ReturnedAggregateRegister reg;
  return reg;
}

// The queue, dynamic array or fixed-size unpacked array `returned` names,
// its elements copied so the record outlives the callee's storage. A fixed
// array of more than one unpacked dimension has no element list of the shape
// a single index reads, so it records nothing, as does a name that is no
// aggregate.
std::optional<ReturnedAggregate> CaptureAggregate(const Expr* returned,
                                                  SimContext& ctx,
                                                  Arena& arena) {
  if (returned == nullptr || (returned->kind != ExprKind::kIdentifier &&
                              returned->kind != ExprKind::kMemberAccess)) {
    return std::nullopt;
  }
  ReturnedAggregate agg;
  if (const QueueObject* q = FindQueueOfBase(returned, ctx, arena)) {
    agg.elem_width = q->elem_width;
    agg.is_4state = q->is_4state;
  } else {
    if (returned->kind != ExprKind::kIdentifier) return std::nullopt;
    const ArrayInfo* info = ctx.FindArrayInfo(returned->text);
    if (info == nullptr || info->is_dynamic || info->is_queue ||
        info->dim_los.size() > 1) {
      return std::nullopt;
    }
    agg.elem_width = info->elem_width;
    agg.is_4state = info->is_4state;
    agg.lo = info->lo;
    agg.is_descending = info->is_descending;
  }
  CollectQueueElements(returned, ctx, arena, agg.elements);
  for (auto& elem : agg.elements) elem = OwnRhsWords(elem, arena);
  if (returned->kind == ExprKind::kIdentifier)
    agg.elem_layout = StructLayoutOfName(returned->text, ctx);
  return agg;
}

// §7.2 with §13.4.1: the layout of the structure the call `call` returns,
// registered under the return type's name, or null where the call names no
// declared function or its return type is no named structure.
const StructTypeInfo* CallResultStructLayout(const Expr* call, SimContext& ctx,
                                             Arena& arena) {
  if (call->kind != ExprKind::kCall) return nullptr;
  const ModuleItem* func = FindSubroutineTarget(call, ctx, arena).func;
  if (func == nullptr || func->return_type.type_name.empty()) return nullptr;
  return ctx.FindStructType(func->return_type.type_name);
}

// §7.2: the member `expr->rhs` of the structure `value` laid out by
// `layout`, its window read off the layout, and §6.11.2 converting the
// unknowns of a 2-state member's window to zeros as a read of the member of a
// variable does. False where there is no layout or it has no such member.
bool ReadLayoutMember(const StructTypeInfo* layout, const Expr* expr,
                      const Logic4Vec& value, Arena& arena, Logic4Vec& out) {
  if (layout == nullptr) return false;
  uint32_t bit_offset = 0;
  uint32_t width = 0;
  DataTypeKind kind = DataTypeKind::kLogic;
  if (!ResolveStructFieldPath(layout, expr->rhs->text, &bit_offset, &width,
                              &kind)) {
    return false;
  }
  out = ExtractBitField(arena, value, bit_offset, width);
  // §7.2 with §6.16: a string member's bits are a handle to its text.
  if (kind == DataTypeKind::kString) {
    out = StringMemberText(out, arena);
    return true;
  }
  if (!Is4stateType(kind)) CoerceTo2State(out);
  return true;
}

// §7.2: the member `expr->rhs` of the structure `value` the call `expr->lhs`
// returned. False where the call returns no named structure or the layout
// has no such member.
bool TryStructResultMember(const Expr* expr, const Logic4Vec& value,
                           SimContext& ctx, Arena& arena, Logic4Vec& out) {
  return ReadLayoutMember(CallResultStructLayout(expr->lhs, ctx, arena), expr,
                          value, arena, out);
}

// Whether `e` is a name or a chain of member selects of names, `h` or `d.c`,
// which evaluates to the object it names and runs nothing.
bool IsHandleNamePath(const Expr* e) {
  if (e == nullptr) return false;
  if (e->kind == ExprKind::kIdentifier) return true;
  return e->kind == ExprKind::kMemberAccess && !e->is_scope_resolution &&
         e->rhs != nullptr && e->rhs->kind == ExprKind::kIdentifier &&
         IsHandleNamePath(e->lhs);
}

// Whether the call `call` runs the body of a declared subroutine: a module's
// (FindSubroutineTarget), a method called through a handle a name path holds,
// `k.get()`, or one of the running method's object called bare, `get()` --
// and not an array method, `q.find(x) with (x > 1)`, or a built-in one.
bool CallsDeclaredSubroutine(const Expr* call, SimContext& ctx, Arena& arena) {
  if (FindSubroutineTarget(call, ctx, arena).func != nullptr) return true;
  const ClassTypeInfo* owner = nullptr;
  const Expr* access = call->lhs;
  if (access != nullptr && access->kind == ExprKind::kMemberAccess &&
      !access->is_scope_resolution && access->rhs != nullptr &&
      access->rhs->kind == ExprKind::kIdentifier &&
      IsHandleNamePath(access->lhs)) {
    const ClassObject* obj =
        ctx.GetClassObject(EvalExpr(access->lhs, ctx, arena).ToUint64());
    return obj != nullptr &&
           ResolveMethodOnObject(obj, access->rhs->text, &owner) != nullptr;
  }
  // A bare call names its callee by its own text or by an identifier callee.
  std::string_view bare = access == nullptr ? std::string_view(call->text)
                          : access->kind == ExprKind::kIdentifier
                              ? std::string_view(access->text)
                              : std::string_view{};
  const ClassObject* self = ctx.CurrentThis();
  return self != nullptr && !bare.empty() &&
         ResolveMethodOnObject(self, bare, &owner) != nullptr;
}

// §7.2 with §7.4.5, §7.12.1 and §13.4.1: the layout of an element of the
// array the call `call` returns -- a declared function's, registered under
// its return type's name, or an array method's, `sq.find(i) with (...)`,
// whose result holds the elements of the array it is called on, laid out by
// that array's element type. Null where neither answers.
const StructTypeInfo* ElementLayoutOfCall(const Expr* call, SimContext& ctx,
                                          Arena& arena) {
  if (const StructTypeInfo* layout = CallResultStructLayout(call, ctx, arena))
    return layout;
  const Expr* access = call->lhs;
  if (access == nullptr || access->kind != ExprKind::kMemberAccess ||
      access->is_scope_resolution || access->lhs == nullptr ||
      access->lhs->kind != ExprKind::kIdentifier)
    return nullptr;
  return StructLayoutOfName(access->lhs->text, ctx);
}

// §7.2 with §7.4.5: `mk()[1].y` and `sq.find(i) with (i.x == 3) [0].y` read
// the member of the structure the element select of an array-valued call
// yields. The select on the call is evaluated as it is alone, `e = mk()[1]`,
// and its member read off the element type's layout; left to the paths that
// read a member through a named array's layout, it read 0.
bool TryElementOfCallResultMember(const Expr* expr, SimContext& ctx,
                                  Arena& arena, Logic4Vec& out) {
  const Expr* sel = expr->lhs;
  if (expr->is_scope_resolution || expr->rhs == nullptr ||
      expr->rhs->kind != ExprKind::kIdentifier || sel == nullptr ||
      sel->kind != ExprKind::kSelect || sel->index_end != nullptr ||
      sel->base == nullptr || sel->base->kind != ExprKind::kCall)
    return false;
  if (const StructTypeInfo* layout = ElementLayoutOfCall(sel->base, ctx, arena))
    return ReadLayoutMember(layout, expr, EvalExpr(sel, ctx, arena), arena,
                            out);
  // §13.4.1: a declared function's return type named by a typedef the run
  // records no layout under -- a module's `typedef s_t q_t[$]` -- lays its
  // elements out as the variable the body returned does. The call runs once
  // here, and a result with no such layout reads as the element of no layout
  // read 0 before.
  if (!CallsDeclaredSubroutine(sel->base, ctx, arena)) return false;
  std::optional<ReturnedAggregate> returned;
  EvalWithReturnedAggregate(sel->base, ctx, arena, returned);
  Logic4Vec idx = EvalExpr(sel->index, ctx, arena);
  if (!returned || returned->elem_layout == nullptr || HasUnknownBits(idx)) {
    out = MakeLogic4VecVal(arena, 32, 0);
    return true;
  }
  Logic4Vec elem = ElementOfReturnedAggregate(
      *returned, static_cast<int64_t>(idx.ToUint64()), arena);
  if (!ReadLayoutMember(returned->elem_layout, expr, elem, arena, out))
    out = MakeLogic4VecVal(arena, 32, 0);
  return true;
}

// §7.10.2.1 and §7.5.2: size() is the number of elements the queue or the
// dynamic array holds, an `int`. No other method is answered on an aggregate
// a call returned.
bool TryReturnedAggregateMethod(const ReturnedAggregate& returned,
                                std::string_view method, Arena& arena,
                                Logic4Vec& out) {
  if (method != "size") return false;
  out = MakeLogic4VecVal(arena, 32, returned.elements.size());
  out.is_signed = true;
  return true;
}

}  // namespace

CallResultReceiverScope::CallResultReceiverScope(const Expr* call,
                                                 SimContext& ctx, Arena& arena)
    : ctx_(ctx) {
  if (call == nullptr || call->kind != ExprKind::kCall ||
      !SelectsNamedMember(call->lhs)) {
    return;
  }
  const Expr* base = CallReceiverStartsAt(call->lhs->lhs);
  if (base == nullptr) return;
  std::optional<ReturnedAggregate> returned;
  Logic4Vec value = EvalWithReturnedAggregate(base, ctx, arena, returned);
  auto& reg = Register();
  outer_base_ = reg.held_base;
  outer_aggregate_ = std::move(reg.held_aggregate);
  reg.held_base = base;
  reg.held_aggregate = std::move(returned);
  ctx.SetDeferredArgSnapshot(base, value);
  base_ = base;
}

CallResultReceiverScope::~CallResultReceiverScope() { Release(); }

void CallResultReceiverScope::Release() {
  if (base_ == nullptr) return;
  ctx_.ClearDeferredArgSnapshot(base_);
  auto& reg = Register();
  reg.held_base = outer_base_;
  reg.held_aggregate = std::move(outer_aggregate_);
  base_ = nullptr;
}

bool StartsAtHeldCall(const Expr* side) {
  const Expr* call = CallReceiverStartsAt(side);
  return call != nullptr && call == Register().held_base;
}

FunctionBodyResultScope::FunctionBodyResultScope(SimContext& ctx) : ctx_(ctx) {
  auto& reg = Register();
  reg.bodies.emplace_back();
  const Logic4Vec* held = reg.held_base != nullptr
                              ? ctx.FindDeferredArgSnapshot(reg.held_base)
                              : nullptr;
  if (held == nullptr) return;
  set_aside_base_ = reg.held_base;
  set_aside_value_ = *held;
  set_aside_aggregate_ = std::move(reg.held_aggregate);
  ctx.ClearDeferredArgSnapshot(set_aside_base_);
  reg.held_base = nullptr;
  reg.held_aggregate.reset();
}

FunctionBodyResultScope::~FunctionBodyResultScope() {
  auto& reg = Register();
  reg.completed = std::move(reg.bodies.back());
  reg.bodies.pop_back();
  if (set_aside_base_ == nullptr) return;
  ctx_.SetDeferredArgSnapshot(set_aside_base_, set_aside_value_);
  reg.held_base = set_aside_base_;
  reg.held_aggregate = std::move(set_aside_aggregate_);
}

void RecordReturnedAggregate(const Expr* returned, SimContext& ctx,
                             Arena& arena) {
  auto& reg = Register();
  if (reg.evaluations == 0 || reg.bodies.empty()) return;
  reg.bodies.back().aggregate = CaptureAggregate(returned, ctx, arena);
}

void RecordReturnedTag(const Expr* returned) {
  auto& reg = Register();
  if (reg.evaluations == 0 || reg.bodies.empty()) return;
  if (returned == nullptr || returned->kind != ExprKind::kTagged ||
      returned->rhs == nullptr) {
    return;
  }
  reg.bodies.back().tag = std::string(returned->rhs->text);
}

void RecordReturnedVariableTag(const Expr* returned, SimContext& ctx) {
  auto& reg = Register();
  if (reg.evaluations == 0 || reg.bodies.empty()) return;
  if (returned == nullptr || returned->kind != ExprKind::kIdentifier) return;
  // The layout gate keeps a tag left in the table under a bare name -- a
  // local of an earlier call, a top-level object of the same name -- from
  // being read as the tag of a variable that has none.
  const StructTypeInfo* layout = StructLayoutOfName(returned->text, ctx);
  if (layout == nullptr || !layout->is_union) return;
  std::string_view tag = ctx.GetVariableTag(TagKeyOfName(returned->text, ctx));
  if (!tag.empty()) reg.bodies.back().tag = std::string(tag);
}

Logic4Vec EvalWithReturnedAggregate(
    const Expr* expr, SimContext& ctx, Arena& arena,
    std::optional<ReturnedAggregate>& returned) {
  returned.reset();
  if (expr == nullptr || expr->kind != ExprKind::kCall)
    return EvalExpr(expr, ctx, arena);
  auto& reg = Register();
  if (expr == reg.held_base) {
    returned = reg.held_aggregate;
    return EvalExpr(expr, ctx, arena);
  }
  ++reg.evaluations;
  reg.completed.aggregate.reset();
  Logic4Vec value = EvalExpr(expr, ctx, arena);
  --reg.evaluations;
  returned = std::move(reg.completed.aggregate);
  reg.completed.aggregate.reset();
  return value;
}

Logic4Vec EvalWithReturnedTag(const Expr* expr, SimContext& ctx, Arena& arena,
                              std::string& tag) {
  tag.clear();
  if (expr == nullptr || expr->kind != ExprKind::kCall)
    return EvalExpr(expr, ctx, arena);
  auto& reg = Register();
  ++reg.evaluations;
  reg.completed.tag.clear();
  Logic4Vec value = EvalExpr(expr, ctx, arena);
  --reg.evaluations;
  tag = std::move(reg.completed.tag);
  reg.completed.tag.clear();
  return value;
}

// One step of the walk from an aggregate's layout to the member `seg` names
// in it: the member's own layout, with `key` -- the tag key of the aggregate,
// its storage key followed by the path so far -- extended by the member's
// name. Null where `seg` names no member or a scalar one, and null where the
// aggregate is a tagged union whose current tag is another member than
// `seg`, since §11.9 (printed page 304) makes the write inconsistent with the
// tag a run-time error that the store reports and declines, and a tag set
// for a member never written would be read against nothing.
static const StructTypeInfo* DescendToMember(const StructTypeInfo& layout,
                                             std::string_view seg,
                                             std::string& key,
                                             SimContext& ctx) {
  if (layout.is_union) {
    std::string_view tag = ctx.GetVariableTag(key);
    if (!tag.empty() && tag != seg) return nullptr;
  }
  const StructFieldInfo* field = FindStructField(&layout, seg);
  if (field == nullptr) return nullptr;
  key += '.';
  key += seg;
  return field->nested;
}

// Whether the member access `lhs`, `s.u` or `s.p.u`, names a tagged union
// member of a variable, and the key that member's tag stands under: the key
// the variable's storage was created by (TagKeyOfName) followed by the
// member path, "s.u" for a top-level s and "m.s.u" for one inside instance
// m, the same shape the layout table gives a nested member's window by. A
// path a scope resolution starts, a member of a class object and a member no
// layout answers name no key.
bool TaggedUnionMemberKey(const Expr* lhs, SimContext& ctx, std::string& key) {
  if (lhs->kind != ExprKind::kMemberAccess || lhs->is_scope_resolution)
    return false;
  std::string name;
  BuildLhsName(lhs, name);
  size_t dot = MemberPathSplit(name, ctx);
  if (dot == std::string::npos) return false;
  std::string_view base = std::string_view(name).substr(0, dot);
  std::string_view path = std::string_view(name).substr(dot + 1);
  const StructTypeInfo* layout = StructLayoutOfName(base, ctx);
  key = TagKeyOfName(base, ctx);
  while (layout != nullptr) {
    size_t seg_end = path.find('.');
    layout = DescendToMember(*layout, path.substr(0, seg_end), key, ctx);
    if (seg_end == std::string_view::npos)
      return layout != nullptr && layout->is_union;
    path = path.substr(seg_end + 1);
  }
  return false;
}

// §7.3.2 (printed page 151) has a tagged union value carry its tag beside the
// member's bits, whether the union is a variable or the member of one:
// `s.u = tagged Valid 9` and `s.u = g()` give s's member u the tag Valid as
// `u = tagged Valid 9` gives u, and §11.9 (printed 304) checks a later write
// into that member, `s.u.Other = 3`, against it. The member store takes the
// bits alone (WriteStructField sees no right-hand expression), so the tag is
// set here, under the member's own key (TaggedUnionMemberKey), from the
// member a `tagged M v` names or the one a call's body returned. Every other
// member target, and every other right-hand side, is evaluated as it was.
static Logic4Vec EvalRhsForTaggedMember(const Stmt* stmt, SimContext& ctx,
                                        Arena& arena) {
  bool is_call = stmt->rhs->kind == ExprKind::kCall;
  bool is_tagged =
      stmt->rhs->kind == ExprKind::kTagged && stmt->rhs->rhs != nullptr;
  std::string key;
  if ((!is_call && !is_tagged) || !TaggedUnionMemberKey(stmt->lhs, ctx, key))
    return EvalRhsWithStructContext(stmt, ctx, arena);
  std::string tag;
  Logic4Vec value = is_call ? EvalWithReturnedTag(stmt->rhs, ctx, arena, tag)
                            : EvalRhsWithStructContext(stmt, ctx, arena);
  if (is_tagged) tag = std::string(stmt->rhs->rhs->text);
  // The tag table keeps the view it is given, so the key is interned in the
  // arena rather than left in a string that ends with this statement.
  if (!tag.empty()) ctx.SetVariableTag(*arena.Create<std::string>(key), tag);
  return value;
}

// §7.3.2 (printed page 151) has a tagged union value carry its tag beside
// the member's bits, §13.4.1 (printed 342) gives the implicit variable of a
// call the return type, tag included for `return tagged M v`, and §11.9
// (printed 304) checks every later member read of the target against the
// tag the assignment gave it. `u = g();` copied the bits alone: the store
// path reads the tag off a `tagged` right-hand side and a call is none, so
// `u.Valid` was checked against no tag and `u.Other` raised nothing. The tag
// a call's body returned is taken by the same handover a formal's binding
// takes it (EvalWithReturnedTag), and set where the `u = tagged M v` writer
// sets it, for a target whose layout is a union; a structure target has no
// tag, a select names no union of its own, and a member target that is a
// tagged union of a variable's is EvalRhsForTaggedMember's.
Logic4Vec EvalRhsCarryingReturnedTag(const Stmt* stmt, SimContext& ctx,
                                     Arena& arena) {
  if (stmt->rhs == nullptr) return EvalRhsWithStructContext(stmt, ctx, arena);
  // §11.4.14.3 with §11.4.14.1 (printed pages 291-292): the source of an
  // unpack is a bit-stream, and one that names an unpacked aggregate -- a
  // queue, a dynamic or a fixed-size array -- is the bit-stream cast of its
  // elements, the first in the most significant bits, which
  // PackBitStreamOperand builds as it does for $countones. Evaluated as a
  // name, a queue answered its carrier alone, so `{<< 8 {h, l, c, d}} = pkt`
  // of a 17-byte queue was reported "too few bits in stream": the suite's
  // 11.4.14.4--dynamic_array_stream-sim.sv (#4365) and the queue source of
  // #4042.
  if (stmt->lhs->kind == ExprKind::kStreamingConcat)
    return PackBitStreamOperand(stmt->rhs, ctx, arena);
  if (stmt->lhs->kind == ExprKind::kMemberAccess)
    return EvalRhsForTaggedMember(stmt, ctx, arena);
  if (stmt->rhs->kind != ExprKind::kCall ||
      stmt->lhs->kind != ExprKind::kIdentifier) {
    return EvalRhsWithStructContext(stmt, ctx, arena);
  }
  std::string tag;
  Logic4Vec value = EvalWithReturnedTag(stmt->rhs, ctx, arena, tag);
  if (tag.empty()) return value;
  const StructTypeInfo* layout = StructLayoutOfName(stmt->lhs->text, ctx);
  if (layout == nullptr || !layout->is_union) return value;
  // The tag table keeps the view it is given, so the key is interned in the
  // arena rather than left in a string that ends with this statement.
  ctx.SetVariableTag(
      *arena.Create<std::string>(TagKeyOfName(stmt->lhs->text, ctx)), tag);
  return value;
}

// The assignment `stmt` of a call's result, and the context and arena it
// is carried out in.
struct CallResultAssign {
  const Stmt* stmt;
  SimContext& ctx;
  Arena& arena;
};

// Copies `returned` into the queue or dynamic array `q` the statement's
// target names, as an assignment to it rebuilds its elements: each at the
// element width, fresh element identities, and the change announced to the
// watchers of `owner`, the object whose property it is, or of the name
// (§9.4.2).
static void CopyReturnedToQueue(const ReturnedAggregate& returned,
                                QueueObject* q, ClassObject* owner,
                                const CallResultAssign& a) {
  q->elements.clear();
  for (const Logic4Vec& e : returned.elements)
    q->elements.push_back(
        OwnRhsWords(ResizeToWidth(e, q->elem_width, a.arena), a.arena));
  q->AssignFreshIds();
  ++q->generation;
  AnnounceQueueChange(a.stmt->lhs, owner, a.ctx);
}

// Copies `returned` into the fixed-size array `dst` the statement's target
// names, element for element from the left of each (§7.6); a different
// number of elements is the §7.6 error, and nothing is written.
static void CopyReturnedToArray(const ReturnedAggregate& returned,
                                const ArrayInfo& dst,
                                const CallResultAssign& a) {
  const Stmt* stmt = a.stmt;
  SimContext& ctx = a.ctx;
  Arena& arena = a.arena;
  std::string_view name = stmt->lhs->text;
  if (returned.elements.size() != dst.size) {
    ctx.GetDiag().Error(stmt->range.start,
                        "array size mismatch in assignment to fixed-size array",
                        Subclause("7.6"));
    return;
  }
  for (uint32_t i = 0; i < dst.size; ++i) {
    uint32_t idx = dst.is_descending ? dst.lo + dst.size - 1 - i : dst.lo + i;
    Variable* elem =
        ctx.FindVariable(std::string(name) + "[" + std::to_string(idx) + "]");
    if (elem == nullptr) continue;
    elem->value = OwnRhsWords(
        ResizeToWidth(returned.elements[i], dst.elem_width, arena), arena);
    elem->NotifyWatchers();
  }
}

bool TryCallResultArrayAssign(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (stmt->lhs == nullptr || stmt->rhs == nullptr ||
      stmt->lhs->kind != ExprKind::kIdentifier ||
      stmt->rhs->kind != ExprKind::kCall ||
      !CallsDeclaredSubroutine(stmt->rhs, ctx, arena))
    return false;
  ClassObject* owner = nullptr;
  QueueObject* q = FindQueueOfBase(stmt->lhs, ctx, arena, &owner);
  const ArrayInfo* dst =
      q == nullptr ? ctx.FindArrayInfo(stmt->lhs->text) : nullptr;
  if (q == nullptr && (dst == nullptr || dst->is_dynamic || dst->is_queue ||
                       dst->dim_sizes.size() > 1))
    return false;
  std::optional<ReturnedAggregate> returned;
  Logic4Vec value = EvalWithReturnedAggregate(stmt->rhs, ctx, arena, returned);
  // A body that returned no aggregate hands out the one value, which a queue
  // holds as its one element, as the queue assignment path makes it.
  if (!returned && q != nullptr) {
    returned.emplace();
    returned->elements.push_back(value);
  }
  if (!returned) {
    ApplyGenericBlockingAssign(stmt, value, ctx, arena);
    return true;
  }
  CallResultAssign target{stmt, ctx, arena};
  if (q != nullptr) {
    CopyReturnedToQueue(*returned, q, owner, target);
  } else {
    CopyReturnedToArray(*returned, *dst, target);
  }
  return true;
}

Logic4Vec ElementOfReturnedAggregate(const ReturnedAggregate& returned,
                                     int64_t idx, Arena& arena) {
  auto size = static_cast<int64_t>(returned.elements.size());
  int64_t lo = returned.lo;
  int64_t pos = returned.is_descending ? lo + size - 1 - idx : idx - lo;
  if (pos < 0 || pos >= size) {
    return returned.is_4state ? MakeAllX(arena, returned.elem_width)
                              : MakeLogic4VecVal(arena, returned.elem_width, 0);
  }
  return returned.elements[static_cast<size_t>(pos)];
}

bool TryEvalCallResultMember(const Expr* expr, SimContext& ctx, Arena& arena,
                             Logic4Vec& out) {
  if (expr != nullptr && expr->kind == ExprKind::kMemberAccess &&
      TryElementOfCallResultMember(expr, ctx, arena, out))
    return true;
  if (!SelectsMemberOfCallResult(expr)) return false;
  // The base side is evaluated once, running the call it starts at, and read
  // as the structure the call's return type names ahead of the handle read: a
  // structure's bits are no handle, and a class's name registers no layout.
  Logic4Vec value = EvalExpr(expr->lhs, ctx, arena);
  if (TryStructResultMember(expr, value, ctx, arena, out)) return true;
  ClassObject* obj = ctx.GetClassObject(value.ToUint64());
  if (obj == nullptr) return false;
  out = obj->GetProperty(expr->rhs->text, arena);
  return true;
}

bool TryEvalCallResultMethodCall(const Expr* expr, SimContext& ctx,
                                 Arena& arena, Logic4Vec& out) {
  if (expr == nullptr || expr->kind != ExprKind::kCall ||
      !SelectsMemberOfCallResult(expr->lhs)) {
    return false;
  }
  const Expr* access = expr->lhs;
  std::optional<ReturnedAggregate> returned;
  Logic4Vec handle =
      EvalWithReturnedAggregate(access->lhs, ctx, arena, returned);
  if (returned) {
    return TryReturnedAggregateMethod(*returned, access->rhs->text, arena, out);
  }
  // §6.16 with §13.4: the call answered a string -- a subroutine declared to
  // return one (ExecClassMethod, EvalFunctionCall) or a string method that
  // answers one (StringResult in eval_string.cpp) marks its value so -- and
  // the method is one of the string type's, `h.get().len()` or
  // `s.toupper().substr(0, 2)`, read off the value the call already produced.
  // Read as a handle, the text named no object and the call answered nothing.
  if (handle.is_string &&
      TryEvalStringMethodOnValue(handle, expr, ctx, arena, out)) {
    return true;
  }
  // §19.8: the call answered a covergroup handle, `pick().sample()`.
  if (TryEvalCovergroupMethodOnHandle(handle, expr, ctx, arena, out)) {
    return true;
  }
  InstanceMethodInfo info;
  info.obj = ctx.GetClassObject(handle.ToUint64());
  // §8.4: a call through the null handle a call answered is reported, once,
  // since this arm owns the receiver and no later one evaluates it again.
  if (info.obj == nullptr) {
    ReportNullHandleCall(access->rhs->text, access->rhs->range.start, ctx);
    return false;
  }
  info.method = ResolveMethodOnObject(info.obj, access->rhs->text, &info.owner);
  if (info.method == nullptr) return false;
  // Run as a method called through a variable is: a static one in class scope
  // (§8.10), an instance one with its defining class as the enclosing scope
  // (§8.15).
  out = RunInstanceMethod(info, expr, ctx, arena);
  return true;
}

}  // namespace delta
