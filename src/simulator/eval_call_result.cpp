#include "simulator/eval_call_result.h"

#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/eval_array_class_queue.h"
#include "simulator/eval_expr_internal.h"
#include "simulator/eval_function_hier.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"

namespace delta {

namespace {

// Whether `side`, the handle side of a member access, is a method call or a
// member path down from one, `f()` or `f().p.q`: the object it denotes is the
// one the call returned, which no name resolves. A path from a name is left to
// the resolvers that own it, and a select on the way to the element paths.
bool RootedAtCall(const Expr* side) {
  if (side == nullptr) return false;
  if (side->kind == ExprKind::kCall) return true;
  return side->kind == ExprKind::kMemberAccess && !side->is_scope_resolution &&
         side->rhs != nullptr && side->rhs->kind == ExprKind::kIdentifier &&
         RootedAtCall(side->lhs);
}

// Whether `expr` selects a named member, `.m`, of something RootedAtCall.
bool SelectsMemberOfCallResult(const Expr* expr) {
  return expr != nullptr && expr->kind == ExprKind::kMemberAccess &&
         !expr->is_scope_resolution && expr->rhs != nullptr &&
         expr->rhs->kind == ExprKind::kIdentifier && RootedAtCall(expr->lhs);
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

// §7.2: the member `expr->rhs` of the structure `value` the call `expr->lhs`
// returned, its window read off the layout, and §6.11.2 converting the
// unknowns of a 2-state member's window to zeros as a read of the member of a
// variable does. False where the call returns no named structure or the
// layout has no such member.
bool TryStructResultMember(const Expr* expr, const Logic4Vec& value,
                           SimContext& ctx, Arena& arena, Logic4Vec& out) {
  const StructTypeInfo* layout = CallResultStructLayout(expr->lhs, ctx, arena);
  if (layout == nullptr) return false;
  uint32_t bit_offset = 0;
  uint32_t width = 0;
  DataTypeKind kind = DataTypeKind::kLogic;
  if (!ResolveStructFieldPath(layout, expr->rhs->text, &bit_offset, &width,
                              &kind)) {
    return false;
  }
  out = ExtractBitField(arena, value, bit_offset, width);
  if (!Is4stateType(kind)) CoerceTo2State(out);
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

FunctionBodyResultScope::FunctionBodyResultScope() {
  Register().bodies.emplace_back();
}

FunctionBodyResultScope::~FunctionBodyResultScope() {
  auto& reg = Register();
  reg.completed = std::move(reg.bodies.back());
  reg.bodies.pop_back();
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
  InstanceMethodInfo info;
  info.obj = ctx.GetClassObject(handle.ToUint64());
  if (info.obj == nullptr) return false;
  info.method = ResolveMethodOnObject(info.obj, access->rhs->text, &info.owner);
  if (info.method == nullptr) return false;
  // Run as a method called through a variable is: a static one in class scope
  // (§8.10), an instance one with its defining class as the enclosing scope
  // (§8.15).
  out = RunInstanceMethod(info, expr, ctx, arena);
  return true;
}

}  // namespace delta
