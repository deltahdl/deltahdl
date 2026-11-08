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

bool SelectsNamedMember(const Expr* expr) {
  return expr != nullptr && expr->kind == ExprKind::kMemberAccess &&
         !expr->is_scope_resolution && expr->rhs != nullptr &&
         expr->rhs->kind == ExprKind::kIdentifier;
}

namespace {

bool IsCall(const Expr* expr) {
  return expr->kind == ExprKind::kCall || expr->kind == ExprKind::kSystemCall;
}

bool RootedAtCall(const Expr* side) {
  if (side == nullptr) return false;
  if (IsCall(side)) return true;
  return SelectsNamedMember(side) && RootedAtCall(side->lhs);
}

bool SelectsMemberOfCallResult(const Expr* expr) {
  return SelectsNamedMember(expr) && RootedAtCall(expr->lhs);
}

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

ModuleItem* ResolveMethodOnObject(const ClassObject* obj, std::string_view name,
                                  const ClassTypeInfo** owner) {
  ModuleItem* method = obj->ResolveVirtualMethod(name, owner);
  if (method == nullptr)
    method = obj->ResolveMethodForType(name, obj->type, owner);
  return method;
}

struct ReturnedRecord {
  std::optional<ReturnedAggregate> aggregate;
  std::string tag;
};

struct ReturnedAggregateRegister {
  std::vector<ReturnedRecord> bodies;
  ReturnedRecord completed;
  int evaluations = 0;
  const Expr* held_base = nullptr;
  std::optional<ReturnedAggregate> held_aggregate;
};

ReturnedAggregateRegister& Register() {
  static thread_local ReturnedAggregateRegister reg;
  return reg;
}

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

const StructTypeInfo* CallResultStructLayout(const Expr* call, SimContext& ctx,
                                             Arena& arena) {
  if (call->kind != ExprKind::kCall) return nullptr;
  const ModuleItem* func = FindSubroutineTarget(call, ctx, arena).func;
  if (func == nullptr || func->return_type.type_name.empty()) return nullptr;
  return ctx.FindStructType(func->return_type.type_name);
}

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
  if (kind == DataTypeKind::kString) {
    out = StringMemberText(out, arena);
    return true;
  }
  if (!Is4stateType(kind)) CoerceTo2State(out);
  return true;
}

bool TryStructResultMember(const Expr* expr, const Logic4Vec& value,
                           SimContext& ctx, Arena& arena, Logic4Vec& out) {
  return ReadLayoutMember(CallResultStructLayout(expr->lhs, ctx, arena), expr,
                          value, arena, out);
}

bool IsHandleNamePath(const Expr* e) {
  if (e == nullptr) return false;
  if (e->kind == ExprKind::kIdentifier) return true;
  return e->kind == ExprKind::kMemberAccess && !e->is_scope_resolution &&
         e->rhs != nullptr && e->rhs->kind == ExprKind::kIdentifier &&
         IsHandleNamePath(e->lhs);
}

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
  std::string_view bare = access == nullptr ? std::string_view(call->text)
                          : access->kind == ExprKind::kIdentifier
                              ? std::string_view(access->text)
                              : std::string_view{};
  const ClassObject* self = ctx.CurrentThis();
  return self != nullptr && !bare.empty() &&
         ResolveMethodOnObject(self, bare, &owner) != nullptr;
}

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
                              std::string& tag, uint32_t context_width) {
  tag.clear();
  if (expr == nullptr || expr->kind != ExprKind::kCall)
    return EvalExpr(expr, ctx, arena, context_width);
  auto& reg = Register();
  ++reg.evaluations;
  reg.completed.tag.clear();
  Logic4Vec value = EvalExpr(expr, ctx, arena, context_width);
  --reg.evaluations;
  tag = std::move(reg.completed.tag);
  reg.completed.tag.clear();
  return value;
}

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

bool ElementTagKey(const Expr* select, SimContext& ctx, Arena& arena,
                   std::string& key) {
  if (select->kind != ExprKind::kSelect || select->base == nullptr ||
      select->base->kind != ExprKind::kIdentifier || select->index == nullptr ||
      select->index_end != nullptr) {
    return false;
  }
  Logic4Vec index = EvalExpr(select->index, ctx, arena);
  if (!index.IsKnown()) return false;
  key = TagKeyOfName(select->base->text, ctx) + "[" +
        std::to_string(index.ToUint64()) + "]";
  return true;
}

static bool TaggedTargetKey(const Expr* lhs, SimContext& ctx, Arena& arena,
                            std::string& key) {
  if (lhs->kind == ExprKind::kSelect)
    return ElementTagKey(lhs, ctx, arena, key);
  return TaggedUnionMemberKey(lhs, ctx, key);
}

static bool RhsCarriesTag(const Stmt* stmt) {
  return stmt->rhs->kind == ExprKind::kCall ||
         (stmt->rhs->kind == ExprKind::kTagged && stmt->rhs->rhs != nullptr);
}

const Expr* TaggedElementTarget(const Stmt* stmt) {
  if (stmt->lhs == nullptr || stmt->rhs == nullptr ||
      stmt->lhs->kind != ExprKind::kSelect || !RhsCarriesTag(stmt))
    return nullptr;
  return stmt->lhs;
}

static Logic4Vec EvalRhsForTaggedMember(const Stmt* stmt, SimContext& ctx,
                                        Arena& arena) {
  bool is_call = stmt->rhs->kind == ExprKind::kCall;
  bool is_tagged = !is_call && RhsCarriesTag(stmt);
  std::string key;
  if ((!is_call && !is_tagged) || !TaggedTargetKey(stmt->lhs, ctx, arena, key))
    return EvalRhsWithStructContext(stmt, ctx, arena);
  std::string tag;
  Logic4Vec value =
      is_call ? EvalWithReturnedTag(stmt->rhs, ctx, arena, tag,
                                    LhsContextWidth(stmt->lhs, ctx, arena))
              : EvalRhsWithStructContext(stmt, ctx, arena);
  if (is_tagged) tag = std::string(stmt->rhs->rhs->text);
  if (!tag.empty()) ctx.SetVariableTag(*arena.Create<std::string>(key), tag);
  return value;
}

Logic4Vec EvalRhsCarryingReturnedTag(const Stmt* stmt, SimContext& ctx,
                                     Arena& arena) {
  if (stmt->rhs == nullptr) return EvalRhsWithStructContext(stmt, ctx, arena);
  if (stmt->lhs->kind == ExprKind::kStreamingConcat)
    return PackBitStreamOperand(stmt->rhs, ctx, arena);
  if (stmt->lhs->kind == ExprKind::kMemberAccess ||
      stmt->lhs->kind == ExprKind::kSelect)
    return EvalRhsForTaggedMember(stmt, ctx, arena);
  if (stmt->rhs->kind != ExprKind::kCall ||
      stmt->lhs->kind != ExprKind::kIdentifier) {
    return EvalRhsWithStructContext(stmt, ctx, arena);
  }
  std::string tag;
  Logic4Vec value = EvalWithReturnedTag(stmt->rhs, ctx, arena, tag,
                                        LhsContextWidth(stmt->lhs, ctx, arena));
  if (tag.empty()) return value;
  const StructTypeInfo* layout = StructLayoutOfName(stmt->lhs->text, ctx);
  if (layout == nullptr || !layout->is_union) return value;
  ctx.SetVariableTag(
      *arena.Create<std::string>(TagKeyOfName(stmt->lhs->text, ctx)), tag);
  return value;
}

struct CallResultAssign {
  const Stmt* stmt;
  SimContext& ctx;
  Arena& arena;
};

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
  Logic4Vec value = EvalExpr(expr->lhs, ctx, arena);
  if (TryStructResultMember(expr, value, ctx, arena, out)) return true;
  ClassObject* obj = ctx.GetClassObject(value.ToUint64());
  if (obj == nullptr) return false;
  out = obj->GetProperty(expr->rhs->text, arena);
  if (PropertyIsString(obj->type, expr->rhs->text, ctx)) out.is_string = true;
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
  if (handle.is_string &&
      TryEvalStringMethodOnValue(handle, expr, ctx, arena, out)) {
    return true;
  }
  if (TryEvalCovergroupMethodOnHandle(handle, expr, ctx, arena, out)) {
    return true;
  }
  InstanceMethodInfo info;
  info.obj = ctx.GetClassObject(handle.ToUint64());
  if (info.obj == nullptr) {
    ReportNullHandleCall(access->rhs->text, access->rhs->range.start, ctx);
    return false;
  }
  info.method = ResolveMethodOnObject(info.obj, access->rhs->text, &info.owner);
  if (info.method == nullptr) return false;
  out = RunInstanceMethod(info, expr, ctx, arena);
  return true;
}

}  // namespace delta
