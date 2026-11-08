#include <cstddef>
#include <cstdint>
#include <map>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "simulator/class_object.h"
#include "simulator/eval_array_class_queue.h"
#include "simulator/eval_class_array.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/variable.h"

namespace delta {

namespace {

struct PropertyStandIn {
  const Expr* target;
  QueueObject* property_queue = nullptr;
  ClassObject* owner = nullptr;
  bool dynamic_array = false;
  QueueObject* local_queue = nullptr;
  Variable* local_var = nullptr;
};

bool MakeDynamicArrayStandIn(const Expr* target, std::string_view name,
                             SimContext& ctx, Arena& arena,
                             PropertyStandIn& out) {
  ClassArrayRef ref;
  if (!ResolveClassArray(target, ctx, arena, ref) || ref.prop == nullptr ||
      !ref.prop->is_dynamic)
    return false;
  std::vector<Logic4Vec> elems;
  PropertyArrayElements(target, ctx, arena, elems);
  out.dynamic_array = true;
  out.local_queue =
      ctx.CreateQueue(name, ref.prop->width, -1, ref.prop->is_4state);
  out.local_queue->elements = std::move(elems);
  out.local_queue->AssignFreshIds();
  return true;
}

void WriteBackDynamicArray(const PropertyStandIn& s, SimContext& ctx,
                           Arena& arena) {
  ClassArrayRef ref;
  if (!ResolveClassArray(s.target, ctx, arena, ref)) return;
  const std::vector<Logic4Vec>& elems = s.local_queue->elements;
  ResizeClassArray(ref, static_cast<uint32_t>(elems.size()), nullptr, ctx,
                   arena);
  if (!ResolveClassArray(s.target, ctx, arena, ref)) return;
  for (size_t i = 0; i < elems.size(); ++i)
    StoreClassArrayElement(ref, ref.lo + static_cast<int64_t>(i), elems[i], ctx,
                           arena);
}

std::string_view StandInName(size_t i, Arena& arena) {
  std::string name = "$stream_property_" + std::to_string(i);
  return {arena.AllocString(name.data(), name.size()), name.size()};
}

bool MakeStandIn(const Expr* target, std::string_view name, SimContext& ctx,
                 Arena& arena, PropertyStandIn& out) {
  out.target = target;
  out.property_queue = FindQueueOfBase(target, ctx, arena, &out.owner);
  if (out.property_queue != nullptr) {
    const QueueObject& pq = *out.property_queue;
    out.local_queue =
        ctx.CreateQueue(name, pq.elem_width, pq.max_size, pq.is_4state);
    out.local_queue->elements = pq.elements;
    out.local_queue->AssignFreshIds();
    return true;
  }
  if (MakeDynamicArrayStandIn(target, name, ctx, arena, out)) return true;
  uint32_t width = FieldLhsWidth(target, ctx);
  if (width == 0) return false;
  out.local_var = ctx.CreateLocalVariable(name, width);
  out.local_var->value =
      ResizeToWidth(EvalExpr(target, ctx, arena), width, arena);
  return true;
}

void WriteBack(const PropertyStandIn& s, SimContext& ctx, Arena& arena) {
  if (s.dynamic_array) {
    WriteBackDynamicArray(s, ctx, arena);
    return;
  }
  if (s.property_queue != nullptr) {
    s.property_queue->elements = s.local_queue->elements;
    s.property_queue->AssignFreshIds();
    ++s.property_queue->generation;
    AnnounceQueueChange(s.target, s.owner, ctx);
    return;
  }
  WriteStructField(s.target, OwnRhsWords(s.local_var->value, arena), ctx);
}

bool IsPropertyTarget(const Expr* e) {
  return e != nullptr && e->kind == ExprKind::kMemberAccess;
}

std::string MemberPath(const Expr* e) {
  if (e == nullptr || e->kind != ExprKind::kMemberAccess || e->lhs == nullptr ||
      e->rhs == nullptr || e->lhs->kind != ExprKind::kIdentifier ||
      e->rhs->kind != ExprKind::kIdentifier)
    return {};
  return std::string(e->lhs->text) + "." + std::string(e->rhs->text);
}

Expr* SubstituteStandIns(const Expr* e,
                         const std::map<std::string, std::string_view>& names,
                         Arena& arena) {
  if (e == nullptr) return nullptr;
  auto it = names.find(MemberPath(e));
  if (it != names.end()) {
    auto* id = arena.Create<Expr>();
    id->kind = ExprKind::kIdentifier;
    id->text = it->second;
    id->range = e->range;
    return id;
  }
  auto* copy = arena.Create<Expr>(*e);
  for (Expr** child :
       {&copy->lhs, &copy->rhs, &copy->base, &copy->index, &copy->index_end,
        &copy->condition, &copy->true_expr, &copy->false_expr})
    *child = SubstituteStandIns(*child, names, arena);
  for (Expr*& arg : copy->args) arg = SubstituteStandIns(arg, names, arena);
  for (Expr*& el : copy->elements) el = SubstituteStandIns(el, names, arena);
  return copy;
}

void SubstituteWithRanges(const Expr* lhs, Expr& rewritten, Arena& arena) {
  std::map<std::string, std::string_view> names;
  for (size_t i = 0; i < rewritten.elements.size(); ++i) {
    if (rewritten.elements[i] != lhs->elements[i])
      names[MemberPath(lhs->elements[i])] = rewritten.elements[i]->text;
  }
  for (size_t i = 0; i < rewritten.elements.size(); ++i) {
    const Expr* with = lhs->elements[i]->stream_range;
    if (with == nullptr || rewritten.elements[i] == lhs->elements[i]) continue;
    rewritten.elements[i]->stream_range =
        SubstituteStandIns(with, names, arena);
  }
}

ClassObject* HandleTargetObject(const Expr* e, SimContext& ctx) {
  if (e->kind != ExprKind::kIdentifier ||
      ctx.GetVariableClassType(e->text).empty())
    return nullptr;
  const Variable* var = ctx.FindVariable(e->text);
  return var == nullptr ? nullptr : ctx.GetClassObject(var->value.ToUint64());
}

const Expr* ExpandHandleTargets(const Expr* lhs, SimContext& ctx,
                                Arena& arena) {
  std::vector<Expr*> expanded;
  bool any = false;
  for (Expr* e : lhs->elements) {
    ClassObject* obj = HandleTargetObject(e, ctx);
    if (obj == nullptr) {
      expanded.push_back(e);
      continue;
    }
    any = true;
    std::vector<const ClassTypeInfo*> chain;
    for (auto* t = obj->type; t != nullptr; t = t->parent) chain.push_back(t);
    for (auto it = chain.rbegin(); it != chain.rend(); ++it) {
      for (const auto& prop : (*it)->properties) {
        if (prop.is_static) continue;
        auto* member = arena.Create<Expr>();
        member->kind = ExprKind::kMemberAccess;
        member->lhs = e;
        member->rhs = arena.Create<Expr>();
        member->rhs->kind = ExprKind::kIdentifier;
        member->rhs->text = prop.name;
        member->range = e->range;
        expanded.push_back(member);
      }
    }
  }
  if (!any) return lhs;
  auto* copy = arena.Create<Expr>(*lhs);
  copy->elements = std::move(expanded);
  return copy;
}

}  // namespace

bool TryUnpackStreamIntoProperties(const Expr* lhs, const Logic4Vec& rhs_val,
                                   SimContext& ctx, Arena& arena) {
  lhs = ExpandHandleTargets(lhs, ctx, arena);
  bool any = false;
  for (const Expr* e : lhs->elements) any = any || IsPropertyTarget(e);
  if (!any) return false;
  ctx.PushScope();
  std::vector<PropertyStandIn> stand_ins;
  auto* rewritten = arena.Create<Expr>(*lhs);
  for (size_t i = 0; i < rewritten->elements.size(); ++i) {
    const Expr* e = rewritten->elements[i];
    if (!IsPropertyTarget(e)) continue;
    std::string_view name = StandInName(i, arena);
    PropertyStandIn s;
    if (!MakeStandIn(e, name, ctx, arena, s)) continue;
    auto* id = arena.Create<Expr>();
    id->kind = ExprKind::kIdentifier;
    id->text = name;
    id->range = e->range;
    rewritten->elements[i] = id;
    stand_ins.push_back(s);
  }
  if (stand_ins.empty()) {
    ctx.PopScope();
    return false;
  }
  SubstituteWithRanges(lhs, *rewritten, arena);
  UnpackStreamingConcatLhs(rewritten, rhs_val, ctx, arena);
  for (const PropertyStandIn& s : stand_ins) WriteBack(s, ctx, arena);
  ctx.PopScope();
  return true;
}

}  // namespace delta
