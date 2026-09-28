// §11.4.14.3 with §8.5: a streaming unpack whose targets include class
// properties reached through a handle.

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

// One property target of the unpack and the local standing in for it while
// the unpack runs: a queue for a queue or dynamic array property, a variable
// of the property's declared width for any other.
struct PropertyStandIn {
  const Expr* target;
  QueueObject* property_queue = nullptr;
  ClassObject* owner = nullptr;
  bool dynamic_array = false;
  QueueObject* local_queue = nullptr;
  Variable* local_var = nullptr;
};

// §7.5 with §8.5: a dynamic array property, `bit [7:0] d[]`, is held by the
// class-array machinery rather than as a queue, so its stand-in is a queue of
// its elements that the unpack may resize like any other.
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

// Resizes the dynamic array property `s` stood in for to what its stand-in
// holds and stores each element.
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

// The name the stand-in for target `i` goes by, kept in the arena because
// the variable and queue tables hold the key rather than a copy of it.
std::string_view StandInName(size_t i, Arena& arena) {
  std::string name = "$stream_property_" + std::to_string(i);
  return {arena.AllocString(name.data(), name.size()), name.size()};
}

// Makes the stand-in for the member access `target`, or answers false where
// it names no property the unpack can take bits into.
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

// Hands what the unpack left in a stand-in to the property it stood in for.
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

// `h.len` for the member access `e` of one handle and one member, the form a
// `with` range names an earlier target by; empty for any other expression.
std::string MemberPath(const Expr* e) {
  if (e == nullptr || e->kind != ExprKind::kMemberAccess || e->lhs == nullptr ||
      e->rhs == nullptr || e->lhs->kind != ExprKind::kIdentifier ||
      e->rhs->kind != ExprKind::kIdentifier)
    return {};
  return std::string(e->lhs->text) + "." + std::string(e->rhs->text);
}

// §11.4.14.4: a `with` range may read a target unpacked before it, as the
// Packet example's `q.payload with [0 +: q.len]` does. While the unpack runs,
// that target's bits are in its stand-in, so the range is read with each
// target it names replaced by its stand-in's name.
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

// Gives each stand-in in `rewritten` the `with` range its target in `lhs`
// wrote, read against the stand-ins (SubstituteStandIns).
void SubstituteWithRanges(const Expr* lhs, Expr& rewritten, Arena& arena) {
  std::map<std::string, std::string_view> names;
  for (size_t i = 0; i < rewritten.elements.size(); ++i) {
    if (rewritten.elements[i] != lhs->elements[i])
      names[MemberPath(lhs->elements[i])] = rewritten.elements[i]->text;
  }
  for (size_t i = 0; i < rewritten.elements.size(); ++i) {
    const Expr* with = lhs->elements[i]->with_expr;
    if (with == nullptr || rewritten.elements[i] == lhs->elements[i]) continue;
    rewritten.elements[i]->with_expr = SubstituteStandIns(with, names, arena);
  }
}

}  // namespace

bool TryUnpackStreamIntoProperties(const Expr* lhs, const Logic4Vec& rhs_val,
                                   SimContext& ctx, Arena& arena) {
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
