#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_map>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "simulator/assoc_index.h"
#include "simulator/class_object.h"
#include "simulator/constraint_solver.h"
#include "simulator/dyn_struct_member.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/eval_array_class_queue.h"
#include "simulator/eval_class_array.h"
#include "simulator/eval_format_internal.h"
#include "simulator/eval_randomize_internal.h"
#include "simulator/sim_context_types.h"

namespace delta {

namespace {

constexpr int64_t kMaxDynamicElements = 256;

const ClassMember* QueueMember(const ClassTypeInfo* type, std::string_view name,
                               SimContext& ctx, const ClassTypeInfo*& level) {
  for (const auto* t = type; t != nullptr; t = t->parent) {
    if (t->decl == nullptr) continue;
    for (const ClassMember* m : t->decl->members) {
      if (m->kind != ClassMemberKind::kProperty || m->name != name) continue;
      if (!(m->is_rand || m->is_randc) || !IsQueuePropertyDecl(m, t, ctx))
        return nullptr;
      level = t;
      return m;
    }
  }
  return nullptr;
}

bool IsSizeCall(const Expr* e, const ClassTypeInfo* type, SimContext& ctx,
                std::string_view& array) {
  const Expr* access = e;
  if (e->kind == ExprKind::kCall) {
    if (!e->args.empty() || e->with_expr != nullptr) return false;
    access = e->lhs;
  }
  if (access == nullptr || access->kind != ExprKind::kMemberAccess ||
      access->is_scope_resolution || access->lhs == nullptr ||
      access->rhs == nullptr || access->lhs->kind != ExprKind::kIdentifier ||
      access->rhs->kind != ExprKind::kIdentifier ||
      access->rhs->text != "size") {
    return false;
  }
  const auto* prop = FindClassArrayProperty(type, access->lhs->text);
  const ClassTypeInfo* level = nullptr;
  if ((prop == nullptr || !prop->is_dynamic) &&
      QueueMember(type, access->lhs->text, ctx, level) == nullptr) {
    return false;
  }
  array = access->lhs->text;
  return true;
}

bool HoldsSizeCall(const Expr* e, const ClassTypeInfo* type, SimContext& ctx) {
  if (e == nullptr) return false;
  std::string_view array;
  if (IsSizeCall(e, type, ctx, array)) return true;
  auto holds = [type, &ctx](const Expr* sub) {
    return HoldsSizeCall(sub, type, ctx);
  };
  const Expr* const kChildren[] = {
      e->lhs,       e->rhs,          e->base,        e->index,
      e->index_end, e->condition,    e->true_expr,   e->false_expr,
      e->with_expr, e->stream_range, e->repeat_count};
  return std::any_of(e->args.begin(), e->args.end(), holds) ||
         std::any_of(e->elements.begin(), e->elements.end(), holds) ||
         std::ranges::any_of(kChildren, holds);
}

RandInfo SizeVariable(std::string_view array, const ClassTypeInfo* level) {
  RandInfo size;
  size.name = ClassArraySizeKey(array);
  size.level = level;
  size.var.name = size.name;
  size.var.qualifier = RandQualifier::kRand;
  size.var.width = 32;
  size.var.is_signed = true;
  size.var.min_val = 0;
  size.var.max_val = kMaxDynamicElements;
  size.var.is_array_size = true;
  size.array_base = std::string(array);
  return size;
}

const Expr* SizeRelation(const Expr* rel, const RandInfo& size,
                         RandomizeCtx& rc) {
  const Expr* resolved = ResolveArraySizes(rel, rc);
  return RefsNamedRandVar(resolved, size.name) ? resolved : nullptr;
}

bool FoldHardSizeRelations(const std::vector<Expr*>& rels, RandInfo& size,
                           std::vector<RandInfo>& rands, RandomizeCtx& rc,
                           int64_t& largest) {
  bool named = false;
  for (const Expr* rel : rels) {
    const Expr* resolved = SizeRelation(rel, size, rc);
    if (resolved == nullptr) continue;
    named = true;
    ConstraintExpr ce = TranslateRelation(resolved, rands, rc, true);
    if (ce.kind == ConstraintKind::kSetMembership && ce.var_name == size.name &&
        !ce.set_values.empty()) {
      largest = std::min(largest, *std::max_element(ce.set_values.begin(),
                                                    ce.set_values.end()));
    }
  }
  return named;
}

bool SoftRelationNamesSize(const std::vector<Expr*>& rels, const RandInfo& size,
                           RandomizeCtx& rc) {
  return std::ranges::any_of(rels, [&](const Expr* rel) {
    return SizeRelation(rel, size, rc) != nullptr;
  });
}

struct SizeReading {
  bool hard = false;
  bool soft = false;
  int64_t largest = kMaxDynamicElements;
};

void ReadBlockSize(const ClassMember* m, RandInfo& size,
                   std::vector<RandInfo>& rands, RandomizeCtx& rc,
                   SizeReading& reading) {
  if (FoldHardSizeRelations(m->constraint_exprs, size, rands, rc,
                            reading.largest)) {
    reading.hard = true;
  }
  if (std::ranges::any_of(m->constraint_disable_soft_refs,
                          [&size](const ConstraintSoftVarRef& ref) {
                            return ref.name == size.name;
                          })) {
    reading.soft = false;
  }
  if (SoftRelationNamesSize(m->constraint_soft_exprs, size, rc)) {
    reading.soft = true;
  }
}

bool FoldSizeConstraints(RandInfo& size, std::vector<RandInfo>& rands,
                         RandomizeCtx& rc) {
  SizeReading reading;
  for (const ClassMember* m : ConstraintMembersInOrder(rc.obj->type)) {
    if (!IsObjectConstraintActive(rc.obj, m->name)) continue;
    ReadBlockSize(m, size, rands, rc, reading);
  }
  if (rc.inline_block != nullptr) {
    ReadBlockSize(rc.inline_block, size, rands, rc, reading);
  }
  const bool kConstrained = reading.hard || reading.soft;
  if (kConstrained) {
    FoldBound(size, ConstraintKind::kLessEqual, reading.largest);
  }
  return kConstrained;
}

struct DynamicMember {
  const ClassMember* decl = nullptr;
  const ClassTypeInfo* level = nullptr;
  int64_t held = 0;
  bool in_queue = false;
};

void AddDynamicArray(const DynamicMember& member, std::vector<RandInfo>& rands,
                     RandomizeCtx& rc) {
  const ClassMember* m = member.decl;
  RandInfo element = BuildRandMember(m, member.level, rc.ctx);
  element.in_queue = member.in_queue;
  rands.push_back(SizeVariable(m->name, member.level));
  rands.back().in_queue = member.in_queue;
  int64_t count = member.held;
  if (FoldSizeConstraints(rands.back(), rands, rc)) {
    count =
        std::clamp<int64_t>(rands.back().var.max_val, 0, kMaxDynamicElements);
  } else {
    rands.pop_back();
  }
  for (int64_t i = 0; i < count; ++i) {
    RandInfo elem = element;
    elem.name = ClassArrayElementKey(m->name, i);
    elem.var.name = elem.name;
    elem.array_base = element.name;
    elem.array_index = i;
    rands.push_back(std::move(elem));
  }
}

void AddAssocElements(const ClassMember* m, const ClassTypeInfo* level,
                      const AssocArrayObject& aa, std::vector<RandInfo>& rands,
                      RandomizeCtx& rc) {
  RandInfo element = BuildRandMember(m, level, rc.ctx);
  element.in_assoc = true;
  element.array_base = element.name;
  auto add = [&](std::string name) {
    RandInfo elem = element;
    elem.name = std::move(name);
    elem.var.name = elem.name;
    rands.push_back(std::move(elem));
  };
  for (const auto& [key, value] : aa.int_data) {
    add(std::string(m->name) + "[" +
        FormatDecimalDigits(key.ToSignedVec(rc.arena)) + "]");
    rands.back().int_key = key;
  }
  for (const auto& [key, value] : aa.str_data) {
    add(std::string(m->name) + "[\"" + key + "\"]");
    rands.back().str_key = key;
  }
}

void AddObjectSizedMember(const ClassMember* m, const ClassTypeInfo* lvl,
                          std::vector<RandInfo>& rands, RandomizeCtx& rc) {
  if (IsAssocPropertyDecl(m, lvl, rc.ctx)) {
    AssocArrayObject* aa = ClassAssocProperty(rc.obj, lvl, m->name, rc.ctx);
    if (aa != nullptr && !m->is_static)
      AddAssocElements(m, lvl, *aa, rands, rc);
    return;
  }
  if (IsQueuePropertyDecl(m, lvl, rc.ctx)) {
    QueueObject* queue = ClassQueueProperty(rc.obj, lvl, m->name, rc.ctx);
    if (queue != nullptr && !m->is_static) {
      AddDynamicArray(
          {m, lvl, static_cast<int64_t>(queue->elements.size()), true}, rands,
          rc);
    }
    return;
  }
  const auto* array = FindClassArrayProperty(lvl, m->name);
  if (array == nullptr || !array->is_dynamic) return;
  if (IsClassHandleMember(m, rc.ctx)) {
    rands.push_back(SizeVariable(m->name, lvl));
    if (!FoldSizeConstraints(rands.back(), rands, rc)) rands.pop_back();
    return;
  }
  AddDynamicArray(
      {m, lvl, static_cast<int64_t>(ClassArraySize(rc.obj, *array)), false},
      rands, rc);
}

}  // namespace

const Expr* ResolveArraySizes(const Expr* rel, RandomizeCtx& rc) {
  const ClassTypeInfo* type = rc.obj != nullptr ? rc.obj->type : nullptr;
  if (rel == nullptr || type == nullptr) return rel;
  auto& cache = type->size_resolved_relations;
  auto it = cache.find(rel);
  if (it != cache.end()) return it->second != nullptr ? it->second : rel;
  Expr* resolved = nullptr;
  if (HoldsSizeCall(rel, type, rc.ctx)) {
    resolved = RewriteExpr(
        rel,
        [type, &rc](const Expr* n) -> Expr* {
          std::string_view array;
          if (!IsSizeCall(n, type, rc.ctx, array)) return nullptr;
          return IdentifierExpr(ClassArraySizeKey(array), n, rc.arena);
        },
        rc.arena);
  }
  cache[rel] = resolved;
  return resolved != nullptr ? resolved : rel;
}

void AddDynamicArrayVariables(std::vector<RandInfo>& rands, RandomizeCtx& rc) {
  for (const auto* lvl = rc.obj->type; lvl != nullptr; lvl = lvl->parent) {
    if (!lvl->decl) continue;
    for (const ClassMember* m : lvl->decl->members) {
      if (m->kind != ClassMemberKind::kProperty || !(m->is_rand || m->is_randc))
        continue;
      AddObjectSizedMember(m, lvl, rands, rc);
      AddRandStructDynamicElements(m, lvl, rands, rc);
    }
  }
}

static bool BeyondDrawnSize(
    const RandInfo& ri, const std::unordered_map<std::string, int64_t>& sizes) {
  if (ri.array_base.empty() || ri.var.is_array_size) return false;
  auto it = sizes.find(ri.array_base);
  return it != sizes.end() && ri.array_index >= it->second;
}

namespace {

void WriteAssocElement(ClassObject* obj, const RandInfo& ri,
                       const Logic4Vec& lv) {
  AssocArrayObject* aa = obj->assoc_properties.at(ri.array_base);
  if (aa->is_string_key) {
    aa->str_data[ri.str_key] = lv;
  } else {
    aa->int_data[ri.int_key] = lv;
  }
}

void WriteStructMember(ClassObject* obj, const RandInfo& ri,
                       const Logic4Vec& lv) {
  Logic4Vec& whole = obj->properties.at(ri.struct_base);
  DepositBitField(whole, ri.struct_offset, lv, ri.var.width);
  obj->properties[std::string(ri.level->name) + "::" + ri.struct_base] = whole;
}

void WriteSolvedValue(ClassObject* obj, const RandInfo& ri,
                      const Logic4Vec& lv) {
  if (ri.in_assoc) {
    WriteAssocElement(obj, ri, lv);
  } else if (!ri.struct_base.empty()) {
    WriteStructMember(obj, ri, lv);
  } else if (ri.is_static && ri.level != nullptr) {
    ri.level->static_properties[ri.name] = lv;
  } else {
    obj->properties[ri.name] = lv;
    obj->properties[std::string(ri.level->name) + "::" + ri.name] = lv;
  }
}

void WriteQueues(
    ClassObject* obj,
    std::unordered_map<std::string, std::vector<Logic4Vec>>& queues) {
  for (auto& [base, elements] : queues) {
    auto it = obj->queue_properties.find(base);
    if (it == obj->queue_properties.end() || it->second == nullptr) continue;
    it->second->elements = std::move(elements);
    it->second->AssignFreshIds();
    ++it->second->generation;
  }
}

void WriteStructDynamicElements(
    ClassObject* obj,
    const std::vector<std::pair<const RandInfo*, Logic4Vec>>& elements,
    Arena& arena) {
  std::unordered_map<std::string, QueueObject*> copies;
  for (const auto& [ri, lv] : elements) {
    QueueObject*& copy = copies[ri->array_base];
    Logic4Vec& whole = obj->properties.at(ri->struct_base);
    if (copy == nullptr) {
      copy = DynMemberForWrite(whole, ri->struct_offset, *ri->dyn_field, arena);
      obj->properties[std::string(ri->level->name) + "::" + ri->struct_base] =
          whole;
    }
    copy->elements.at(static_cast<size_t>(ri->array_index)) = lv;
  }
}

}  // namespace

void WriteBackSolved(ClassObject* obj, std::vector<RandInfo>& rands,
                     const ConstraintSolver& solver, const std::string& prefix,
                     Arena& arena) {
  std::unordered_map<std::string, int64_t> sizes;
  std::unordered_map<std::string, std::vector<Logic4Vec>> queues;
  std::vector<std::pair<const RandInfo*, Logic4Vec>> struct_elements;
  for (auto& ri : rands) {
    if (ri.var.is_array_size)
      sizes[ri.array_base] = solver.GetValue(prefix + ri.name);
    if (BeyondDrawnSize(ri, sizes)) continue;
    Logic4Vec lv = SolvedValue(ri, solver, prefix, arena);
    if (ri.dyn_field != nullptr) {
      struct_elements.emplace_back(&ri, lv);
    } else if (!ri.in_queue) {
      WriteSolvedValue(obj, ri, lv);
    } else if (!ri.var.is_array_size) {
      queues[ri.array_base].push_back(lv);
    }
  }
  WriteQueues(obj, queues);
  WriteStructDynamicElements(obj, struct_elements, arena);
  for (const auto& [array, size] : sizes)
    DropDroppedElementModes(RandModesOf(obj, array), array, size);
}

}  // namespace delta
