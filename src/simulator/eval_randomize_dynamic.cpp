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
#include "simulator/class_object.h"
#include "simulator/constraint_solver.h"
#include "simulator/dyn_struct_member.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/eval_array_class_queue.h"
#include "simulator/eval_class_array.h"
#include "simulator/eval_randomize_internal.h"
#include "simulator/sim_context_types.h"

namespace delta {

// 18.4: a rand member declared as a dynamic array whose size an active
// constraint block constrains is resized to the size the size constraints
// choose and randomized over that many elements; one whose size no block
// constrains keeps its size and is randomized over the elements it holds.
// 18.5.7.1: the size constraints are solved first and the iterative
// constraints next, so the size is the solver's variable drawn ahead of the
// others, which a foreach reads as a state variable.

namespace {

// The most elements a dynamic array is randomized over: the elements are
// drawn for the largest size the size constraints admit, and a size bounded
// below alone admits any.
constexpr int64_t kMaxDynamicElements = 256;

// §18.4: the rand member named `name` the class chain from `type` declares
// as a queue, and the class declaring it in `level`; null for any other name.
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

// Whether `e` is the size method of a dynamic array or queue property of the
// class `type`, `A.size` or `A.size()`, filling `array` with the property's
// name.
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

// Whether `e` holds a size call of a dynamic array or queue property of
// `type` anywhere within it.
bool HoldsSizeCall(const Expr* e, const ClassTypeInfo* type, SimContext& ctx) {
  if (e == nullptr) return false;
  std::string_view array;
  if (IsSizeCall(e, type, ctx, array)) return true;
  auto holds = [type, &ctx](const Expr* sub) {
    return HoldsSizeCall(sub, type, ctx);
  };
  return std::any_of(e->args.begin(), e->args.end(), holds) ||
         std::any_of(e->elements.begin(), e->elements.end(), holds) ||
         holds(e->lhs) || holds(e->rhs) || holds(e->base) || holds(e->index) ||
         holds(e->index_end) || holds(e->condition) || holds(e->true_expr) ||
         holds(e->false_expr) || holds(e->with_expr) || holds(e->repeat_count);
}

// The solver variable for the size of the dynamic array `array` declared at
// `level`: an int, as the size method returns (7.5.2), over the sizes the
// elements are drawn for, and drawn ahead of the other variables.
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

// 18.4: folds the active size constraints over the size variable `size`,
// which each relation of an active constraint block naming the size method
// is translated against, a comparison folding its domain and a set
// membership bounding it by its largest member; false where no active block
// constrains the size, which leaves the array its size.
bool FoldSizeConstraints(RandInfo& size, std::vector<RandInfo>& rands,
                         RandomizeCtx& rc) {
  bool constrained = false;
  int64_t largest = kMaxDynamicElements;
  for (const ClassMember* m : ConstraintMembersInOrder(rc.obj->type)) {
    if (!IsObjectConstraintActive(rc.obj, m->name)) continue;
    for (const Expr* rel : m->constraint_exprs) {
      const Expr* resolved = ResolveArraySizes(rel, rc);
      if (!RefsNamedRandVar(resolved, size.name)) continue;
      ConstraintExpr ce = TranslateRelation(resolved, rands, rc, /*fold=*/true);
      constrained = true;
      if (ce.kind == ConstraintKind::kSetMembership &&
          ce.var_name == size.name && !ce.set_values.empty()) {
        largest = std::min(largest, *std::max_element(ce.set_values.begin(),
                                                      ce.set_values.end()));
      }
    }
  }
  if (constrained) FoldBound(size, ConstraintKind::kLessEqual, largest);
  return constrained;
}

// A rand member declared as a dynamic array or a queue: its declaration, the
// class declaring it, the elements the object holds, and whether it is a
// queue.
struct DynamicMember {
  const ClassMember* decl = nullptr;
  const ClassTypeInfo* level = nullptr;
  int64_t held = 0;
  bool in_queue = false;
};

// The random variables of the rand dynamic array or queue `member`: the size
// variable where the size is constrained, and one variable per element up to
// the largest size admitted, or up to the size the object holds where it is
// not.
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

// §18.4: the random variables of the rand member `m` declared at `level`
// as the associative array `aa`: one per element it holds, named by its key,
// `m[5]` or `m["a"]`.
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
    add(ClassArrayElementKey(m->name, key));
    rands.back().int_key = key;
  }
  for (const auto& [key, value] : aa.str_data) {
    add(std::string(m->name) + "[\"" + key + "\"]");
    rands.back().str_key = key;
  }
}

// The random variables of the rand member `m` of `lvl` whose count is the
// object's rather than the class's, where it is one.
void AddObjectSizedMember(const ClassMember* m, const ClassTypeInfo* lvl,
                          std::vector<RandInfo>& rands, RandomizeCtx& rc) {
  // §18.4: an associative array has its elements randomized, its keys and so
  // its size left as they are.
  if (IsAssocPropertyDecl(m, lvl, rc.ctx)) {
    AssocArrayObject* aa = ClassAssocProperty(rc.obj, lvl, m->name, rc.ctx);
    if (aa != nullptr && !m->is_static)
      AddAssocElements(m, lvl, *aa, rands, rc);
    return;
  }
  // §18.4: a queue is randomized as a dynamic array is, resized at its back to
  // the size the constraints draw.
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
  // §18.4: randomize() allocates no class object, so an array of handles is
  // resized alone: the handles up to the new size are kept and the elements
  // added are null.
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

// 18.4: whether `ri` is an element of a dynamic array beyond the size the
// solve drew for it, recorded in `sizes` under the array's name by the size
// variable, which precedes the elements; the array is resized to that size,
// so the element is dropped rather than written.
static bool BeyondDrawnSize(
    const RandInfo& ri, const std::unordered_map<std::string, int64_t>& sizes) {
  if (ri.array_base.empty() || ri.var.is_array_size) return false;
  auto it = sizes.find(ri.array_base);
  return it != sizes.end() && ri.array_index >= it->second;
}

namespace {

// §18.4: an element of a rand associative array lands under the key it was
// drawn for.
void WriteAssocElement(ClassObject* obj, const RandInfo& ri,
                       const Logic4Vec& lv) {
  // The array the element was collected from holds it under its key.
  AssocArrayObject* aa = obj->assoc_properties.at(ri.array_base);
  if (aa->is_string_key) {
    aa->str_data[ri.str_key] = lv;
  } else {
    aa->int_data[ri.int_key] = lv;
  }
}

// §18.4: a member of a rand unpacked structure lands in its bits of the value
// the property holds, the other members left as they were.
void WriteStructMember(ClassObject* obj, const RandInfo& ri,
                       const Logic4Vec& lv) {
  // The property the structure's layout came from holds the whole value.
  Logic4Vec& whole = obj->properties.at(ri.struct_base);
  DepositBitField(whole, ri.struct_offset, lv, ri.var.width);
  obj->properties[std::string(ri.level->name) + "::" + ri.struct_base] = whole;
}

// The value `lv` drawn for `ri`, written where the variable is held.
void WriteSolvedValue(ClassObject* obj, const RandInfo& ri,
                      const Logic4Vec& lv) {
  if (ri.in_assoc) {
    WriteAssocElement(obj, ri, lv);
  } else if (!ri.struct_base.empty()) {
    WriteStructMember(obj, ri, lv);
  } else if (ri.is_static && ri.level != nullptr) {
    // 18.6.3: a static random variable is a single storage shared by every
    // instance of the class, so a successful randomize() must publish the
    // drawn value to that class-wide cell, not to a private per-object copy,
    // which would shadow the shared storage for this object and leave the
    // other instances observing the old value.
    ri.level->static_properties[ri.name] = lv;
  } else {
    obj->properties[ri.name] = lv;
    obj->properties[std::string(ri.level->name) + "::" + ri.name] = lv;
  }
}

// §18.4: each rand queue holds the elements drawn for it, as many as its
// size, resized at its back.
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

// §18.4: the elements drawn for the rand dynamic members of rand unpacked
// structures, each written into the copy of its member's elements the
// structure is given to hold, one copy per member.
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

// 18.6.1: write each solved value back to the object, keeping the bare and
// scoped ("Class::name") property aliases in sync so member reads see it. A
// dynamic array's size is written under its key, which sizes the array
// (18.4), ahead of its elements.
void WriteBackSolved(ClassObject* obj, std::vector<RandInfo>& rands,
                     ConstraintSolver& solver, Arena& arena) {
  std::unordered_map<std::string, int64_t> sizes;
  std::unordered_map<std::string, std::vector<Logic4Vec>> queues;
  std::vector<std::pair<const RandInfo*, Logic4Vec>> struct_elements;
  for (auto& ri : rands) {
    if (ri.var.is_array_size) sizes[ri.array_base] = solver.GetValue(ri.name);
    if (BeyondDrawnSize(ri, sizes)) continue;
    Logic4Vec lv = SolvedValue(ri, solver, arena);
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
}

}  // namespace delta
