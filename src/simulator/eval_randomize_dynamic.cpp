#include <algorithm>
#include <cstdint>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "simulator/class_object.h"
#include "simulator/constraint_solver.h"
#include "simulator/eval_class_array.h"
#include "simulator/eval_randomize_internal.h"

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

// Whether `e` is the size method of a dynamic array property of the class
// `type`, `A.size` or `A.size()`, filling `array` with the property's name.
bool IsSizeCall(const Expr* e, const ClassTypeInfo* type,
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
  if (prop == nullptr || !prop->is_dynamic) return false;
  array = access->lhs->text;
  return true;
}

// Whether `e` holds a size call of a dynamic array property of `type`
// anywhere within it.
bool HoldsSizeCall(const Expr* e, const ClassTypeInfo* type) {
  if (e == nullptr) return false;
  std::string_view array;
  if (IsSizeCall(e, type, array)) return true;
  auto holds = [type](const Expr* sub) { return HoldsSizeCall(sub, type); };
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

// The random variables of the rand member `m`, a dynamic array declared at
// `level`: the size variable where the size is constrained, and one
// variable per element up to the largest size admitted, or up to the size
// the object holds where it is not.
void AddDynamicArray(const ClassMember* m, const ClassTypeInfo* level,
                     const ClassTypeInfo::PropertyInfo& array,
                     std::vector<RandInfo>& rands, RandomizeCtx& rc) {
  RandInfo element = BuildRandMember(m, level, rc.ctx);
  rands.push_back(SizeVariable(m->name, level));
  auto count = static_cast<int64_t>(ClassArraySize(rc.obj, array));
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

}  // namespace

const Expr* ResolveArraySizes(const Expr* rel, RandomizeCtx& rc) {
  const ClassTypeInfo* type = rc.obj != nullptr ? rc.obj->type : nullptr;
  if (rel == nullptr || type == nullptr) return rel;
  auto& cache = type->size_resolved_relations;
  auto it = cache.find(rel);
  if (it != cache.end()) return it->second != nullptr ? it->second : rel;
  Expr* resolved = nullptr;
  if (HoldsSizeCall(rel, type)) {
    resolved = RewriteExpr(
        rel,
        [type, &rc](const Expr* n) -> Expr* {
          std::string_view array;
          if (!IsSizeCall(n, type, array)) return nullptr;
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
      const auto* array = FindClassArrayProperty(lvl, m->name);
      if (array == nullptr || !array->is_dynamic) continue;
      AddDynamicArray(m, lvl, *array, rands, rc);
    }
  }
}

}  // namespace delta
