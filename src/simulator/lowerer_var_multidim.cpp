#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/types.h"
#include "elaborator/rtlir.h"
#include "parser/ast_expr.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer_register.h"
#include "simulator/pattern_type_key.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/variable.h"

namespace delta {

namespace {
struct MultiDimArray {
  const RtlirVariable& var;
  SimContext& ctx;
  Arena& arena;
  bool in_place = false;
  const StructTypeInfo* layout = nullptr;
};
}  // namespace

static const std::vector<Expr*>* ReplicateBody(const Expr* pat) {
  if (!pat->pattern_keys.empty()) return nullptr;
  if (pat->elements.size() != 1) return nullptr;
  if (!pat->elements[0]->is_pattern_replication) return nullptr;
  const auto& body = pat->elements[0]->elements;
  return body.empty() ? nullptr : &body;
}

static bool IsDimPattern(const Expr* item) {
  return item->kind == ExprKind::kAssignmentPattern ||
         item->kind == ExprKind::kConcatenation;
}

static const Expr* ArrayInitPattern(const Expr* init) {
  if (!init) return nullptr;
  if (init->kind == ExprKind::kCast && init->lhs && IsDimPattern(init->lhs))
    return init->lhs;
  return IsDimPattern(init) ? init : nullptr;
}

static const Expr* FindKeyedItem(const Expr* pat, uint32_t idx,
                                 const MultiDimArray& m) {
  if (const Expr* item = IndexKeyedItem(pat, idx, m.ctx, m.arena)) return item;
  if (const Expr* item = TypeKeyedItem(
          pat, SubjectOfVariableElement(m.var, m.ctx, m.arena), m.ctx))
    return item;
  return DefaultKeyedItem(pat);
}

static const Expr* SelectDimItem(const Expr* pat, uint32_t idx, uint32_t pos,
                                 const MultiDimArray& m) {
  if (!pat->pattern_keys.empty()) return FindKeyedItem(pat, idx, m);
  if (const auto* body = ReplicateBody(pat)) return (*body)[pos % body->size()];
  return pos < pat->elements.size() ? pat->elements[pos] : nullptr;
}

static Variable* NewMultiDimLeaf(const MultiDimArray& m,
                                 const std::string& name) {
  auto* stored = m.arena.Create<std::string>(name);
  auto* elem = m.ctx.CreateVariable(*stored, m.var.width);
  RecordPackedRange(m.var.dtype, elem, m.ctx, m.arena);
  elem->is_4state = m.var.is_4state;
  elem->is_signed = m.var.is_signed;
  elem->is_string = m.var.is_string;
  elem->is_event = m.var.is_event;
  return elem;
}

Variable* ExistingArrayElement(SimContext& ctx, const std::string& key) {
  const auto& variables = ctx.GetVariables();
  auto found = variables.find(key);
  return found == variables.end() ? nullptr : found->second;
}

Logic4Vec ArrayItemForElement(const RtlirVariable& var, const Logic4Vec& val,
                              Arena& arena) {
  if (var.is_real) return MakeRealVec(arena, RealValueOf(val), var.width);
  return OwnRhsWords(ResizeToWidth(val, var.width, arena), arena);
}

static Variable* MultiDimLeaf(const MultiDimArray& m, const std::string& name) {
  return m.in_place ? ExistingArrayElement(m.ctx, name)
                    : NewMultiDimLeaf(m, name);
}

static void StoreMultiDimLeaf(const MultiDimArray& m, const std::string& name,
                              const Logic4Vec& val) {
  Variable* elem = MultiDimLeaf(m, name);
  if (elem == nullptr) return;
  elem->value = ArrayItemForElement(m.var, val, m.arena);
}

static void CreateMultiDimLeaf(const MultiDimArray& m, const std::string& name,
                               const Expr* item) {
  if (item != nullptr) {
    StoreMultiDimLeaf(m, name,
                      EvalItemForLayout(item, m.layout, m.ctx, m.arena));
    return;
  }
  Variable* elem = MultiDimLeaf(m, name);
  if (elem != nullptr && !m.var.is_4state)
    elem->value = MakeLogic4VecVal(m.arena, m.var.width, 0);
}

static std::string MultiDimChildName(const std::string& prefix, int64_t idx) {
  return prefix + "[" + std::to_string(static_cast<uint32_t>(idx)) + "]";
}

static uint32_t FromLeftBound(const MultiDimArray& m, size_t d, uint32_t k) {
  const auto& dim = m.var.unpacked_dims[d];
  return dim.left > dim.right ? m.var.unpacked_dim_sizes[d] - 1 - k : k;
}

static size_t MultiDimLeafCount(const MultiDimArray& m, size_t d) {
  size_t count = 1;
  for (size_t k = d; k < m.var.unpacked_dim_sizes.size(); ++k)
    count *= m.var.unpacked_dim_sizes[k];
  return count;
}

static void StoreSubarrayLeaves(const MultiDimArray& m,
                                const std::string& prefix, size_t d,
                                const std::vector<Logic4Vec>& elems,
                                size_t& next) {
  if (d == m.var.unpacked_dim_sizes.size()) {
    StoreMultiDimLeaf(m, prefix, elems[next++]);
    return;
  }
  for (uint32_t pos = 0; pos < m.var.unpacked_dim_sizes[d]; ++pos) {
    int64_t idx = m.var.unpacked_dims[d].Low() + FromLeftBound(m, d, pos);
    StoreSubarrayLeaves(m, MultiDimChildName(prefix, idx), d + 1, elems, next);
  }
}

static void CreateMultiDimLeaves(const MultiDimArray& m,
                                 const std::string& prefix, size_t d,
                                 const Expr* item);

static bool CreateLeavesFromArrayItem(const MultiDimArray& m,
                                      const std::string& prefix, size_t d,
                                      const Expr* item) {
  std::vector<Logic4Vec> elems;
  if (!CollectArrayItemElements(item, m.ctx, m.arena, elems)) return false;
  if (elems.size() != MultiDimLeafCount(m, d)) {
    m.ctx.GetDiag().Error(
        item->range.start,
        "array size mismatch in assignment to fixed-size array",
        Subclause("7.6"));
    CreateMultiDimLeaves(m, prefix, d, nullptr);
    return true;
  }
  size_t next = 0;
  StoreSubarrayLeaves(m, prefix, d, elems, next);
  return true;
}

static const Expr* SubarrayPattern(const Expr* item, SimContext& ctx) {
  if (item == nullptr) return nullptr;
  if (IsDimPattern(item)) return item;
  return TypedUnpackedArrayPattern(item, ctx);
}

static void CreateMultiDimLeaves(const MultiDimArray& m,
                                 const std::string& prefix, size_t d,
                                 const Expr* item) {
  const auto& sizes = m.var.unpacked_dim_sizes;
  if (d == sizes.size()) {
    CreateMultiDimLeaf(m, prefix, item);
    return;
  }
  const Expr* pat = SubarrayPattern(item, m.ctx);
  if (pat == nullptr && item != nullptr &&
      CreateLeavesFromArrayItem(m, prefix, d, item))
    return;
  for (uint32_t i = 0; i < sizes[d]; ++i) {
    int64_t idx = m.var.unpacked_dims[d].Low() + i;
    const Expr* sub = pat ? SelectDimItem(pat, static_cast<uint32_t>(idx),
                                          FromLeftBound(m, d, i), m)
                          : item;
    CreateMultiDimLeaves(m, MultiDimChildName(prefix, idx), d + 1, sub);
  }
}

void FillMultiDimLeaves(std::string_view name, const RtlirVariable& var,
                        SimContext& ctx, Arena& arena, bool in_place) {
  CreateMultiDimLeaves(
      MultiDimArray{var, ctx, arena, in_place, ctx.GetVariableStructType(name)},
      std::string(name), 0, ArrayInitPattern(var.init_expr));
}

}  // namespace delta
