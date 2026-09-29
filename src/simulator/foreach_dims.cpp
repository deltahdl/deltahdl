#include "simulator/foreach_dims.h"

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/packed_range.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/class_object.h"
#include "simulator/eval_class_array.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/variable.h"

namespace delta {

std::string GetForeachArrayName(const Expr* expr) {
  if (!expr) return {};
  if (expr->kind == ExprKind::kIdentifier) return std::string(expr->text);
  if (expr->kind == ExprKind::kMemberAccess) {
    std::string name;
    BuildLhsName(expr, name);
    return name;
  }
  return {};
}

static ForeachDim DimOfRange(std::string_view var, const PackedRange& range) {
  return {var, range.left, range.left > range.right,
          static_cast<uint64_t>(range.HighIndex() - range.LowIndex()) + 1};
}

// An unpacked dimension as ArrayInfo and a property record it: its address
// extent from `lo` and whether it was declared descending.
static ForeachDim DimOfExtent(int64_t lo, uint64_t size, bool descending) {
  int64_t high = lo + static_cast<int64_t>(size) - 1;
  return {{}, descending ? high : lo, descending, size};
}

// The unpacked dimensions `info` records, outermost first, and the key of the
// element standing at every one's low index, `name[lo]` or `name[lo][lo]`,
// whose packed type every element shares.
static void AppendUnpackedDims(const ArrayInfo& info,
                               std::vector<ForeachDim>& dims,
                               std::string& elem_key) {
  if (info.dim_sizes.empty()) {
    dims.push_back(DimOfExtent(info.lo, info.size, info.is_descending));
    elem_key += "[" + std::to_string(info.lo) + "]";
    return;
  }
  for (size_t k = 0; k < info.dim_sizes.size(); ++k) {
    bool descending = k < info.dim_descending.size() && info.dim_descending[k];
    dims.push_back(DimOfExtent(info.dim_los[k], info.dim_sizes[k], descending));
    elem_key += "[" + std::to_string(info.dim_los[k]) + "]";
  }
}

// The packed dimensions of `v`, outermost first, as RecordPackedRange recorded
// them; an `int` or a scalar is the one [width-1:0] it is addressed as.
static void AppendPackedDims(const Variable& v, std::vector<ForeachDim>& dims) {
  dims.push_back(DimOfRange({}, v.DeclaredRange()));
  if (!v.has_packed_range) return;
  for (const auto& range : v.inner_packed_dims)
    dims.push_back(DimOfRange({}, range));
}

// Keeps the dimensions `stmt` names a loop variable for, each given its name.
static std::vector<ForeachDim> NamedDims(const Stmt* stmt,
                                         const std::vector<ForeachDim>& all) {
  std::vector<ForeachDim> named;
  for (size_t k = 0; k < stmt->foreach_vars.size() && k < all.size(); ++k) {
    if (stmt->foreach_vars[k].empty()) continue;
    named.push_back(all[k]);
    named.back().var = stmt->foreach_vars[k];
  }
  return named;
}

std::vector<ForeachDim> DeclaredForeachDims(const Stmt* stmt, SimContext& ctx) {
  std::string name = GetForeachArrayName(stmt->expr);
  if (name.empty() || ctx.IsStringVariable(name)) return {};
  std::vector<ForeachDim> all;
  std::string elem_key = name;
  if (const ArrayInfo* info = ctx.FindArrayInfo(name)) {
    if (info->is_dynamic || info->is_queue || info->elements_are_queues)
      return {};
    AppendUnpackedDims(*info, all, elem_key);
  }
  const Variable* elem = ctx.FindVariable(elem_key);
  if (elem != nullptr && !elem->is_string) {
    AppendPackedDims(*elem, all);
  } else if (all.empty()) {
    return {};
  }
  return NamedDims(stmt, all);
}

std::vector<ForeachDim> ClassArrayForeachDims(const Stmt* stmt,
                                              const ClassArrayRef& ref) {
  if (ref.dim != 0) return {};
  std::vector<ForeachDim> all;
  if (!ClassArrayHoldsSubarrays(ref)) {
    all.push_back(DimOfExtent(ref.lo, ref.size, ref.prop->array_descending));
    return NamedDims(stmt, all);
  }
  const auto& prop = *ref.prop;
  for (size_t k = 0; k < prop.dim_sizes.size(); ++k) {
    bool descending = k < prop.dim_descending.size() && prop.dim_descending[k];
    all.push_back(DimOfExtent(prop.dim_los[k], prop.dim_sizes[k], descending));
  }
  return NamedDims(stmt, all);
}

std::vector<ForeachDim> StructMemberForeachDims(const Stmt* stmt,
                                                const StructFieldInfo& member) {
  return NamedDims(
      stmt, {DimOfRange({}, PackedRange{member.elem_left, member.elem_right})});
}

uint64_t ForeachCombinationCount(const std::vector<ForeachDim>& dims) {
  uint64_t total = 1;
  for (const auto& d : dims) total *= d.size;
  return total;
}

std::vector<Variable*> CreateForeachDimVars(const std::vector<ForeachDim>& dims,
                                            SimContext& ctx) {
  std::vector<Variable*> vars;
  vars.reserve(dims.size());
  for (const auto& d : dims) vars.push_back(ctx.CreateLocalVariable(d.var, 32));
  return vars;
}

void SetForeachDimVars(const std::vector<ForeachDim>& dims,
                       const std::vector<Variable*>& vars, uint64_t n,
                       Arena& arena) {
  for (size_t k = dims.size(); k-- > 0;) {
    uint64_t pos = n % dims[k].size;
    n /= dims[k].size;
    vars[k]->value = MakeLogic4VecVal(
        arena, 32, static_cast<uint64_t>(dims[k].IndexAt(pos)));
  }
}

}  // namespace delta
