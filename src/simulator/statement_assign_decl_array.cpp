#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <optional>
#include <string>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/variable.h"

namespace delta {

static std::optional<int64_t> BlockArraySizeFormUpperBound(const Expr* dim,
                                                           SimContext& ctx,
                                                           Arena& arena) {
  if (IsAssocIndexDim(dim, ctx)) return std::nullopt;
  auto size = static_cast<int64_t>(EvalExpr(dim, ctx, arena).ToUint64());
  if (size <= 0) return std::nullopt;
  return size - 1;
}

namespace {
struct BlockDimBounds {
  int64_t left;
  int64_t right;
  int64_t Low() const { return std::min(left, right); }
  int64_t Count() const { return std::abs(left - right) + 1; }
};

struct BlockArrayLeaves {
  const std::vector<BlockDimBounds>& dims;
  uint32_t elem_width;
  SimContext& ctx;
  Arena& arena;
  bool is_signed = false;
  bool is_4state = true;
  bool is_string = false;
};
}  // namespace

static std::optional<BlockDimBounds> EvalBlockDim(const Expr* dim,
                                                  SimContext& ctx,
                                                  Arena& arena) {
  if (!dim) return std::nullopt;
  if (dim->kind == ExprKind::kBinary && dim->op == TokenKind::kColon) {
    return BlockDimBounds{SelectBoundValue(EvalExpr(dim->lhs, ctx, arena)),
                          SelectBoundValue(EvalExpr(dim->rhs, ctx, arena))};
  }
  if (auto hi = BlockArraySizeFormUpperBound(dim, ctx, arena))
    return BlockDimBounds{0, *hi};
  return std::nullopt;
}

static void CreateBlockArrayLeaves(const BlockArrayLeaves& b, size_t d,
                                   const std::string& prefix) {
  if (d == b.dims.size()) {
    Variable* leaf = b.ctx.CreateVariable(*b.arena.Create<std::string>(prefix),
                                          b.elem_width);
    leaf->is_signed = b.is_signed;
    leaf->is_4state = b.is_4state;
    leaf->is_string = b.is_string;
    if (!b.is_4state) leaf->value = MakeLogic4VecVal(b.arena, b.elem_width, 0);
    return;
  }
  int64_t low = b.dims[d].Low();
  for (int64_t i = 0; i < b.dims[d].Count(); ++i) {
    CreateBlockArrayLeaves(
        b, d + 1,
        prefix + "[" + std::to_string(static_cast<uint32_t>(low + i)) + "]");
  }
}

void CreateBlockArrayElements(const Stmt* stmt, uint32_t elem_width,
                              SimContext& ctx, Arena& arena) {
  if (stmt->var_unpacked_dims.empty()) return;
  std::vector<BlockDimBounds> dims;
  dims.reserve(stmt->var_unpacked_dims.size());
  for (const auto* dim : stmt->var_unpacked_dims) {
    auto bounds = EvalBlockDim(dim, ctx, arena);
    if (!bounds) return;
    dims.push_back(*bounds);
  }
  ArrayInfo info;
  info.lo = static_cast<uint32_t>(dims[0].Low());
  info.size = static_cast<uint32_t>(dims[0].Count());
  info.elem_width = elem_width;
  info.is_descending = dims[0].left > dims[0].right;
  info.is_4state = DeclaredTypeIs4State(stmt->var_decl_type, ctx);
  info.elem_type_kind = stmt->var_decl_type.kind;
  info.elem_type_name = stmt->var_decl_type.type_name;
  info.elem_type_is_unpacked_array = stmt->var_decl_type.names_unpacked_array;
  if (dims.size() > 1) {
    for (const auto& dim : dims) {
      info.dim_los.push_back(static_cast<uint32_t>(dim.Low()));
      info.dim_sizes.push_back(static_cast<uint32_t>(dim.Count()));
      info.dim_descending.push_back(dim.left > dim.right);
    }
  }
  ctx.RegisterArrayInScope(stmt->var_name, info);
  CreateBlockArrayLeaves(
      BlockArrayLeaves{dims, elem_width, ctx, arena,
                       DeclaredTypeIsSigned(stmt->var_decl_type, ctx),
                       info.is_4state,
                       DeclaredTypeIsString(stmt->var_decl_type, ctx)},
      0, ctx.ActiveInstancePrefix() + std::string(stmt->var_name));
}

}  // namespace delta
