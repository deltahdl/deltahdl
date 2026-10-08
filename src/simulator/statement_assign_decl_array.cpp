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

// §7.4.2: as in C, a fixed-size unpacked dimension may instead be written as a
// single positive constant integer giving its element count, `[size]` then
// meaning `[0:size-1]`. The clause's own example gives `int Array[8][32]` and
// `int Array[0:7][0:31]` as the same declaration, so the size form is the
// ascending range counting from zero and is returned here as that range's upper
// bound.
//
// Every dimension is read this way, the clause's own `int Array[8][32]` being
// two of them. It was once restricted to a lone dimension because the range
// form beside it took the first of several and built one dimension from it, so
// admitting the size form would have spread that reading; the builder below now
// takes every dimension, and there is nothing left to spread.
//
// A queue dimension does not reach here: CreateBlockQueue is asked first and
// answers for every `[$]` and `[$:N]`.
static std::optional<int64_t> BlockArraySizeFormUpperBound(const Expr* dim,
                                                           SimContext& ctx,
                                                           Arena& arena) {
  if (IsAssocIndexDim(dim, ctx)) return std::nullopt;
  auto size = static_cast<int64_t>(EvalExpr(dim, ctx, arena).ToUint64());
  // §7.4.2 asks for a positive size. A declaration that gives anything else is
  // reported by the elaborator's ApplyConstSizedUnpackedDim, so nothing is
  // built here and the same rule is not named twice.
  if (size <= 0) return std::nullopt;
  return size - 1;
}

namespace {
// The bounds one unpacked dimension of a block declaration was written with,
// in the order it wrote them, so that a descending dimension stays
// distinguishable from the ascending one with the same address extent.
struct BlockDimBounds {
  int64_t left;
  int64_t right;
  int64_t Low() const { return std::min(left, right); }
  int64_t Count() const { return std::abs(left - right) + 1; }
};

// §7.4.2: bundle for materializing the leaves of a fixed multidimensional
// unpacked array declared in a block, keeping the recursive walk within the
// parameter-count limit -- the same reason lowerer_var.cpp's MultiDimArray
// exists for the declaration among a module's items.
struct BlockArrayLeaves {
  const std::vector<BlockDimBounds>& dims;
  uint32_t elem_width;
  SimContext& ctx;
  Arena& arena;
  // §6.11.3 and §6.16: each element is a variable of the declared type, so it
  // carries the declaration's signedness, state-ness and string type as a
  // module's element does (CreateArrayElements in lowerer_var.cpp).
  bool is_signed = false;
  bool is_4state = true;
  bool is_string = false;
};
}  // namespace

// The bounds of one dimension, evaluated against the running process. The two
// paths that build an unpacked array differ here and nowhere else: the lowerer
// reads what the elaborator folded, and a block declaration's dimensions are
// expressions the process evaluates as it reaches them.
static std::optional<BlockDimBounds> EvalBlockDim(const Expr* dim,
                                                  SimContext& ctx,
                                                  Arena& arena) {
  if (!dim) return std::nullopt;
  // §7.4.2: a range bound may be negative, so each is read as the signed
  // value it was written as; `[-1:0]` is two elements, not a range from 0 up
  // to the 32 bits of -1.
  if (dim->kind == ExprKind::kBinary && dim->op == TokenKind::kColon) {
    return BlockDimBounds{SelectBoundValue(EvalExpr(dim->lhs, ctx, arena)),
                          SelectBoundValue(EvalExpr(dim->rhs, ctx, arena))};
  }
  if (auto hi = BlockArraySizeFormUpperBound(dim, ctx, arena))
    return BlockDimBounds{0, *hi};
  return std::nullopt;
}

// §7.4.4 makes `int a[0:1][0:2]` an array of two arrays of three, and its
// leaves are named in row-major order by the address each dimension gives --
// §11.5.2 counting an address from the smaller of the two bounds the
// declaration wrote, whichever way round it wrote them. The names are the ones
// CreateMultiDimLeaves builds for a declaration among a module's items, because
// a leaf named `a[1][2]` by one path and anything else by the other would be
// read by neither: TryCompoundArraySelect looks the name up.
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
  // An element is named by its index's 32 bits, as every select names it.
  int64_t low = b.dims[d].Low();
  for (int64_t i = 0; i < b.dims[d].Count(); ++i) {
    CreateBlockArrayLeaves(
        b, d + 1,
        prefix + "[" + std::to_string(static_cast<uint32_t>(low + i)) + "]");
  }
}

// §7.4.4: a multidimensional array is an array of arrays, and one declaration
// may give it several dimensions at once, and §7.4.2 has the dimensions
// following the identifier set the unpacked ones, so every one of them is one
// of the array's. This read the first and built the array as though the
// declaration had stopped there, so `int a[0:1][0:2]` in a begin-end block was
// two elements rather than six and a write to `a[1][2]` reached a leaf nothing
// had created. The declaration among a module's items builds all of them, and
// what the two paths must agree on -- the leaf names, and the per-dimension
// extents $size, foreach and $readmemh read off dim_los/dim_sizes -- is what
// this now records as that one does.
void CreateBlockArrayElements(const Stmt* stmt, uint32_t elem_width,
                              SimContext& ctx, Arena& arena) {
  if (stmt->var_unpacked_dims.empty()) return;
  std::vector<BlockDimBounds> dims;
  dims.reserve(stmt->var_unpacked_dims.size());
  for (const auto* dim : stmt->var_unpacked_dims) {
    auto bounds = EvalBlockDim(dim, ctx, arena);
    // A dimension this cannot read is not one dimension missing but a shape
    // this function cannot build, so nothing is registered and nothing named.
    if (!bounds) return;
    dims.push_back(*bounds);
  }
  ArrayInfo info;
  // The lo/size pair keeps describing the outermost dimension, which is what
  // every whole-array and outer-index path reads, exactly as it does for the
  // declaration among a module's items.
  info.lo = static_cast<uint32_t>(dims[0].Low());
  info.size = static_cast<uint32_t>(dims[0].Count());
  info.elem_width = elem_width;
  info.is_descending = dims[0].left > dims[0].right;
  // Both are per-declaration facts the module path already records and this one
  // left at their defaults, so an `int` array declared in a block answered
  // 4-state and answered its element type as implicit.
  info.is_4state = DeclaredTypeIs4State(stmt->var_decl_type, ctx);
  info.elem_type_kind = stmt->var_decl_type.kind;
  if (dims.size() > 1) {
    for (const auto& dim : dims) {
      info.dim_los.push_back(static_cast<uint32_t>(dim.Low()));
      info.dim_sizes.push_back(static_cast<uint32_t>(dim.Count()));
      info.dim_descending.push_back(dim.left > dim.right);
    }
  }
  // §23.9: a declaration inside a begin-end block is local to that block, so
  // its shape goes away with the block rather than answering for a like-named
  // variable after it. The element variables below are created the same way a
  // few lines down in this file.
  ctx.RegisterArrayInScope(stmt->var_name, info);
  CreateBlockArrayLeaves(
      BlockArrayLeaves{dims, elem_width, ctx, arena,
                       DeclaredTypeIsSigned(stmt->var_decl_type, ctx),
                       info.is_4state,
                       DeclaredTypeIsString(stmt->var_decl_type, ctx)},
      0, std::string(stmt->var_name));
}

}  // namespace delta
