#include "simulator/vpi_design_attach_build.h"

#include <cstdint>
#include <optional>

#include "common/arena.h"
#include "common/packed_range.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

namespace {

// A range bound as the integer it evaluates to, sign-extended where the bound
// is signed so that a negative index stays negative.
int64_t BoundValue(const Logic4Vec& v) {
  auto raw = v.ToUint64();
  if (!v.is_signed || v.width == 0 || v.width >= 64) {
    return static_cast<int64_t>(raw);
  }
  const uint64_t kSign = uint64_t{1} << (v.width - 1);
  return static_cast<int64_t>((raw ^ kSign) - kSign);
}

// §11.5.1: one packed range, evaluated in the scope the attach set.
PackedRange EvaluatedRange(Expr* left, Expr* right, SimContext& ctx) {
  Arena& arena = ctx.GetArena();
  return {BoundValue(EvalExpr(left, ctx, arena)),
          BoundValue(EvalExpr(right, ctx, arena))};
}

}  // namespace

VpiObject* VpiIntConstant(int64_t value, const VpiAttachBuild& build) {
  VpiObject* constant = build.alloc();
  constant->type = vpiConstant;
  constant->const_type = vpiIntConst;
  auto* storage = build.arena.Create<Variable>();
  storage->value =
      MakeLogic4VecVal(build.arena, 32, static_cast<uint64_t>(value));
  constant->var = storage;
  constant->size = 32;
  return constant;
}

int64_t PackedDimsWidth(const PackedDims& dims) {
  int64_t width = 1;
  for (const PackedRange& dim : dims) {
    width *= dim.HighIndex() - dim.LowIndex() + 1;
  }
  return width;
}

PackedDims WrittenPackedDims(const DataType* type, SimContext& ctx) {
  if (type == nullptr || type->packed_dim_left == nullptr ||
      type->packed_dim_right == nullptr) {
    return {};
  }
  PackedDims dims{
      EvaluatedRange(type->packed_dim_left, type->packed_dim_right, ctx)};
  for (const auto& [left, right] : type->extra_packed_dims) {
    if (left == nullptr || right == nullptr) return {};
    dims.push_back(EvaluatedRange(left, right, ctx));
  }
  return dims;
}

std::optional<PackedDims> DeclaredPackedDims(const DataType* type,
                                             uint32_t width, SimContext& ctx) {
  PackedDims dims = WrittenPackedDims(type, ctx);
  if (dims.empty()) return std::nullopt;
  const int64_t kSpan = PackedDimsWidth(dims);
  if (kSpan == width) return dims;
  if (kSpan == 0 || width % kSpan != 0) return std::nullopt;
  dims.push_back(PackedRange::Implicit(static_cast<uint32_t>(width / kSpan)));
  return dims;
}

}  // namespace delta
