#include <cstdint>
#include <optional>
#include <string>

#include "common/arena.h"
#include "common/packed_range.h"
#include "common/types.h"
#include "elaborator/rtlir.h"
#include "parser/ast_type.h"
#include "simulator/evaluation.h"
#include "simulator/instance_prefix_override.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_design_walk.h"
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

// §11.5.1: the packed range `type` declares, evaluated in the scope the attach
// set, where it accounts for all `width` bits; null where the declaration
// writes none, which leaves the object without bits, or a range the width does
// not match, as the dimensions of a packed array do.
std::optional<PackedRange> DeclaredRange(const DataType* type, uint32_t width,
                                         SimContext& ctx) {
  if (type == nullptr || type->packed_dim_left == nullptr ||
      type->packed_dim_right == nullptr) {
    return std::nullopt;
  }
  Arena& arena = ctx.GetArena();
  const PackedRange kRange{
      BoundValue(EvalExpr(type->packed_dim_left, ctx, arena)),
      BoundValue(EvalExpr(type->packed_dim_right, ctx, arena))};
  if (kRange.HighIndex() - kRange.LowIndex() + 1 != width) {
    return std::nullopt;
  }
  return kRange;
}

// Whether §37.17 detail 12 gives a variable of `type` bits: a logic or bit
// variable, or a packed array of them.
bool HasVarBits(int type) {
  return type == kVpiReg || type == vpiBitVar || type == vpiPackedArrayVar;
}

}  // namespace

void VpiContext::MakeVectorBits(VpiObject* parent, int bit_type,
                                const PackedRange& range) {
  // The bits stand in declaration order, the left index first.
  const auto kWidth =
      static_cast<int64_t>(range.HighIndex() - range.LowIndex() + 1);
  Arena& arena = sim_ctx_->GetArena();
  for (int64_t offset = kWidth - 1; offset >= 0; --offset) {
    const int64_t kIndex = range.IndexAtOffset(offset);
    VpiObject* bit = AllocObject();
    bit->type = bit_type;
    bit->parent = parent;
    bit->var = parent->var;
    bit->net = parent->net;
    bit->bit_offset = static_cast<int>(offset);
    bit->size = 1;
    bit->index = static_cast<int>(kIndex);
    name_pool_.emplace_back(std::string(parent->name) + "[" +
                            std::to_string(kIndex) + "]");
    bit->name = name_pool_.back();
    bit->full_name = parent->full_name + "[" + std::to_string(kIndex) + "]";
    // §37.16 and §37.17 detail 13: vpiIndex reaches the bit's index.
    VpiObject* index = AllocObject();
    index->type = vpiConstant;
    index->const_type = vpiIntConst;
    auto* storage = arena.Create<Variable>();
    storage->value = MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(kIndex));
    index->var = storage;
    index->size = 32;
    bit->index_expr = index;
    parent->children.push_back(bit);
  }
}

void VpiContext::AttachVectorBits(const RtlirDesign* design) {
  // §37.16 and §37.17: a vector net has a net bit per bit and a packed logic or
  // bit variable a var bit per bit, each reached by its index (§38.19) and
  // holding that bit of its parent's value. A run made none, so neither the
  // vpiBit iteration nor an index reached a bit of any object.
  if (design == nullptr || sim_ctx_ == nullptr) return;
  SimContext& ctx = *sim_ctx_;
  WalkInstancePaths(
      design, [&](const RtlirModule* mod, const std::string& prefix) {
        // The range is the declaration's, read in the instance's own scope,
        // where its parameters have their instance's values.
        InstancePrefixOverride scope(ctx.InstancePrefixOverride(),
                                     prefix.empty() ? "" : prefix + ".");
        for (const RtlirNet& net : mod->nets) {
          VpiHandle obj =
              FindObjectForFlatName(object_map_, VpiFlatName(prefix, net.name));
          if (obj == nullptr || obj->type != kVpiNet) continue;
          auto range = DeclaredRange(net.dtype, net.width, ctx);
          if (range) MakeVectorBits(obj, vpiNetBit, *range);
        }
        for (const RtlirVariable& var : mod->variables) {
          VpiHandle obj =
              FindObjectForFlatName(object_map_, VpiFlatName(prefix, var.name));
          if (obj == nullptr || !HasVarBits(obj->type)) continue;
          auto range = DeclaredRange(var.dtype, var.width, ctx);
          if (range) MakeVectorBits(obj, vpiRegBit, *range);
        }
      });
}

}  // namespace delta
