#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <utility>
#include <vector>

#include "common/packed_range.h"
#include "common/types.h"
#include "elaborator/rtlir.h"
#include "parser/ast_type.h"
#include "simulator/instance_prefix_override.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_design_attach_build.h"
#include "simulator/vpi_design_walk.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {

std::vector<RtlirNet> VpiDeclaredNets(const RtlirModule& mod) {
  std::vector<RtlirNet> nets = mod.nets;
  for (const RtlirPort& port : mod.ports) {
    // A variable port, an interface port among them, declares no net, and an
    // interconnect port's net is made apart (FillInterconnectNetObject).
    if (port.net_type == NetType::kNone || port.is_interconnect) continue;
    const bool kDeclared = std::ranges::any_of(
        mod.nets, [&](const RtlirNet& net) { return net.name == port.name; });
    if (kDeclared) continue;
    RtlirNet& net = nets.emplace_back();
    net.name = port.name;
    net.width = port.width;
    net.dtype = port.dtype;
    net.data_kind = port.data_kind;
    // An inline enum holds its base type's range where a dimension written over
    // a named type or a struct or union is held (§37.16 detail 1).
    net.has_declared_packed_dim = port.dtype != nullptr &&
                                  port.dtype->packed_dim_left != nullptr &&
                                  port.dtype->kind != DataTypeKind::kEnum;
    net.num_unpacked_dims = port.num_unpacked_dims;
    net.unpacked_dims = port.unpacked_dims;
  }
  return nets;
}

std::vector<RtlirVariable> VpiDeclaredVariables(const RtlirModule& mod) {
  std::vector<RtlirVariable> vars = mod.variables;
  for (const RtlirPort& port : mod.ports) {
    // A net port declares a net, and an interface port (§25.3) no variable.
    if (port.net_type != NetType::kNone || port.is_interface_port) continue;
    // A structure or union port already declares its variable (§7.2.1).
    const bool kDeclared = std::ranges::any_of(
        mod.variables,
        [&](const RtlirVariable& var) { return var.name == port.name; });
    if (kDeclared) continue;
    RtlirVariable& var = vars.emplace_back();
    var.name = port.name;
    var.width = port.width;
    var.dtype = port.dtype;
    var.decl_kind = port.data_kind;
    var.is_real = port.data_kind == DataTypeKind::kReal ||
                  port.data_kind == DataTypeKind::kRealtime;
    var.is_string = port.data_kind == DataTypeKind::kString;
    var.num_unpacked_dims = port.num_unpacked_dims;
    var.unpacked_dims = port.unpacked_dims;
  }
  return vars;
}

std::vector<std::string> VpiDeclaredNetKeys(const RtlirNet& net,
                                            const std::string& prefix) {
  const std::string kKey = VpiFlatName(prefix, net.name);
  if (net.num_unpacked_dims == 0) return {kKey};
  std::vector<std::string> keys;
  if (net.unpacked_dims.size() != 1) return keys;
  const RtlirUnpackedDim& dim = net.unpacked_dims.front();
  for (int64_t i = dim.Low(); i < dim.Low() + dim.Size(); ++i) {
    keys.push_back(kKey + "[" + std::to_string(i) + "]");
  }
  return keys;
}

namespace {

// Whether §37.17 detail 12 gives `obj` bits: a logic or bit variable, a packed
// array of them, or a packed struct or union, which detail 20 makes a vector.
bool HasVarBits(const VpiObject& obj) {
  if (obj.type == kVpiReg || obj.type == vpiBitVar ||
      obj.type == vpiPackedArrayVar) {
    return true;
  }
  return (obj.type == vpiStructVar || obj.type == vpiUnionVar) &&
         obj.decl_vector;
}

// The bits of a variable: those its packed dimensions index, or for a packed
// struct or union declared with none, its implicit [n-1:0] (§7.2.1).
std::optional<PackedDims> VarBitDims(const VpiObject& obj,
                                     const RtlirVariable& var,
                                     SimContext& ctx) {
  auto dims = DeclaredPackedDims(var.dtype, var.width, ctx);
  if (dims || obj.type == kVpiReg || obj.type == vpiBitVar || var.width == 0) {
    return dims;
  }
  return PackedDims{PackedRange::Implicit(var.width)};
}

// One object a vector's bits hang from, the kind of bit it has and the
// dimensions they are indexed by.
struct BitTarget {
  VpiObject* parent;
  int bit_type;
  PackedDims dims;
};

// The nets the instance at `prefix` declares that have bits, its vector nets.
void AddNetBitTargets(const RtlirModule* mod, const std::string& prefix,
                      const VpiObjectMap& objects, SimContext& ctx,
                      std::vector<BitTarget>& targets) {
  for (const RtlirNet& net : VpiDeclaredNets(*mod)) {
    auto dims = DeclaredPackedDims(net.dtype, net.width, ctx);
    if (!dims) continue;
    for (const std::string& key : VpiDeclaredNetKeys(net, prefix)) {
      VpiHandle obj = FindObjectForFlatName(objects, key);
      if (obj == nullptr || obj->type != kVpiNet) continue;
      targets.push_back({obj, vpiNetBit, *dims});
    }
  }
}

// The objects of the instance at `prefix` that have bits: its vector nets and
// its packed logic and bit variables. The ranges are the declarations', read in
// the instance's own scope, where its parameters have their instance's values.
std::vector<BitTarget> BitTargets(const RtlirModule* mod,
                                  const std::string& prefix,
                                  const VpiObjectMap& objects,
                                  SimContext& ctx) {
  InstancePrefixOverride scope(ctx.InstancePrefixOverride(),
                               prefix.empty() ? "" : prefix + ".");
  std::vector<BitTarget> targets;
  AddNetBitTargets(mod, prefix, objects, ctx, targets);
  for (const RtlirVariable& var : VpiDeclaredVariables(*mod)) {
    VpiHandle obj =
        FindObjectForFlatName(objects, VpiFlatName(prefix, var.name));
    if (obj == nullptr || !HasVarBits(*obj)) continue;
    auto dims = VarBitDims(*obj, var, ctx);
    if (dims) targets.push_back({obj, vpiRegBit, std::move(*dims)});
  }
  return targets;
}

// The indices, outermost first, naming the bit `offset` places above the least
// significant end of a value of `dims`.
std::vector<int64_t> IndicesAtOffset(const PackedDims& dims, int64_t offset) {
  std::vector<int64_t> indices(dims.size());
  for (std::size_t k = dims.size(); k-- > 0;) {
    const int64_t kSize = dims[k].HighIndex() - dims[k].LowIndex() + 1;
    indices[k] = dims[k].IndexAtOffset(offset % kSize);
    offset /= kSize;
  }
  return indices;
}

// §37.16, §37.17: the bits of `target.parent`, in declaration order with the
// left index first, each holding its offset into the parent's storage, size 1
// and its index, which vpiIndex reaches as a constant (detail 13). Of a value
// with more than one packed dimension, a bit is named by an index in each, and
// its index is the innermost. A var bit's vpiIndex iteration reaches its
// indices, starting with its own and working outward. The parent keeps the
// dimensions, which a select of it indexes.
void MakeVectorBits(const BitTarget& target, const VpiAttachBuild& build) {
  VpiObject* parent = target.parent;
  parent->packed_dims = target.dims;
  for (int64_t offset = PackedDimsWidth(target.dims) - 1; offset >= 0;
       --offset) {
    const std::vector<int64_t> kIndices = IndicesAtOffset(target.dims, offset);
    std::string suffix;
    for (int64_t index : kIndices) suffix += "[" + std::to_string(index) + "]";
    VpiObject* bit = build.alloc();
    bit->type = target.bit_type;
    bit->parent = parent;
    bit->var = parent->var;
    bit->net = parent->net;
    bit->bit_offset = static_cast<int>(offset);
    bit->size = 1;
    bit->index = static_cast<int>(kIndices.back());
    bit->name = build.keep(std::string(parent->name) + suffix);
    bit->full_name = parent->full_name + suffix;
    bit->index_expr = VpiIntConstant(kIndices.back(), build);
    if (target.bit_type == vpiRegBit) {
      bit->children.push_back(bit->index_expr);
      for (std::size_t k = kIndices.size() - 1; k-- > 0;) {
        bit->children.push_back(VpiIntConstant(kIndices[k], build));
      }
    }
    parent->children.push_back(bit);
  }
}

}  // namespace

void AttachVectorBits(const RtlirDesign* design, const VpiObjectMap& objects,
                      SimContext& ctx, const VpiAttachBuild& build) {
  // §37.16 and §37.17: a vector net has a net bit per bit and a packed logic or
  // bit variable a var bit per bit, each reached by its index (§38.19) and
  // holding that bit of its parent's value. A run made none, so neither the
  // vpiBit iteration nor an index reached a bit of any object.
  if (design == nullptr) return;
  WalkInstancePaths(
      design, [&](const RtlirModule* mod, const std::string& prefix) {
        for (const BitTarget& target : BitTargets(mod, prefix, objects, ctx)) {
          MakeVectorBits(target, build);
        }
      });
}

}  // namespace delta
