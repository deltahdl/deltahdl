#include "simulator/class_specialization_key.h"

#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/types.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

namespace delta {

namespace {

using PackedDims = std::vector<std::pair<Expr*, Expr*>>;

std::string_view BuiltinTypeKeyword(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kLogic:
      return "logic";
    case DataTypeKind::kReg:
      return "reg";
    case DataTypeKind::kBit:
      return "bit";
    case DataTypeKind::kByte:
      return "byte";
    case DataTypeKind::kShortint:
      return "shortint";
    case DataTypeKind::kInt:
      return "int";
    case DataTypeKind::kLongint:
      return "longint";
    case DataTypeKind::kInteger:
      return "integer";
    case DataTypeKind::kReal:
      return "real";
    case DataTypeKind::kShortreal:
      return "shortreal";
    case DataTypeKind::kTime:
      return "time";
    case DataTypeKind::kRealtime:
      return "realtime";
    case DataTypeKind::kString:
      return "string";
    case DataTypeKind::kEvent:
      return "event";
    case DataTypeKind::kChandle:
      return "chandle";
    case DataTypeKind::kVoid:
      return "void";
    default:
      return {};
  }
}

const DataType* BuiltinTypedefTarget(const DataType& type, SimContext& ctx,
                                     PackedDims& dims) {
  const DataType* step = &type;
  for (size_t hops = 0; hops <= ctx.TypeDeclarationCount(); ++hops) {
    if (step->packed_dim_left != nullptr) {
      dims.emplace_back(step->packed_dim_left, step->packed_dim_right);
      dims.insert(dims.end(), step->extra_packed_dims.begin(),
                  step->extra_packed_dims.end());
    }
    if (step->kind != DataTypeKind::kNamed)
      return BuiltinTypeKeyword(step->kind).empty() ? nullptr : step;
    if (!step->type_params.empty()) return nullptr;
    const ModuleItem* item = TypedefItemSeenFrom(*step, nullptr, ctx);
    if (item == nullptr || !item->unpacked_dims.empty()) return nullptr;
    step = &item->typedef_type;
  }
  return nullptr;
}

std::optional<std::pair<bool, uint32_t>> IntegralKindForm(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kBit:
      return std::pair{false, 0u};
    case DataTypeKind::kLogic:
    case DataTypeKind::kReg:
      return std::pair{true, 0u};
    case DataTypeKind::kByte:
      return std::pair{false, 8u};
    case DataTypeKind::kShortint:
      return std::pair{false, 16u};
    case DataTypeKind::kInt:
      return std::pair{false, 32u};
    case DataTypeKind::kLongint:
      return std::pair{false, 64u};
    case DataTypeKind::kInteger:
      return std::pair{true, 32u};
    case DataTypeKind::kTime:
      return std::pair{true, 64u};
    default:
      return std::nullopt;
  }
}

std::optional<std::string> PackedBoundsKey(const PackedDims& dims,
                                           uint32_t width, SimContext& ctx) {
  std::string key;
  uint64_t bits = 1;
  for (const auto& [left, right] : dims) {
    if (left == nullptr || right == nullptr) return std::nullopt;
    Logic4Vec lv = EvalExpr(left, ctx, ctx.GetArena());
    Logic4Vec rv = EvalExpr(right, ctx, ctx.GetArena());
    if (HasUnknownBits(lv) || HasUnknownBits(rv)) return std::nullopt;
    int64_t l = SelectBoundValue(lv);
    int64_t r = SelectBoundValue(rv);
    bits *= static_cast<uint64_t>((l >= r ? l - r : r - l) + 1);
    key += "[" + std::to_string(l) + ":" + std::to_string(r) + "]";
  }
  if (bits != width) return std::nullopt;
  return key;
}

std::string IntegralTypeKey(const DataType& builtin,
                            std::pair<bool, uint32_t> form,
                            const PackedDims& dims, uint32_t width,
                            SimContext& ctx) {
  const auto [four_state, predefined] = form;
  std::string key = four_state ? "logic" : "bit";
  if (builtin.is_signed) key += " signed";
  if (width == 0) return key;
  std::optional<std::string> bounds;
  if (predefined == 0) bounds = PackedBoundsKey(dims, width, ctx);
  if (!bounds.has_value() || bounds->empty())
    bounds = "[" + std::to_string(width - 1) + ":0]";
  return key + *bounds;
}

}  // namespace

std::string TypeActualKey(const ClassDecl* decl, size_t i,
                          const DataType* actual, SimContext& ctx) {
  const DataType* type = actual;
  if (type == nullptr)
    type = i < decl->param_types.size() ? &decl->param_types[i] : nullptr;
  if (type == nullptr) return {};
  PackedDims dims;
  const DataType* builtin = BuiltinTypedefTarget(*type, ctx, dims);
  if (builtin == nullptr) return std::string(type->type_name);
  if (const auto kForm = IntegralKindForm(builtin->kind)) {
    return IntegralTypeKey(*builtin, *kForm, dims,
                           DeclaredTypeWidth(*type, ctx), ctx);
  }
  if (builtin->kind == DataTypeKind::kRealtime) return "real";
  return std::string(BuiltinTypeKeyword(builtin->kind));
}

}  // namespace delta
