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

// The packed dimensions a type writes, each a left and a right bound, outermost
// first.
using PackedDims = std::vector<std::pair<Expr*, Expr*>>;

// §6.11 and §6.12 name the integral and real types the standard defines, each
// of which a type actual may be written as; the keyword each such kind is
// spelled by in a specialization's key, whatever name the type carries. Empty
// for a kind no type actual is written as -- a net type, a void -- and for the
// named and inline aggregate kinds, which TypeActualKey spells for itself.
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

// §6.18 with §6.22.1: the built-in type at the end of the chain of typedefs
// the name `type` writes, `int` for `word_t` under `typedef int word_t;`.
// Null where `type` names no typedef, where the chain ends at no built-in
// type -- a class, an enum, a struct -- and where a step on it writes a
// parameter list or declares unpacked dimensions, `typedef int iq_t[$];`
// standing for a queue of int rather than for int. Each packed dimension a
// step writes is appended to `dims`, the use-site's ahead of the typedef's,
// since §7.4.4 stacks a dimension written where the name is used outside the
// ones the typedef carries.
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

// §6.11 (printed page 109): whether the integral built-in `kind` is
// 4-state, and the width it is predefined to have, 0 for bit, logic and reg,
// which take theirs from their packed dimensions; §6.11.2 makes logic and reg
// one type. Nullopt for a kind that is no integral built-in type.
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

// §7.4.1 with §6.22.1: the bounds of the packed dimensions `dims` lists,
// outermost first, each spelled "[left:right]". Nullopt where a bound cannot be
// folded here or the bounds do not account for the `width` bits the type was
// sized with, as RecordPackedRange (lowerer_register.cpp) declines such bounds
// for a variable; the caller then spells the type by its width alone.
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

// §6.22.1 (printed page 135): an integral built-in type spelled by what makes
// two such types match -- 2- or 4-state, signed or not, and the bounds of each
// packed dimension -- as the simple bit vector it matches, rule e) spelling a
// type with a predefined width as the vector ranged [width-1:0] and rule g)
// taking the signing a type ends with, however written. So `byte` and `bit
// signed [7:0]` are both "bit signed[7:0]", `integer` and `logic signed
// [31:0]` both "logic signed[31:0]", and `bit [2:0]` and `bit [3:1]`, which
// rule f) keeps apart by their bounds, two keys. A scalar is the vector ranged
// [0:0], and a type nothing sizes is spelled with no bounds. `form` is the
// state and predefined width IntegralKindForm answers for `builtin`'s kind.
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
