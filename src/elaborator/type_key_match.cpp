#include "elaborator/type_key_match.h"

#include <array>
#include <cstdint>
#include <optional>
#include <string_view>
#include <tuple>
#include <vector>

#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/net_data_type.h"
#include "elaborator/type_eval.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

// §6.22.1: what decides whether two integral types match -- whether each
// is 4-state, whether it is signed, and the range of its one dimension.
struct IntegralShape {
  bool four_state;
  bool is_signed;
  int64_t left;
  int64_t right;
};

bool SameShape(const IntegralShape& a, const IntegralShape& b) {
  return std::tie(a.four_state, a.is_signed, a.left, a.right) ==
         std::tie(b.four_state, b.is_signed, b.left, b.right);
}

struct IntegerAtom {
  std::string_view keyword;
  DataTypeKind kind;
  IntegralShape shape;
};

// §6.11: the integer atom types, each a vector of predefined width.
constexpr std::array<IntegerAtom, 6> kIntegerAtoms = {{
    {"byte", DataTypeKind::kByte, {false, true, 7, 0}},
    {"shortint", DataTypeKind::kShortint, {false, true, 15, 0}},
    {"int", DataTypeKind::kInt, {false, true, 31, 0}},
    {"longint", DataTypeKind::kLongint, {false, true, 63, 0}},
    {"integer", DataTypeKind::kInteger, {true, true, 31, 0}},
    {"time", DataTypeKind::kTime, {true, false, 63, 0}},
}};

std::optional<IntegralShape> AtomShapeOfKeyword(std::string_view key) {
  for (const IntegerAtom& atom : kIntegerAtoms)
    if (atom.keyword == key) return atom.shape;
  return std::nullopt;
}

// The shape of an integer atom type or of a bit, logic or reg vector of at most
// one packed dimension whose bounds fold, nothing for any other type.
std::optional<IntegralShape> IntegralShapeOf(const DataType& t) {
  for (const IntegerAtom& atom : kIntegerAtoms)
    if (atom.kind == t.kind) return atom.shape;
  if (t.kind != DataTypeKind::kBit && t.kind != DataTypeKind::kLogic &&
      t.kind != DataTypeKind::kReg)
    return std::nullopt;
  if (!t.extra_packed_dims.empty()) return std::nullopt;
  IntegralShape shape{t.kind != DataTypeKind::kBit, t.is_signed, 0, 0};
  if (t.packed_dim_left == nullptr) return shape;
  auto left = ConstEvalInt(t.packed_dim_left);
  auto right = ConstEvalInt(t.packed_dim_right);
  if (!left || !right) return std::nullopt;
  shape.left = *left;
  shape.right = *right;
  return shape;
}

// §6.22.1: a vector type of predefined width -- an integer atom -- matches
// a bit, logic or reg vector of the same state and signedness over the range
// [width-1:0], and two such vectors match when their ranges are the same.
bool IntegralShapesMatch(const std::optional<IntegralShape>& a,
                         const DataType& b) {
  std::optional<IntegralShape> shape = IntegralShapeOf(b);
  return a.has_value() && shape.has_value() && SameShape(*a, *shape);
}

}  // namespace

bool IsTypeKey(std::string_view key, const TypedefMap& typedefs) {
  return IsTypeKeyword(key) || typedefs.count(key) != 0;
}

bool TypeKeyMatchesType(std::string_view key, const DataType& type,
                        const TypedefMap& typedefs) {
  std::vector<std::string_view> names;
  const DataType* t = FollowTypedefs(type, typedefs, names);
  if (t == nullptr) return false;
  auto it = typedefs.find(key);
  if (it == typedefs.end()) {
    if (TypeKeyMatchesKind(key, t->kind) && t->packed_dim_left == nullptr)
      return true;
    return IntegralShapesMatch(AtomShapeOfKeyword(key), *t);
  }
  const DataType* k = FollowTypedefs(it->second, typedefs, names);
  if (k == nullptr) return false;
  // §6.22.1 (c) and (d): an enum, structure or union matches only a type of
  // the same declaration.
  if (k->decl_loc.IsValid() || t->decl_loc.IsValid()) {
    return std::tie(k->decl_loc.file_id, k->decl_loc.line,
                    k->decl_loc.column) ==
           std::tie(t->decl_loc.file_id, t->decl_loc.line, t->decl_loc.column);
  }
  if (IntegralShapeOf(*k).has_value())
    return IntegralShapesMatch(IntegralShapeOf(*k), *t);
  return k->kind == t->kind &&
         EvalTypeWidth(*k, typedefs) == EvalTypeWidth(*t, typedefs);
}

bool TypeKeyMatchesMember(std::string_view key, const StructMember& member,
                          const TypedefMap& typedefs) {
  if (!member.unpacked_dims.empty()) return false;
  if (member.nested_type != nullptr)
    return TypeKeyMatchesType(key, *member.nested_type, typedefs);
  DataType dt;
  dt.kind = member.type_kind;
  dt.type_name = member.type_name;
  dt.packed_dim_left = member.packed_dim_left;
  dt.packed_dim_right = member.packed_dim_right;
  dt.extra_packed_dims = member.extra_packed_dims;
  return TypeKeyMatchesType(key, dt, typedefs);
}

}  // namespace delta
