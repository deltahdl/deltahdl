#include "simulator/pattern_type_key.h"

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <string_view>

#include "common/arena.h"
#include "common/packed_range.h"
#include "elaborator/rtlir.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign_internal.h"

namespace delta {

namespace {

// §6.11 and §6.12: each built-in type keyword a type key may be, with the
// width and signing its type has.
struct KeywordType {
  std::string_view keyword;
  DataTypeKind kind;
  uint32_t width;
  bool is_signed;
};

constexpr std::array<KeywordType, 13> kKeywordTypes = {{
    {"bit", DataTypeKind::kBit, 1, false},
    {"logic", DataTypeKind::kLogic, 1, false},
    {"reg", DataTypeKind::kReg, 1, false},
    {"byte", DataTypeKind::kByte, 8, true},
    {"shortint", DataTypeKind::kShortint, 16, true},
    {"int", DataTypeKind::kInt, 32, true},
    {"longint", DataTypeKind::kLongint, 64, true},
    {"integer", DataTypeKind::kInteger, 32, true},
    {"time", DataTypeKind::kTime, 64, false},
    {"shortreal", DataTypeKind::kShortreal, 32, false},
    {"real", DataTypeKind::kReal, 64, false},
    {"realtime", DataTypeKind::kRealtime, 64, false},
    {"string", DataTypeKind::kString, 0, false},
}};

// §6.11: the integral kinds, the 4-state ones among them, and the ones
// §6.11.1 makes signed by default.
constexpr std::array<DataTypeKind, 9> kIntegralKinds = {
    DataTypeKind::kBit,     DataTypeKind::kLogic,    DataTypeKind::kReg,
    DataTypeKind::kByte,    DataTypeKind::kShortint, DataTypeKind::kInt,
    DataTypeKind::kLongint, DataTypeKind::kInteger,  DataTypeKind::kTime};
constexpr std::array<DataTypeKind, 4> kFourStateKinds = {
    DataTypeKind::kLogic, DataTypeKind::kReg, DataTypeKind::kInteger,
    DataTypeKind::kTime};
constexpr std::array<DataTypeKind, 5> kSignedKinds = {
    DataTypeKind::kByte, DataTypeKind::kShortint, DataTypeKind::kInt,
    DataTypeKind::kLongint, DataTypeKind::kInteger};
constexpr std::array<DataTypeKind, 3> kNominalKinds = {
    DataTypeKind::kStruct, DataTypeKind::kUnion, DataTypeKind::kEnum};

// The entry of kKeywordTypes for `name`; null where `name` is no keyword.
const KeywordType* FindKeywordType(std::string_view name) {
  for (const KeywordType& k : kKeywordTypes) {
    if (k.keyword == name) return &k;
  }
  return nullptr;
}

template <size_t N>
bool KindIn(const std::array<DataTypeKind, N>& kinds, DataTypeKind kind) {
  return std::ranges::find(kinds, kind) != kinds.end();
}

}  // namespace

DataTypeKind PatternKeyKeywordKind(std::string_view key) {
  const KeywordType* k = FindKeywordType(key);
  return k != nullptr ? k->kind : DataTypeKind::kImplicit;
}

std::optional<PatternKeyType> ResolvePatternKeyType(std::string_view key,
                                                    const SimContext& ctx) {
  if (const KeywordType* k = FindKeywordType(key))
    return PatternKeyType{
        k->kind, k->width, k->is_signed, PackedRange::Implicit(k->width), {}};
  DataTypeKind kind = ctx.FindTypeKind(key);
  if (kind == DataTypeKind::kNamed) return std::nullopt;
  uint32_t width = ctx.FindTypeWidth(key);
  return PatternKeyType{
      kind, width, ctx.FindTypeSigned(key),
      ctx.FindTypeRange(key).value_or(PackedRange::Implicit(width)), key};
}

bool PatternKeyMatches(const PatternKeyType& key,
                       const PatternKeySubject& subject) {
  if (subject.is_array) return false;
  if (!key.name.empty() && key.name == subject.type_name) return true;
  if (KindIn(kIntegralKinds, key.kind) &&
      KindIn(kIntegralKinds, subject.kind)) {
    PackedRange range = subject.range.value_or(PackedRange{});
    return KindIn(kFourStateKinds, key.kind) ==
               KindIn(kFourStateKinds, subject.kind) &&
           key.width == subject.width &&
           key.is_signed == subject.is_signed.value_or(false) &&
           key.range.left == range.left && key.range.right == range.right;
  }
  // A structure, union or enum type matches only itself, the name compared
  // above.
  if (KindIn(kNominalKinds, key.kind)) return false;
  return key.kind == subject.kind;
}

PatternKeySubject SubjectOf(PatternKeySubject subject, const SimContext& ctx) {
  // A type written as a keyword carries the keyword as its type_name too, so
  // a name is a typedef's only where it is no keyword; read as one, `int`'s
  // signing came from a typedef table holding no `int`, and an int element
  // took no `int:` key.
  bool named = !subject.type_name.empty() &&
               FindKeywordType(subject.type_name) == nullptr;
  if (subject.kind == DataTypeKind::kNamed)
    subject.kind = ctx.FindTypeKind(subject.type_name);
  if (!subject.is_signed) {
    subject.is_signed = named ? ctx.FindTypeSigned(subject.type_name)
                              : KindIn(kSignedKinds, subject.kind);
  }
  if (!subject.range && named)
    subject.range = ctx.FindTypeRange(subject.type_name);
  if (!subject.range) subject.range = PackedRange::Implicit(subject.width);
  return subject;
}

PatternKeySubject SubjectOfElement(const ArrayInfo& info,
                                   const SimContext& ctx) {
  return SubjectOf({.kind = info.elem_type_kind,
                    .width = info.elem_width,
                    .is_signed = info.elem_is_signed,
                    .type_name = info.elem_type_name,
                    .range = info.elem_range},
                   ctx);
}

PatternKeySubject SubjectOfField(const StructFieldInfo& field,
                                 const SimContext& ctx) {
  // §10.9.2 with §10.9.1: a key reaches an unpacked array member through the
  // rules for arrays, so it is matched against one element's type.
  uint32_t width =
      field.elem_count > 0 ? field.width / field.elem_count : field.width;
  std::optional<PackedRange> range = field.decl_range;
  if (field.packed_elem_width > 0)
    range = PackedRange{field.packed_left, field.packed_right};
  // A member written as a typedef name takes the typedef's signing.
  std::optional<bool> is_signed = field.is_signed;
  if (field.type_kind == DataTypeKind::kNamed) is_signed = std::nullopt;
  return SubjectOf({.kind = field.type_kind,
                    .width = width,
                    .is_signed = is_signed,
                    .type_name = field.type_name,
                    .range = range,
                    .is_array = field.is_dynamic},
                   ctx);
}

// §10.9.1: the typedef name an array's element type was written as, which a
// type key of its pattern names; empty for a built-in type.
static std::string_view ElementTypeName(const RtlirVariable& var) {
  return var.written_type == nullptr ? std::string_view{}
                                     : var.written_type->type_name;
}

// §6.22.1: the bounds of the outermost packed dimension the array's element
// type writes, folded as RecordPackedRange folds them for each element; empty
// for an element type written with none, whose typedef or width gives them.
static std::optional<PackedRange> ElementRange(const RtlirVariable& var,
                                               SimContext& ctx, Arena& arena) {
  const DataType* dt =
      var.dtype != nullptr ? ctx.PackedTypeBehind(*var.dtype) : nullptr;
  if (dt == nullptr || dt->packed_dim_left == nullptr ||
      dt->packed_dim_right == nullptr)
    return std::nullopt;
  return PackedRange{
      SelectBoundValue(EvalExpr(dt->packed_dim_left, ctx, arena)),
      SelectBoundValue(EvalExpr(dt->packed_dim_right, ctx, arena))};
}

PatternKeySubject SubjectOfVariableElement(const RtlirVariable& var,
                                           SimContext& ctx, Arena& arena) {
  return SubjectOf({.kind = var.elem_type_kind,
                    .width = var.width,
                    .is_signed = var.is_signed,
                    .type_name = ElementTypeName(var),
                    .range = ElementRange(var, ctx, arena)},
                   ctx);
}

void RecordElementType(ArrayInfo& info, const RtlirVariable& var,
                       SimContext& ctx, Arena& arena) {
  info.elem_type_kind = var.elem_type_kind;
  info.elem_type_name = ElementTypeName(var);
  info.elem_is_signed = var.is_signed;
  info.elem_range = ElementRange(var, ctx, arena);
}

bool PatternHasTypeKey(const Expr* pattern, const SimContext& ctx) {
  return std::ranges::any_of(pattern->pattern_keys, [&](const Expr* key) {
    return ResolvePatternKeyType(key->text, ctx).has_value();
  });
}

const Expr* IndexKeyedItem(const Expr* pattern, uint32_t idx, SimContext& ctx,
                           Arena& arena) {
  size_t keyed =
      std::min(pattern->pattern_keys.size(), pattern->elements.size());
  for (size_t i = 0; i < keyed; ++i) {
    const Expr* key = pattern->pattern_keys[i];
    if (key->text == "default" || ResolvePatternKeyType(key->text, ctx))
      continue;
    if (PatternKeyIndex(key, ctx, arena) == idx) return pattern->elements[i];
  }
  return nullptr;
}

const Expr* TypeKeyedItem(const Expr* pattern, const PatternKeySubject& subject,
                          const SimContext& ctx) {
  size_t keyed =
      std::min(pattern->pattern_keys.size(), pattern->elements.size());
  for (size_t i = keyed; i-- > 0;) {
    auto type = ResolvePatternKeyType(pattern->pattern_keys[i]->text, ctx);
    if (type && PatternKeyMatches(*type, subject)) return pattern->elements[i];
  }
  return nullptr;
}

const Expr* DefaultKeyedItem(const Expr* pattern) {
  size_t keyed =
      std::min(pattern->pattern_keys.size(), pattern->elements.size());
  for (size_t i = 0; i < keyed; ++i)
    if (pattern->pattern_keys[i]->text == "default")
      return pattern->elements[i];
  return nullptr;
}

}  // namespace delta
