#include "elaborator/typename_writer.h"

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <map>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "elaborator/operator_classes.h"
#include "elaborator/rtlir.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

// The keywords the built-in types are written with.
const std::map<DataTypeKind, std::string_view>& BuiltinKeywords() {
  static const std::map<DataTypeKind, std::string_view> kKeywords = {
      {DataTypeKind::kLogic, "logic"},
      {DataTypeKind::kReg, "reg"},
      {DataTypeKind::kBit, "bit"},
      {DataTypeKind::kByte, "byte"},
      {DataTypeKind::kShortint, "shortint"},
      {DataTypeKind::kInt, "int"},
      {DataTypeKind::kLongint, "longint"},
      {DataTypeKind::kInteger, "integer"},
      {DataTypeKind::kTime, "time"},
      {DataTypeKind::kReal, "real"},
      {DataTypeKind::kShortreal, "shortreal"},
      {DataTypeKind::kRealtime, "realtime"},
      {DataTypeKind::kString, "string"},
      {DataTypeKind::kChandle, "chandle"},
      {DataTypeKind::kEvent, "event"}};
  return kKeywords;
}

// The keyword a built-in type is written with, empty for a type that is not
// one.
std::string_view BuiltinKeyword(DataTypeKind kind) {
  auto it = BuiltinKeywords().find(kind);
  return it == BuiltinKeywords().end() ? std::string_view{} : it->second;
}

// Step c's struct, union and enum: the kinds $typename writes out with their
// bodies, packed or not, rather than by a keyword.
bool IsStructUnionOrEnumKind(DataTypeKind kind) {
  return kind == DataTypeKind::kEnum || kind == DataTypeKind::kStruct ||
         kind == DataTypeKind::kUnion;
}

// §6.11: the integer atom types other than `time` are signed by default, and
// the integer vector types and `time` unsigned.
bool SignedByDefault(DataTypeKind kind) {
  static constexpr std::array kSigned = {
      DataTypeKind::kByte, DataTypeKind::kShortint, DataTypeKind::kInt,
      DataTypeKind::kLongint, DataTypeKind::kInteger};
  return std::ranges::find(kSigned, kind) != kSigned.end();
}

// Step b: the default signing is removed, so an integral type's signing is
// written only where it differs from its kind's.
std::string_view SigningText(DataTypeKind kind, bool is_signed) {
  static constexpr std::array kIntegral = {
      DataTypeKind::kLogic,   DataTypeKind::kReg,      DataTypeKind::kBit,
      DataTypeKind::kByte,    DataTypeKind::kShortint, DataTypeKind::kInt,
      DataTypeKind::kLongint, DataTypeKind::kInteger,  DataTypeKind::kTime};
  if (std::ranges::find(kIntegral, kind) == kIntegral.end() ||
      is_signed == SignedByDefault(kind)) {
    return {};
  }
  return is_signed ? " signed" : " unsigned";
}

// The built-in type the name `name` spells, signed as its keyword is by
// default; nothing where `name` is no keyword's name.
std::optional<DataType> KeywordType(const Expr* name) {
  if (name->kind != ExprKind::kIdentifier) return std::nullopt;
  for (const auto& [kind, keyword] : BuiltinKeywords()) {
    if (keyword != name->text) continue;
    DataType type;
    type.kind = kind;
    type.is_signed = SignedByDefault(kind);
    return type;
  }
  return std::nullopt;
}

}  // namespace

// What is written of a type: the parts a DataType and a StructMember share.
struct TypenameParts {
  DataTypeKind kind = DataTypeKind::kImplicit;
  bool is_signed = false;
  const Expr* left = nullptr;
  const Expr* right = nullptr;
  const std::vector<std::pair<Expr*, Expr*>>* extra = nullptr;
  std::string_view type_name;
  std::string_view scope_name;
  const DataType* whole = nullptr;
};

namespace {

TypenameParts PartsOf(const DataType& type) {
  TypenameParts parts;
  parts.kind = type.kind;
  parts.is_signed = type.is_signed;
  parts.left = type.packed_dim_left;
  parts.right = type.packed_dim_right;
  parts.extra = &type.extra_packed_dims;
  parts.type_name = type.type_name;
  parts.scope_name = type.scope_name;
  parts.whole = &type;
  return parts;
}

}  // namespace

std::string TypenameWriter::OfType(const DataType& type, std::string_view scope,
                                   std::string_view hint) {
  return OfParts(PartsOf(type), scope, hint);
}

std::string TypenameWriter::OfMember(const StructMember& member,
                                     std::string_view scope) {
  if (member.nested_type != nullptr) {
    return OfType(*member.nested_type, scope, member.name);
  }
  TypenameParts parts;
  parts.kind = member.type_kind;
  parts.is_signed = member.is_signed;
  parts.left = member.packed_dim_left;
  parts.right = member.packed_dim_right;
  parts.extra = &member.extra_packed_dims;
  parts.type_name = member.type_name;
  parts.scope_name = member.scope_name;
  return OfParts(parts, scope, member.name);
}

// Step g: each packed range as unsized decimal bounds.
std::string TypenameWriter::PackedText(const TypenameParts& parts) {
  std::string text;
  if (parts.left != nullptr && parts.right != nullptr) {
    text += RangeText(parts.left, parts.right);
  }
  for (const auto& [left, right] : *parts.extra) {
    text += RangeText(left, right);
  }
  return text;
}

std::string TypenameWriter::RangeText(const Expr* left, const Expr* right) {
  return "[" + std::to_string(env_.value_of(left)) + ":" +
         std::to_string(env_.value_of(right)) + "]";
}

std::string TypenameWriter::OfParts(const TypenameParts& parts,
                                    std::string_view scope,
                                    std::string_view hint) {
  if (parts.kind == DataTypeKind::kNamed) return OfName(parts, scope);
  if (parts.whole != nullptr && IsStructUnionOrEnumKind(parts.kind)) {
    return OfStructUnionOrEnum(*parts.whole,
                               Anonymous(*parts.whole, scope, hint));
  }
  std::string text(BuiltinKeyword(parts.kind));
  if (text.empty()) text = "logic";
  text += SigningText(parts.kind, parts.is_signed);
  return text + PackedText(parts);
}

// Step a: a typedef name is resolved back to the type it names, the
// declaration's own packed ranges written after it; step f: a struct, union
// or enum it names, and a class, keep the name, behind the scope declaring it.
std::string TypenameWriter::OfName(const TypenameParts& parts,
                                   std::string_view scope) {
  std::string prefix = parts.scope_name.empty()
                           ? std::string(scope)
                           : std::string(parts.scope_name) + "::";
  const DataType* named =
      env_.resolve_name(parts.scope_name, parts.type_name, prefix);
  if (named == nullptr) return OfUnresolvedName(parts, prefix);
  if (IsStructUnionOrEnumKind(named->kind)) {
    return OfStructUnionOrEnum(
        *named, TypeOwnerPrefix(prefix) + std::string(parts.type_name));
  }
  return OfType(*named, prefix, parts.type_name) + PackedText(parts);
}

// A name no typedef resolves: a class, named behind the package or
// compilation unit declaring it ("$unit::"), or the module; any other name
// as written.
std::string TypenameWriter::OfUnresolvedName(const TypenameParts& parts,
                                             const std::string& prefix) {
  std::string qualified =
      env_.qualified_class_name(parts.scope_name, parts.type_name);
  if (!qualified.empty()) return qualified;
  return TypeOwnerPrefix(prefix) + std::string(parts.type_name);
}

// Step f: a module's declarations are prefixed with the module's name and a
// dot, a package's with the package and `::`.
std::string TypenameWriter::TypeOwnerPrefix(std::string_view prefix) {
  if (!prefix.empty()) return std::string(prefix);
  return std::string(env_.scope_name()) + ".";
}

// Step c: an anonymous struct, union or enum is named by the system. The clause
// leaves the form to the implementation; this one writes "e$", "s$" or "u$"
// followed by the name of what declares the type, which no other
// declaration of the scope shares.
std::string TypenameWriter::Anonymous(const DataType& type,
                                      std::string_view scope,
                                      std::string_view hint) {
  char letter = type.kind == DataTypeKind::kEnum     ? 'e'
                : type.kind == DataTypeKind::kStruct ? 's'
                                                     : 'u';
  return TypeOwnerPrefix(scope) + letter + "$" + std::string(hint);
}

std::string TypenameWriter::OfStructUnionOrEnum(const DataType& type,
                                                const std::string& name) {
  if (type.kind == DataTypeKind::kEnum) return OfEnum(type) + name;
  std::string text = type.kind == DataTypeKind::kStruct ? "struct" : "union";
  if (type.is_packed) text += " packed";
  text += "{";
  for (const StructMember& member : type.struct_members) {
    text += OfMember(member, "") + " " + std::string(member.name) + ";";
  }
  return text + "}" + name;
}

// Step e: each enumeration constant with its value, sized and signed as the
// base type it is held in.
std::string TypenameWriter::OfEnum(const DataType& type) {
  uint32_t width = 32;
  bool is_signed = true;
  if (type.enum_base_kind != DataTypeKind::kImplicit) {
    DataType base;
    base.kind = type.enum_base_kind;
    base.packed_dim_left = type.packed_dim_left;
    base.packed_dim_right = type.packed_dim_right;
    width = env_.width_of(base);
    // ParseEnumType gives the enumeration the base type's signing.
    is_signed = type.is_signed;
  }
  std::string text = "enum{";
  int64_t next = 0;
  for (size_t i = 0; i < type.enum_members.size(); ++i) {
    const EnumMember& member = type.enum_members[i];
    if (member.value != nullptr) next = env_.value_of(member.value);
    if (i > 0) text += ",";
    text += std::string(member.name) + "=" + std::to_string(width) +
            (is_signed ? "'sd" : "'d") + std::to_string(next);
    ++next;
  }
  return text + "}";
}

std::optional<DataType> KeywordTypeOf(const Expr* arg) {
  if (arg->kind != ExprKind::kSelect) return KeywordType(arg);
  if (arg->index_end == nullptr || arg->is_part_select_plus ||
      arg->is_part_select_minus) {
    return std::nullopt;
  }
  std::optional<DataType> type = KeywordType(arg->base);
  if (type) {
    type->packed_dim_left = arg->index;
    type->packed_dim_right = arg->index_end;
  }
  return type;
}

std::string UnpackedDimsText(const RtlirVariable& var) {
  if (var.num_unpacked_dims == 0 ||
      var.unpacked_dims.size() != var.num_unpacked_dims) {
    return {};
  }
  std::string text = "$";
  for (const RtlirUnpackedDim& dim : var.unpacked_dims) {
    text +=
        "[" + std::to_string(dim.left) + ":" + std::to_string(dim.right) + "]";
  }
  return text;
}

std::string ElementDimsText(std::string_view unpacked) {
  std::string_view rest = unpacked.substr(1);
  rest = rest.substr(rest.find(']') + 1);
  return rest.empty() ? "" : "$" + std::string(rest);
}

namespace {

SelfType SelfTypeOf(const Expr* e, const TypenameEnvironment& env);

// §11.8.1: a bit-select or a part-select of a vector is unsigned whatever the
// vector is, one bit wide or as wide as the range it selects (§11.5.1).
SelfType SelfTypeOfSelect(const Expr* e, const TypenameEnvironment& env) {
  if (e->base == nullptr || e->base->kind != ExprKind::kIdentifier) return {};
  SelfType vector = env.name_self_type(e->base->text);
  if (!vector.known) return {};
  uint32_t width = 1;
  if (e->index_end != nullptr) {
    int64_t end = env.value_of(e->index_end);
    if (e->is_part_select_plus || e->is_part_select_minus) {
      width = static_cast<uint32_t>(end);
    } else {
      int64_t start = env.value_of(e->index);
      width =
          static_cast<uint32_t>((start > end ? start - end : end - start) + 1);
    }
  }
  return {width, false, vector.four_state, true};
}

// §11.4.12 with §11.8.1: a concatenation is unsigned and as wide as its
// operands together.
SelfType SelfTypeOfConcat(const Expr* e, const TypenameEnvironment& env) {
  SelfType whole{0, false, false, true};
  for (const Expr* element : e->elements) {
    SelfType part = SelfTypeOf(element, env);
    if (!part.known) return {};
    whole.width += part.width;
    whole.four_state = whole.four_state || part.four_state;
  }
  return whole;
}

// §11.6.1 Table 11-21 with §11.8.1: a logical negation or a reduction is one
// unsigned bit; any other unary operator is its operand's type.
SelfType SelfTypeOfUnary(const Expr* e, const TypenameEnvironment& env) {
  SelfType operand = SelfTypeOf(e->lhs, env);
  if (!operand.known) return {};
  if (e->op == TokenKind::kBang || IsUnaryReductionOp(e->op)) {
    return {1, false, operand.four_state, true};
  }
  return operand;
}

// §11.6.1 Table 11-21 with §11.8.1: an arithmetic or bitwise operator is as
// wide as its wider operand and signed where both are, a shift or a power is
// its left operand's type, and any other is one unsigned bit; each is 4-state
// where an operand is.
SelfType SelfTypeOfBinary(const Expr* e, const TypenameEnvironment& env) {
  SelfType left = SelfTypeOf(e->lhs, env);
  SelfType right = SelfTypeOf(e->rhs, env);
  if (!left.known || !right.known) return {};
  bool four_state = left.four_state || right.four_state;
  if (IsMaxWidthBinaryOp(e->op)) {
    return {std::max(left.width, right.width),
            left.is_signed && right.is_signed, four_state, true};
  }
  if (IsLeftWidthBinaryOp(e->op)) {
    return {left.width, left.is_signed, four_state, true};
  }
  return {1, false, four_state, true};
}

SelfType SelfTypeOf(const Expr* e, const TypenameEnvironment& env) {
  switch (e->kind) {
    case ExprKind::kIdentifier:
      return env.name_self_type(e->text);
    case ExprKind::kSelect:
      return SelfTypeOfSelect(e, env);
    case ExprKind::kConcatenation:
      return SelfTypeOfConcat(e, env);
    case ExprKind::kUnary:
      return SelfTypeOfUnary(e, env);
    case ExprKind::kBinary:
      return SelfTypeOfBinary(e, env);
    default:
      return {};
  }
}

}  // namespace

std::string TypenameOfOperation(const Expr* arg,
                                const TypenameEnvironment& env) {
  if (env.is_real(arg)) return "real";
  SelfType type = SelfTypeOf(arg, env);
  if (!type.known) return {};
  std::string text = type.four_state ? "logic" : "bit";
  if (type.is_signed) text += " signed";
  if (type.width > 1) text += "[" + std::to_string(type.width - 1) + ":0]";
  return text;
}

}  // namespace delta
