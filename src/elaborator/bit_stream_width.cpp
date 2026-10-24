#include "elaborator/bit_stream_width.h"

#include <cstdint>
#include <cstdlib>
#include <optional>
#include <vector>

#include "elaborator/const_eval.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

namespace delta {

std::optional<uint32_t> FixedDimElementCount(const Expr* dim,
                                             const ScopeMap& scope) {
  if (dim == nullptr) return std::nullopt;
  if (dim->kind == ExprKind::kBinary && dim->op == TokenKind::kColon) {
    auto left = ConstEvalInt(dim->lhs, scope);
    auto right = ConstEvalInt(dim->rhs, scope);
    if (!left || !right) return std::nullopt;
    return static_cast<uint32_t>(std::abs(*left - *right) + 1);
  }
  auto size = ConstEvalInt(dim, scope);
  if (!size || *size <= 0) return std::nullopt;
  return static_cast<uint32_t>(*size);
}

uint32_t FixedUnpackedElementCount(const std::vector<Expr*>& dims) {
  const ScopeMap kNoParameters;
  uint32_t count = 1;
  for (const Expr* dim : dims) {
    auto elements = FixedDimElementCount(dim, kNoParameters);
    if (!elements) return 0;
    count *= *elements;
  }
  return count;
}

namespace {

// The depth bounds a cyclic typedef.
uint32_t BitStreamTypeWidthAt(const DataType& type, const TypedefMap& typedefs,
                              int depth);

// One member's share of an unpacked structure's bit-stream size: its element
// size times its unpacked element count, zero where either is not fixed. A
// string is a dynamic array of bytes to a bit-stream cast (printed page 143),
// so its size is never fixed; the 64 bits EvalStructMemberWidth gives it are
// the simulator's storage for the string's handle.
uint32_t MemberBitStreamWidth(const StructMember& m, const TypedefMap& typedefs,
                              int depth) {
  if (m.type_kind == DataTypeKind::kString) return 0;
  const DataType* member_type =
      m.nested_type != nullptr ? m.nested_type : MemberNamedType(m, typedefs);
  uint32_t element = member_type == nullptr
                         ? EvalStructMemberWidth(m, typedefs)
                         : BitStreamTypeWidthAt(*member_type, typedefs, depth);
  return element * FixedUnpackedElementCount(m.unpacked_dims);
}

uint32_t BitStreamTypeWidthAt(const DataType& type, const TypedefMap& typedefs,
                              int depth) {
  if (depth > 8) return 0;
  if (type.kind == DataTypeKind::kNamed) {
    auto td = typedefs.find(type.type_name);
    if (td == typedefs.end()) return 0;
    return BitStreamTypeWidthAt(td->second, typedefs, depth + 1);
  }
  if (type.kind != DataTypeKind::kStruct || type.is_packed)
    return EvalTypeWidth(type, typedefs);
  uint32_t total = 0;
  for (const StructMember& m : type.struct_members) {
    uint32_t member = MemberBitStreamWidth(m, typedefs, depth + 1);
    if (member == 0) return 0;
    total += member;
  }
  return total;
}

}  // namespace

uint32_t BitStreamTypeWidth(const DataType& type, const TypedefMap& typedefs) {
  return BitStreamTypeWidthAt(type, typedefs, 0);
}

}  // namespace delta
