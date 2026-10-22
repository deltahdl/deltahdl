#include <cstddef>
#include <cstdint>
#include <optional>

#include "common/arena.h"
#include "elaborator/const_eval.h"
#include "elaborator/queue_dim.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

namespace delta {

const DataType* ResolvedAggregateType(const DataType& dtype,
                                      const TypedefMap& typedefs,
                                      Arena& arena) {
  const DataType* d = &dtype;
  // §6.18 lets a typedef name stand for another typedef name; the chain is
  // bounded so a name defined in terms of itself resolves to nothing rather
  // than looping.
  for (int hops = 0; d->kind == DataTypeKind::kNamed && hops < 16; ++hops) {
    d = FindNamedType(*d, typedefs);
    if (d == nullptr) return nullptr;
  }
  if (d->kind != DataTypeKind::kStruct && d->kind != DataTypeKind::kUnion) {
    return nullptr;
  }
  if (d->struct_members.empty()) return nullptr;
  auto* copy = arena.Create<DataType>(*d);
  ResolveNestedAggregateTypes(*copy, typedefs, arena);
  return copy;
}

const DataType* NamedPackedVectorType(const DataType& dtype,
                                      const TypedefMap& typedefs,
                                      Arena& arena) {
  const DataType* d = &dtype;
  for (std::size_t steps = 0;
       d->kind == DataTypeKind::kNamed && steps <= typedefs.size(); ++steps) {
    d = FindNamedType(*d, typedefs);
    if (d == nullptr) return nullptr;
  }
  if (d->kind == DataTypeKind::kNamed || d->kind == DataTypeKind::kEnum ||
      d->packed_dim_left == nullptr) {
    return nullptr;
  }
  return arena.Create<DataType>(*d);
}

namespace {

// `bound` folded against `scope`, as a literal of the integer it is; `bound`
// itself where it is a literal already or does not fold.
Expr* FoldedBound(Expr* bound, const ScopeMap& scope, Arena& arena) {
  if (bound == nullptr || bound->kind == ExprKind::kIntegerLiteral)
    return bound;
  std::optional<int64_t> value = ConstEvalInt(bound, scope);
  if (!value) return bound;
  auto* literal = arena.Create<Expr>();
  literal->kind = ExprKind::kIntegerLiteral;
  literal->int_val = static_cast<uint64_t>(*value);
  literal->range = bound->range;
  return literal;
}

// An unpacked dimension folded: `[size]` whole, `[left:right]` and a queue's
// `[$:bound]` by their bounds. A dynamic dimension, null, has none.
Expr* FoldedUnpackedDim(Expr* dim, const ScopeMap& scope, Arena& arena) {
  if (dim == nullptr) return nullptr;
  bool is_range =
      dim->kind == ExprKind::kBinary && dim->op == TokenKind::kColon;
  if (!is_range && !IsQueueDim(dim)) return FoldedBound(dim, scope, arena);
  auto* folded = arena.Create<Expr>(*dim);
  if (is_range) folded->lhs = FoldedBound(dim->lhs, scope, arena);
  folded->rhs = FoldedBound(dim->rhs, scope, arena);
  return folded;
}

void FoldPackedBounds(Expr*& left, Expr*& right, const ScopeMap& scope,
                      Arena& arena) {
  left = FoldedBound(left, scope, arena);
  right = FoldedBound(right, scope, arena);
}

}  // namespace

void FoldMemberDims(DataType& type, const ScopeMap& scope, Arena& arena) {
  for (StructMember& m : type.struct_members) {
    FoldPackedBounds(m.packed_dim_left, m.packed_dim_right, scope, arena);
    for (auto& [left, right] : m.extra_packed_dims)
      FoldPackedBounds(left, right, scope, arena);
    for (Expr*& dim : m.unpacked_dims)
      dim = FoldedUnpackedDim(dim, scope, arena);
    if (m.nested_type == nullptr) continue;
    auto* nested = arena.Create<DataType>(*m.nested_type);
    FoldPackedBounds(nested->packed_dim_left, nested->packed_dim_right, scope,
                     arena);
    for (auto& [left, right] : nested->extra_packed_dims)
      FoldPackedBounds(left, right, scope, arena);
    FoldMemberDims(*nested, scope, arena);
    m.nested_type = nested;
  }
}

}  // namespace delta
