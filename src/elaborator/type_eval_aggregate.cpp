#include "common/arena.h"
#include "elaborator/type_eval.h"
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

}  // namespace delta
