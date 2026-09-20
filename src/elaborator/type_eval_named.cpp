// Named-type and member-type resolution: FindNamedType, MemberNamedType,
// NestedAggregateSource and ResolveNestedAggregateTypes. Moved out of
// type_eval.cpp verbatim, for room, once that file reached the source-size
// gate.

#include <string>

#include "common/arena.h"
#include "elaborator/type_eval.h"
#include "parser/ast_type.h"

namespace delta {

// The type a named type denotes, or null when no declaration matches it. A
// name behind a scope prefix selects that scope's declaration and never the
// unqualified one: §8.23 (printed page 200) has the class scope resolution
// operator pick out one class's member, its example telling `Base::bin` from
// a `bin` of the enclosing scope, and §26.3 (printed 808) reaches a package's
// declaration the same way, `ComplexPkg::Complex cout`. So a prefixed name
// looks up the "Scope::name" key RegisterPackageTypedefs and
// RegisterClassTypedefs in elaborator_resolve.cpp record, and misses rather
// than falling back to a bare name, which would size the object wrongly.
const DataType* FindNamedType(const DataType& dtype,
                              const TypedefMap& typedefs) {
  if (dtype.kind != DataTypeKind::kNamed) return nullptr;
  if (!dtype.scope_name.empty()) {
    std::string qualified =
        std::string(dtype.scope_name) + "::" + std::string(dtype.type_name);
    auto qit = typedefs.find(qualified);
    return (qit != typedefs.end()) ? &qit->second : nullptr;
  }
  auto it = typedefs.find(dtype.type_name);
  return (it != typedefs.end()) ? &it->second : nullptr;
}

// The same for a structure or union member's named type (§7.2.1): a member
// written behind a qualifier, `q::pair_t Add`, was looked up by `pair_t`
// alone, resolving to whatever a wildcard import made the bare name stand
// for, or to nothing.
const DataType* MemberNamedType(const StructMember& m,
                                const TypedefMap& typedefs) {
  DataType named;
  named.kind = m.type_kind;
  named.type_name = m.type_name;
  named.scope_name = m.scope_name;
  return FindNamedType(named, typedefs);
}

// The struct/union DataType a member's declared type denotes: an inline
// aggregate keeps its parsed type directly; a named member resolves through the
// typedef table, by its qualified name where it was written with one. Returns
// null for scalar members and unresolved names.
static const DataType* NestedAggregateSource(const StructMember& m,
                                             const TypedefMap& typedefs) {
  if (m.nested_type) return m.nested_type;
  const DataType* named = MemberNamedType(m, typedefs);
  bool aggregate = named != nullptr && (named->kind == DataTypeKind::kStruct ||
                                        named->kind == DataTypeKind::kUnion);
  return aggregate ? named : nullptr;
}

void ResolveNestedAggregateTypes(DataType& dt, const TypedefMap& typedefs,
                                 Arena& arena) {
  for (auto& m : dt.struct_members) {
    const DataType* src = NestedAggregateSource(m, typedefs);
    if (!src) continue;
    auto* copy = arena.Create<DataType>(*src);
    ResolveNestedAggregateTypes(*copy, typedefs, arena);
    m.nested_type = copy;
  }
}

}  // namespace delta
