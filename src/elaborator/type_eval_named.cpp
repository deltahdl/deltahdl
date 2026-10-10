// Named-type and member-type resolution: FindNamedType, MemberNamedType,
// NestedAggregateSource and ResolveNestedAggregateTypes, moved out of
// type_eval.cpp verbatim, for room, once that file reached the source-size
// gate; ResolvedTypeKind, which follows a chain of names to its type; and
// RecordTypedef, which enters a typedef into the table.

#include <cstddef>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "elaborator/std_package.h"
#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
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
    // §9.7 with §G.6: process::state is declared by the built-in process
    // class, which no declaration of the design holds.
    return (qit != typedefs.end()) ? &qit->second : StdClassEnumType(dtype);
  }
  auto it = typedefs.find(dtype.type_name);
  return (it != typedefs.end()) ? &it->second : nullptr;
}

DataType InPackageScope(const DataType& type, const PackageDecl& package) {
  DataType scoped = type;
  if (type.kind != DataTypeKind::kNamed || !type.scope_name.empty()) {
    return scoped;
  }
  for (const ModuleItem* item : package.items) {
    if (item->kind == ModuleItemKind::kTypedef &&
        item->name == type.type_name) {
      scoped.scope_name = package.name;
    }
  }
  return scoped;
}

DataTypeKind ResolvedTypeKind(const DataType& dtype,
                              const TypedefMap& typedefs) {
  // Each step follows one name, and a chain longer than the table has names
  // runs through one of them twice, so the walk is bounded by the table.
  const DataType* type = &dtype;
  for (std::size_t steps = 0; steps <= typedefs.size(); ++steps) {
    const DataType* named = FindNamedType(*type, typedefs);
    if (named == nullptr) break;
    type = named;
  }
  return type->kind;
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
    if (!src) {
      // A named member that is no aggregate keeps no nested type, and the
      // run-time layout sizes it by this width rather than by its kind alone.
      if (const DataType* named = MemberNamedType(m, typedefs))
        m.resolved_width = EvalTypeWidth(*named, typedefs);
      continue;
    }
    auto* copy = arena.Create<DataType>(*src);
    ResolveNestedAggregateTypes(*copy, typedefs, arena);
    m.nested_type = copy;
  }
}

// §6.18 has a typedef name a type declared before it, and §23.9 looks a name a
// module does not yet declare up in the compilation unit's scope. So in a
// module, `typedef HU HU;` names the compilation unit's HU and declares the
// module's HU as the type that HU stood for. Recorded as written, the entry
// would name itself, and following it would never end; the table already
// holds what the name stood for, a typedef's type or, for a class, no entry at
// all. Packed dimensions the typedef writes after the name are packed outside
// that type's own (§7.4.1), so `typedef w_t [1:0] w_t;` under a compilation
// unit `typedef logic [3:0] w_t;` is `logic [1:0][3:0]`.
void RecordTypedef(TypedefMap& typedefs, std::string_view name,
                   const DataType& type) {
  if (type.kind != DataTypeKind::kNamed || !type.scope_name.empty() ||
      type.type_name != name) {
    typedefs[name] = type;
    return;
  }
  auto outer = typedefs.find(name);
  if (outer == typedefs.end() || type.packed_dim_left == nullptr) return;
  DataType& stood_for = outer->second;
  std::vector<std::pair<Expr*, Expr*>> dims{
      {type.packed_dim_left, type.packed_dim_right}};
  dims.insert(dims.end(), type.extra_packed_dims.begin(),
              type.extra_packed_dims.end());
  if (stood_for.packed_dim_left != nullptr)
    dims.emplace_back(stood_for.packed_dim_left, stood_for.packed_dim_right);
  dims.insert(dims.end(), stood_for.extra_packed_dims.begin(),
              stood_for.extra_packed_dims.end());
  stood_for.packed_dim_left = dims.front().first;
  stood_for.packed_dim_right = dims.front().second;
  stood_for.extra_packed_dims.assign(dims.begin() + 1, dims.end());
}

}  // namespace delta
