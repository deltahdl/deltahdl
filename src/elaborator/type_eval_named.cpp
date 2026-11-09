#include <algorithm>
#include <cstddef>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "elaborator/std_package.h"
#include "elaborator/type_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

std::vector<std::string_view> OuterScopePrefixes(const DataType& dt) {
  std::vector<std::string_view> prefixes = dt.outer_scope_names;
  if (!prefixes.empty() && prefixes.front() == "$unit")
    prefixes.erase(prefixes.begin());
  return prefixes;
}

std::string TypeChainKey(const DataType& type) {
  if (type.scope_name.empty()) return std::string(type.type_name);
  std::string key;
  for (std::string_view prefix : OuterScopePrefixes(type))
    key += std::string(prefix) + "::";
  return key + std::string(type.scope_name) +
         "::" + std::string(type.type_name);
}

std::optional<DataType> ThroughBoundPrefix(const DataType& dtype,
                                           const TypedefMap& typedefs) {
  if (dtype.scope_name.empty() || !dtype.outer_scope_names.empty())
    return std::nullopt;
  auto bound = typedefs.find(dtype.scope_name);
  if (bound == typedefs.end()) return std::nullopt;
  const DataType& cls = bound->second;
  if (cls.kind != DataTypeKind::kNamed || !cls.scope_name.empty() ||
      !cls.type_params.empty() || cls.type_name == dtype.scope_name)
    return std::nullopt;
  DataType through = dtype;
  through.scope_name = cls.type_name;
  return through;
}

const DataType* FindNamedType(const DataType& dtype,
                              const TypedefMap& typedefs) {
  if (dtype.kind != DataTypeKind::kNamed) return nullptr;
  if (!dtype.scope_name.empty()) {
    auto qit = typedefs.find(TypeChainKey(dtype));
    if (qit != typedefs.end()) return &qit->second;
    if (std::optional<DataType> through = ThroughBoundPrefix(dtype, typedefs))
      return FindNamedType(*through, typedefs);
    return StdClassEnumType(dtype);
  }
  auto it = typedefs.find(dtype.type_name);
  return (it != typedefs.end()) ? &it->second : nullptr;
}

static bool IsBareTypeName(const DataType& type) {
  return type.kind == DataTypeKind::kNamed && type.scope_name.empty();
}

DataType InPackageScope(const DataType& type, const PackageDecl& package) {
  DataType scoped = type;
  if (!IsBareTypeName(type)) return scoped;
  for (const ModuleItem* item : package.items) {
    if (item->kind == ModuleItemKind::kTypedef &&
        item->name == type.type_name) {
      scoped.scope_name = package.name;
    }
  }
  return scoped;
}

DataType InClassScope(const DataType& type, const ClassDecl& cls,
                      std::string_view scope) {
  DataType scoped = type;
  if (!IsBareTypeName(type)) return scoped;
  for (const ClassMember* m : cls.members) {
    if (m->kind == ClassMemberKind::kTypedef && m->name == type.type_name) {
      scoped.scope_name = scope;
    }
  }
  return scoped;
}

DataType InClassScope(const DataType& type, const ClassDecl& cls) {
  return InClassScope(type, cls, cls.name);
}

static void ScopeTypedefName(std::string_view type_name,
                             std::string_view& scope_name,
                             const TypedefScopes& scopes) {
  auto declarer = scopes.find(type_name);
  if (scope_name.empty() && declarer != scopes.end())
    scope_name = declarer->second;
}

static void ScopeTypedefMembers(DataType& type, const TypedefScopes& scopes,
                                Arena& arena) {
  for (StructMember& m : type.struct_members) {
    if (m.nested_type != nullptr) {
      auto* nested = arena.Create<DataType>(*m.nested_type);
      ScopeTypedefMembers(*nested, scopes, arena);
      m.nested_type = nested;
      continue;
    }
    ScopeTypedefName(m.type_name, m.scope_name, scopes);
  }
}

DataType InTypedefScopes(const DataType& type, const TypedefScopes& scopes,
                         Arena& arena) {
  DataType scoped = type;
  ScopeTypedefName(scoped.type_name, scoped.scope_name, scopes);
  ScopeTypedefMembers(scoped, scopes, arena);
  return scoped;
}

void EnterTypedefScope(TypedefScopes& scopes, const ModuleItem& td,
                       std::string_view scope) {
  if (td.typedef_type.kind != DataTypeKind::kImplicit) scopes[td.name] = scope;
}

DataType PackageTypedefType(const ModuleItem& item, const PackageDecl& pkg,
                            Arena& arena) {
  TypedefScopes declared;
  const auto kAt = std::find(pkg.items.begin(), pkg.items.end(), &item);
  for (auto earlier = pkg.items.begin(); earlier != kAt; ++earlier) {
    if ((*earlier)->kind == ModuleItemKind::kTypedef)
      EnterTypedefScope(declared, **earlier, pkg.name);
  }
  return InTypedefScopes(InPackageScope(item.typedef_type, pkg), declared,
                         arena);
}

const DataType& LastTypeInChain(const DataType& dtype,
                                const TypedefMap& typedefs) {
  const DataType* type = &dtype;
  for (std::size_t steps = 0; steps <= typedefs.size(); ++steps) {
    const DataType* named = FindNamedType(*type, typedefs);
    if (named == nullptr) break;
    type = named;
  }
  return *type;
}

DataTypeKind ResolvedTypeKind(const DataType& dtype,
                              const TypedefMap& typedefs) {
  return LastTypeInChain(dtype, typedefs).kind;
}

const DataType* TypeAtChainEnd(const DataType& dtype,
                               const TypedefMap& typedefs) {
  if (ResolvedTypeKind(dtype, typedefs) == DataTypeKind::kNamed) return nullptr;
  const DataType* type = &dtype;
  while (type->kind == DataTypeKind::kNamed)
    type = FindNamedType(*type, typedefs);
  return type;
}

const DataType* MemberNamedType(const StructMember& m,
                                const TypedefMap& typedefs) {
  DataType named;
  named.kind = m.type_kind;
  named.type_name = m.type_name;
  named.scope_name = m.scope_name;
  return FindNamedType(named, typedefs);
}

static const DataType* NestedAggregateSource(const StructMember& m,
                                             const TypedefMap& typedefs) {
  if (m.nested_type) return m.nested_type;
  const DataType* named = MemberNamedType(m, typedefs);
  bool aggregate = named != nullptr && (named->kind == DataTypeKind::kStruct ||
                                        named->kind == DataTypeKind::kUnion);
  return aggregate ? named : nullptr;
}

void SizeClassHandleMembers(
    DataType& dt, const TypedefMap& typedefs,
    const std::unordered_set<std::string_view>& class_names) {
  for (StructMember& m : dt.struct_members) {
    DataType written;
    written.kind = m.type_kind;
    written.type_name = m.type_name;
    written.scope_name = m.scope_name;
    const DataType& end = LastTypeInChain(written, typedefs);
    if (!class_names.contains(end.type_name)) continue;
    m.type_name = end.type_name;
    m.scope_name = end.scope_name;
    m.resolved_width = kClassMemberHandleWidth;
  }
}

void ResolveNestedAggregateTypes(DataType& dt, const TypedefMap& typedefs,
                                 Arena& arena) {
  for (auto& m : dt.struct_members) {
    const DataType* src = NestedAggregateSource(m, typedefs);
    if (!src || (m.nested_type == nullptr && m.packed_dim_left != nullptr)) {
      if (MemberNamedType(m, typedefs) != nullptr)
        m.resolved_width = EvalStructMemberWidth(m, typedefs);
      continue;
    }
    auto* copy = arena.Create<DataType>(*src);
    ResolveNestedAggregateTypes(*copy, typedefs, arena);
    m.nested_type = copy;
  }
}

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
