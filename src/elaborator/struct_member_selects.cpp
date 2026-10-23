#include "elaborator/struct_member_selects.h"

#include <algorithm>
#include <cstddef>
#include <format>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/type_site_lookup.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

SitedType ThroughTypedefsAt(const CompilationUnit& unit, SitedType named) {
  for (FoundItem def = TypedefOf(unit, named.site, *named.type);
       def.item != nullptr; def = TypedefOf(unit, named.site, *named.type)) {
    named = {&def.item->typedef_type, def.site,
             named.dims + def.item->unpacked_dims.size()};
  }
  return named;
}

namespace {

// The type a part of a dotted name reaches, and how a report names it: by the
// typedef name it was written with, or else by the name of the variable or
// the member declared with it.
struct ReachedType {
  SitedType sited;
  std::string_view type_name;
  std::string_view declared;
};

// §7.2: whether `reached` is a structure or a union itself, no element of an
// array of them left to select.
bool IsAggregate(const ReachedType& reached) {
  const DataType* type = reached.sited.type;
  return type != nullptr && reached.sited.dims == 0 &&
         (type->kind == DataTypeKind::kStruct ||
          type->kind == DataTypeKind::kUnion);
}

// The member named `name` the structure or union `holder` declares; null where
// `holder` is none, or declares no member of that name.
const StructMember* MemberOf(const ReachedType& holder, std::string_view name) {
  if (!IsAggregate(holder)) return nullptr;
  const std::vector<StructMember>& members = holder.sited.type->struct_members;
  const auto kFound = std::ranges::find(members, name, &StructMember::name);
  return kFound == members.end() ? nullptr : &*kFound;
}

// The type the member `member` of a structure or union written at `site` is
// declared with: the inline structure, union or enumeration it writes, or the
// type its typedef name stands for; no type for a member of a built-in type
// or of a class (§8).
SitedType MemberType(const CompilationUnit& unit, const TypeSite& site,
                     const StructMember& member) {
  const std::size_t kDims = member.unpacked_dims.size();
  if (member.nested_type != nullptr) return {member.nested_type, site, kDims};
  DataType written;
  written.type_name = member.type_name;
  written.scope_name = member.scope_name;
  const FoundItem kDef = TypedefOf(unit, site, written);
  if (kDef.item == nullptr) return {};
  return ThroughTypedefsAt(unit, {&kDef.item->typedef_type, kDef.site,
                                  kDims + kDef.item->unpacked_dims.size()});
}

// The type `written`, which the variable or property named `declared` is
// declared with, reaches through its typedefs; none where it is no type.
ReachedType NamedReached(const SitedType& written, const CompilationUnit& unit,
                         std::string_view declared) {
  if (written.type == nullptr) return {};
  const std::string_view kTypeName = written.type->kind == DataTypeKind::kNamed
                                         ? written.type->type_name
                                         : std::string_view();
  return {ThroughTypedefsAt(unit, written), kTypeName, declared};
}

// The type the part `e` of a dotted name reaches: the variable its first name
// names, one element per select of an unpacked dimension, the member each
// member select names of the structure or union reached before it, and the
// property one names of the class a handle reached before it holds (§8.5).
ReachedType Reached(const Expr& e, const CompilationUnit& unit,
                    const RootTypeOf& root_type) {
  if (e.kind == ExprKind::kIdentifier) {
    return NamedReached(root_type(e), unit, e.text);
  }
  if (e.kind == ExprKind::kSelect) {
    ReachedType element = Reached(*e.base, unit, root_type);
    if (element.sited.dims == 0) return {};
    --element.sited.dims;
    return element;
  }
  if (e.kind != ExprKind::kMemberAccess || e.is_scope_resolution) return {};
  const ReachedType kHolder = Reached(*e.lhs, unit, root_type);
  const StructMember* member = MemberOf(kHolder, e.rhs->text);
  if (member == nullptr) return NamedReached(root_type(e), unit, e.rhs->text);
  return {MemberType(unit, kHolder.sited.site, *member), member->type_name,
          member->name};
}

}  // namespace

void ReportUndeclaredAggregateMember(const Expr& access,
                                     const CompilationUnit& unit,
                                     const RootTypeOf& root_type,
                                     DiagEngine& diag) {
  if (access.rhs->text == "rand_mode") return;
  const ReachedType kHolder = Reached(*access.lhs, unit, root_type);
  if (!IsAggregate(kHolder) || MemberOf(kHolder, access.rhs->text) != nullptr) {
    return;
  }
  const char* noun =
      kHolder.sited.type->kind == DataTypeKind::kUnion ? "union" : "structure";
  const std::string kAggregate =
      kHolder.type_name.empty()
          ? std::format("the {} of '{}'", noun, kHolder.declared)
          : std::format("{} '{}'", noun, kHolder.type_name);
  diag.Error(
      access.rhs->range.start,
      std::format("{} has no member named '{}'", kAggregate, access.rhs->text),
      Subclause("23.7"));
}

}  // namespace delta
