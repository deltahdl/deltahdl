// §6.19: what each named constant of an enumeration is worth. The folding is
// written once here and read by every scope that declares constants -- a
// module's enumerations in elaborator_typedef.cpp, which also emits the backing
// variables, and the package and compilation-unit scopes, which hold constants
// in a ScopeMap and nothing else. The constants a package's import brings in
// (§26.3) are bound into such a map here as well, for the two walks over a
// package's declarations that fold and check its parameters.

#include "elaborator/elaborator_enum_constants.h"

#include <cstdint>
#include <format>
#include <string>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "elaborator/const_eval.h"
#include "elaborator/rtlir.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {
namespace {

// The running value §6.19 assigns: a member's explicit value replaces it, and
// each member emitted advances it by one for the member after.
struct EnumMemberFolder {
  const ScopeMap& scope;
  Arena& arena;
  int64_t next_val = 0;
  std::vector<RtlirEnumMember> members = {};

  // Records one member under the current value and advances it.
  void Emit(std::string_view name) {
    members.push_back({name, next_val});
    ++next_val;
  }

  // Builds an arena-owned "<base><index>" name and emits it as a member.
  void EmitIndexed(std::string_view base, int64_t index) {
    auto s = std::format("{}{}", base, index);
    auto* p = arena.AllocString(s.c_str(), s.size());
    Emit(std::string_view{p, s.size()});
  }

  // Expands a `name[range_start:range_end]` member into one indexed member per
  // step from range_start toward range_end (inclusive).
  void EmitInclusiveRange(std::string_view name, int64_t n, int64_t m) {
    int step = (m >= n) ? 1 : -1;
    for (auto i = n;; i += step) {
      EmitIndexed(name, i);
      if (i == m) break;
    }
  }

  // Emits one declared member, expanding any `[range]` suffix.
  void EmitDeclared(const EnumMember& member) {
    if (!member.range_start) {
      Emit(member.name);
      return;
    }
    auto n = ConstEvalInt(member.range_start, scope).value_or(0);
    if (member.range_end) {
      EmitInclusiveRange(member.name, n,
                         ConstEvalInt(member.range_end, scope).value_or(0));
    } else {
      for (int64_t i = 0; i < n; ++i) EmitIndexed(member.name, i);
    }
  }
};

// The members of the enumeration `item` declares, or null when it declares
// none. Syntax 6-5 makes the enum form a data_type, so it stands either as the
// type a typedef names or as the type of a data declaration.
const std::vector<EnumMember>* EnumMembersDeclaredBy(const ModuleItem* item) {
  if (item->kind == ModuleItemKind::kTypedef &&
      item->typedef_type.kind == DataTypeKind::kEnum)
    return &item->typedef_type.enum_members;
  if (item->data_type.kind == DataTypeKind::kEnum)
    return &item->data_type.enum_members;
  return nullptr;
}

// The names `pkg` declares ahead of `until`: its parameters and the members
// of its enumerations, as written. A `name[N]` member of §6.19.2 is held
// under the name it is written with, not under the indexed names it expands
// to.
std::unordered_set<std::string_view> NamesDeclaredBefore(
    const PackageDecl* pkg, const ModuleItem* until) {
  std::unordered_set<std::string_view> names;
  for (const auto* item : pkg->items) {
    if (item == until) break;
    if (item->kind == ModuleItemKind::kParamDecl) names.insert(item->name);
    const auto* members = EnumMembersDeclaredBy(item);
    if (members == nullptr) continue;
    for (const auto& m : *members) names.insert(m.name);
  }
  return names;
}

}  // namespace

std::vector<RtlirEnumMember> FoldEnumMembers(
    const std::vector<EnumMember>& decl_members, const ScopeMap& scope,
    Arena& arena) {
  EnumMemberFolder folder{scope, arena};
  for (const auto& member : decl_members) {
    if (member.value) {
      folder.next_val =
          ConstEvalInt(member.value, scope).value_or(folder.next_val);
    }
    folder.EmitDeclared(member);
  }
  return std::move(folder.members);
}

std::vector<RtlirEnumMember> BindEnumConstantsOfItem(const ModuleItem* item,
                                                     ScopeMap& scope,
                                                     Arena& arena) {
  const auto* members = EnumMembersDeclaredBy(item);
  if (members == nullptr) return {};
  auto folded = FoldEnumMembers(*members, scope, arena);
  for (const auto& m : folded) scope[m.name] = m.value;
  return folded;
}

void BindPackageImportConstants(const PackageDecl* pkg, const ModuleItem* imp,
                                const ScopeMap& cu_param_scope,
                                ScopeMap& scope) {
  if (imp->kind != ModuleItemKind::kImportDecl) return;
  const ImportItem& item = imp->import_item;
  std::string prefix = std::string(item.package_name) + ".";
  if (!item.is_wildcard) {
    auto it = cu_param_scope.find(prefix + std::string(item.item_name));
    if (it != cu_param_scope.end()) scope[item.item_name] = it->second;
    return;
  }
  // The bare name is the tail of the recorded key, whose characters outlive
  // every scope map (RecordPackageConstant allocates the key in the arena).
  std::unordered_set<std::string_view> own = NamesDeclaredBefore(pkg, imp);
  for (const auto& [key, value] : cu_param_scope) {
    if (key.substr(0, prefix.size()) != prefix) continue;
    std::string_view name = key.substr(prefix.size());
    if (name.find('.') != std::string_view::npos || own.count(name) != 0)
      continue;
    scope[name] = value;
  }
}

}  // namespace delta
