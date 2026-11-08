#include "elaborator/elaborator_enum_constants.h"

#include <cstddef>
#include <cstdint>
#include <format>
#include <string>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "elaborator/const_eval.h"
#include "elaborator/rtlir_enum_member.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {
namespace {

constexpr size_t kScratchBlockSize = 256;

bool LiteralHasXZ(std::string_view txt) {
  auto apos = txt.find('\'');
  if (apos == std::string_view::npos) return false;
  return txt.substr(apos + 1).find_first_of("xXzZ") != std::string_view::npos;
}

struct EnumMemberFolder {
  const ScopeMap& scope;
  Arena& arena;
  int64_t next_val = 0;
  std::vector<RtlirEnumMember> members = {};

  void Emit(std::string_view name) {
    members.push_back({name, next_val});
    ++next_val;
  }

  void EmitIndexed(std::string_view base, int64_t index) {
    auto s = std::format("{}{}", base, index);
    auto* p = arena.AllocString(s.c_str(), s.size());
    Emit(std::string_view{p, s.size()});
  }

  void EmitInclusiveRange(std::string_view name, int64_t n, int64_t m) {
    int step = (m >= n) ? 1 : -1;
    for (auto i = n;; i += step) {
      EmitIndexed(name, i);
      if (i == m) break;
    }
  }

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

void VisitEnumTypes(const DataType& type, const std::string& path,
                    const EnumTypeVisitor& fn) {
  if (type.kind == DataTypeKind::kEnum) fn(path, type);
  for (const auto& sm : type.struct_members) {
    if (sm.nested_type == nullptr) continue;
    std::string member_path =
        path.empty() ? std::string(sm.name) : path + "." + std::string(sm.name);
    VisitEnumTypes(*sm.nested_type, member_path, fn);
  }
}

void AddEnumConstantNames(const DataType& type, const ScopeMap& scope,
                          std::unordered_set<std::string>& names) {
  for (const auto& m : type.enum_members) {
    for (std::string& name : EnumMemberDeclaredNames(m, scope)) {
      names.insert(std::move(name));
    }
  }
}

std::unordered_set<std::string> NamesDeclaredBefore(const PackageDecl* pkg,
                                                    const ModuleItem* until,
                                                    const ScopeMap& scope) {
  std::unordered_set<std::string> names;
  for (const auto* item : pkg->items) {
    if (item == until) break;
    if (item->kind == ModuleItemKind::kParamDecl) names.emplace(item->name);
    ForEachEnumTypeOfItem(item, [&](std::string_view, const DataType& type) {
      AddEnumConstantNames(type, scope, names);
    });
  }
  return names;
}

}  // namespace

bool ExprContainsXZ(const Expr* e) {
  if (!e) return false;
  if ((e->kind == ExprKind::kIntegerLiteral ||
       e->kind == ExprKind::kUnbasedUnsizedLiteral) &&
      LiteralHasXZ(e->text)) {
    return true;
  }
  if (ExprContainsXZ(e->lhs)) return true;
  if (ExprContainsXZ(e->rhs)) return true;
  for (const auto* elem : e->elements) {
    if (ExprContainsXZ(elem)) return true;
  }
  return ExprContainsXZ(e->repeat_count);
}

void ForEachEnumTypeIn(const DataType& type, const EnumTypeVisitor& fn) {
  VisitEnumTypes(type, "", fn);
}

void ForEachEnumTypeOfItem(const ModuleItem* item, const EnumTypeVisitor& fn) {
  ForEachEnumTypeIn(item->kind == ModuleItemKind::kTypedef ? item->typedef_type
                                                           : item->data_type,
                    fn);
}

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
    if (ExprContainsXZ(member.value) && !member.range_start)
      folder.members.back().xz_value = member.value;
  }
  return std::move(folder.members);
}

std::vector<std::string> EnumMemberDeclaredNames(const EnumMember& member,
                                                 const ScopeMap& scope) {
  bool bounds_fold = member.range_start == nullptr ||
                     (ConstEvalInt(member.range_start, scope).has_value() &&
                      (member.range_end == nullptr ||
                       ConstEvalInt(member.range_end, scope).has_value()));
  if (!bounds_fold) return {std::string(member.name)};
  Arena scratch(kScratchBlockSize);
  EnumMemberFolder folder{scope, scratch};
  folder.EmitDeclared(member);
  std::vector<std::string> names;
  names.reserve(folder.members.size());
  for (const auto& m : folder.members) names.emplace_back(m.name);
  return names;
}

std::vector<RtlirEnumMember> BindEnumConstantsOfItem(const ModuleItem* item,
                                                     ScopeMap& scope,
                                                     Arena& arena) {
  std::vector<RtlirEnumMember> bound;
  ForEachEnumTypeOfItem(item, [&](std::string_view, const DataType& type) {
    for (const auto& m : FoldEnumMembers(type.enum_members, scope, arena)) {
      BindDeclaredConstant(scope, m.name, m.value);
      bound.push_back(m);
    }
  });
  return bound;
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
  std::unordered_set<std::string> own = NamesDeclaredBefore(pkg, imp, scope);
  for (const auto& [key, value] : cu_param_scope) {
    if (key.substr(0, prefix.size()) != prefix) continue;
    std::string_view name = key.substr(prefix.size());
    if (name.find('.') != std::string_view::npos ||
        own.count(std::string(name)) != 0)
      continue;
    scope[name] = value;
  }
}

}  // namespace delta
