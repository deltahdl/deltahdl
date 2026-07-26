#include <algorithm>
#include <format>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"

namespace delta {

// §23.9/§24.3: true when a lexically enclosing scope declares `name`.
static bool NameInEnclosingScope(
    const std::vector<std::unordered_set<std::string_view>>& scopes,
    std::string_view name) {
  for (const auto& scope : scopes) {
    if (scope.count(name)) return true;
  }
  return false;
}

bool Elaborator::IsNameInModuleScope(std::string_view name) const {
  if (declared_names_.count(name)) return true;
  if (ansi_port_names_.count(name)) return true;
  if (non_ansi_complete_ports_.count(name)) return true;
  if (non_ansi_partial_ports_.count(name)) return true;
  if (const_names_.count(name)) return true;
  if (enum_member_names_.count(name)) return true;
  if (specparam_names_.count(name)) return true;
  if (class_names_.count(name)) return true;
  if (class_var_names_.count(name)) return true;
  if (task_names_.count(name)) return true;
  if (let_names_.count(name)) return true;
  if (func_decls_.count(name)) return true;
  if (interface_inst_types_.count(name)) return true;
  if (checker_inst_names_.count(name)) return true;
  // §23.9/§24.3: a lexically nested module/program/interface also sees names
  // declared in the scopes that textually enclose it.
  if (NameInEnclosingScope(enclosing_scope_names_, name)) return true;
  return false;
}

std::unordered_set<std::string_view> Elaborator::CaptureCurrentScopeNames()
    const {
  std::unordered_set<std::string_view> scope;
  scope.insert(declared_names_.begin(), declared_names_.end());
  scope.insert(const_names_.begin(), const_names_.end());
  scope.insert(enum_member_names_.begin(), enum_member_names_.end());
  scope.insert(specparam_names_.begin(), specparam_names_.end());
  scope.insert(class_names_.begin(), class_names_.end());
  scope.insert(class_var_names_.begin(), class_var_names_.end());
  scope.insert(task_names_.begin(), task_names_.end());
  scope.insert(let_names_.begin(), let_names_.end());
  scope.insert(ansi_port_names_.begin(), ansi_port_names_.end());
  scope.insert(non_ansi_complete_ports_.begin(),
               non_ansi_complete_ports_.end());
  scope.insert(checker_inst_names_.begin(), checker_inst_names_.end());
  for (const auto& [name, kind] : var_types_) scope.insert(name);
  for (const auto& [name, item] : func_decls_) scope.insert(name);
  for (const auto& [name, width] : non_ansi_partial_ports_) scope.insert(name);
  for (const auto& [name, type] : interface_inst_types_) scope.insert(name);
  for (const auto& [name, type] : typedefs_) scope.insert(name);
  return scope;
}

namespace {

bool ForwardTypedefHasDefinition(const ModuleDecl* decl,
                                 const ModuleItem* item) {
  for (const auto* other : decl->items) {
    if (other == item) continue;
    if (other->kind == ModuleItemKind::kTypedef && other->name == item->name &&
        other->typedef_type.kind != DataTypeKind::kImplicit) {
      return true;
    }
    if (other->kind == ModuleItemKind::kClassDecl && other->class_decl &&
        other->class_decl->name == item->name) {
      return true;
    }
  }
  return false;
}

void ScanForwardScopePrefix(const ModuleDecl* decl, std::string_view scope,
                            bool& is_forward_in_scope,
                            bool& resolves_to_class) {
  for (const auto* other : decl->items) {
    if (other->kind == ModuleItemKind::kTypedef && other->name == scope &&
        other->typedef_type.kind == DataTypeKind::kImplicit) {
      is_forward_in_scope = true;
    }
    if (other->kind == ModuleItemKind::kClassDecl && other->class_decl &&
        other->class_decl->name == scope) {
      resolves_to_class = true;
    }
  }
}

}  // namespace

void Elaborator::ValidateForwardTypedefsInScope(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kTypedef) continue;
    if (item->typedef_type.kind != DataTypeKind::kImplicit) continue;
    bool resolved = ForwardTypedefHasDefinition(decl, item);
    if (!resolved && class_names_.count(item->name) > 0) {
      resolved = true;
    }
    if (!resolved) {
      diag_.Error(item->loc,
                  std::format("forward typedef '{}' is never resolved by a "
                              "definition in the same scope",
                              item->name));
    }
  }
}

void Elaborator::ValidateForwardTypedefScopePrefix(const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    if (item->kind != ModuleItemKind::kTypedef) continue;
    if (item->typedef_type.kind != DataTypeKind::kNamed) continue;
    if (item->typedef_type.scope_name.empty()) continue;
    auto scope = item->typedef_type.scope_name;
    bool is_forward_in_scope = false;
    bool resolves_to_class = class_names_.count(scope) > 0;
    ScanForwardScopePrefix(decl, scope, is_forward_in_scope, resolves_to_class);
    if (!is_forward_in_scope) continue;
    if (!resolves_to_class) {
      diag_.Error(item->loc,
                  std::format("scope-resolution prefix '{}' of a typedef does "
                              "not resolve to a class",
                              scope));
    }
  }
}

}  // namespace delta
