#include <format>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_data.h"
#include "elaborator/elaborator_enum_constants.h"
#include "elaborator/elaborator_validate_classes.h"
#include "elaborator/type_eval.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

static bool NameInEnclosingScope(
    const std::vector<std::unordered_set<std::string_view>>& scopes,
    std::string_view name) {
  for (const auto& scope : scopes) {
    if (scope.count(name)) return true;
  }
  return false;
}

bool Elaborator::IsNameInModuleScope(std::string_view name) const {
  if (let_names_.count(name)) return true;
  if (declared_names_.count(name)) return true;
  if (ansi_port_names_.count(name)) return true;
  if (non_ansi_complete_ports_.count(name)) return true;
  if (non_ansi_partial_ports_.count(name)) return true;
  if (const_names_.count(name)) return true;
  if (enum_member_names_.count(name)) return true;
  if (specparam_names_.count(name)) return true;
  if (class_names_.count(name)) return true;
  if (class_var_names_.count(name)) return true;
  if (func_decls_.count(name)) return true;
  if (interface_inst_types_.count(name)) return true;
  if (checker_inst_names_.count(name)) return true;
  if (NameInEnclosingScope(enclosing_scope_names_, name)) return true;
  return false;
}

bool Elaborator::IsNameInEnclosingScope(std::string_view name) const {
  return NameInEnclosingScope(enclosing_scope_names_, name);
}

std::unordered_map<std::string_view, ModuleDecl*>
ElaboratorData::NestedDeclsSeenInside() const {
  std::unordered_map<std::string_view, ModuleDecl*> seen =
      enclosing_nested_decls_;
  for (const auto& [name, decl] : nested_module_decls_) seen[name] = decl;
  return seen;
}

void ElaboratorData::TakeNestedDeclInheritance() {
  inherited_default_disable_iff_ =
      std::exchange(nested_default_disable_iff_, nullptr);
  inherited_default_clock_ = std::exchange(nested_default_clock_, {});
  enclosing_nested_decls_ = std::exchange(pending_enclosing_nested_decls_, {});
}

void ElaboratorData::BeginNestedDeclScope(
    const ModuleDecl* nested,
    std::unordered_set<std::string_view> at_instance) {
  auto at_decl = nested_decl_scope_names_.find(nested);
  if (at_decl != nested_decl_scope_names_.end()) {
    pending_enclosing_scope_ = at_decl->second;
    has_pending_enclosing_scope_ = true;
    return;
  }
  auto above = nested_decl_names_above_.find(nested);
  if (above != nested_decl_names_above_.end()) {
    for (const std::string& name : above->second) at_instance.emplace(name);
  }
  pending_enclosing_scope_ = std::move(at_instance);
  has_pending_enclosing_scope_ = true;
}

static void AddEnumMemberNames(const EnumMember& member,
                               std::unordered_set<std::string>& names) {
  const ScopeMap kNoScope;
  for (std::string& name : EnumMemberDeclaredNames(member, kNoScope)) {
    names.insert(std::move(name));
  }
}

static void AddItemDeclaredNames(const ModuleItem* item,
                                 std::unordered_set<std::string>& names) {
  if (!item->name.empty()) names.emplace(item->name);
  if (!item->inst_name.empty()) names.emplace(item->inst_name);
  if (!item->gate_inst_name.empty()) names.emplace(item->gate_inst_name);
  if (item->first_in_decl_list) {
    ForEachEnumTypeOfItem(item, [&](std::string_view, const DataType& type) {
      for (const auto& member : type.enum_members) {
        AddEnumMemberNames(member, names);
      }
    });
  }
  if (item->kind == ModuleItemKind::kContAssign &&
      item->assign_lhs != nullptr &&
      item->assign_lhs->kind == ExprKind::kIdentifier) {
    names.emplace(item->assign_lhs->text);
  }
}

void ElaboratorData::RecordNestedDeclNamesAbove(
    const std::vector<ModuleItem*>& items) {
  std::unordered_set<std::string> above;
  for (const auto* item : items) {
    if (item->kind == ModuleItemKind::kNestedModuleDecl &&
        item->nested_module_decl != nullptr) {
      nested_decl_names_above_.try_emplace(item->nested_module_decl, above);
    }
    AddItemDeclaredNames(item, above);
  }
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
  for (const auto& [name, signals] : clocking_signals_) scope.insert(name);
  return scope;
}

namespace {

bool ForwardTypedefHasDefinition(const std::vector<ModuleItem*>& items,
                                 const ModuleItem* item) {
  for (const auto* other : items) {
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

struct ScopePrefixedType {
  const DataType* type = nullptr;
  std::string_view construct;
};

ScopePrefixedType ScopePrefixedTypeOfItem(const ModuleItem* item) {
  switch (item->kind) {
    case ModuleItemKind::kTypedef:
      return {&item->typedef_type, "a typedef"};
    case ModuleItemKind::kParamDecl:
      if (item->data_type.kind != DataTypeKind::kVoid) return {};
      return {&item->typedef_type, "a type parameter assignment"};
    case ModuleItemKind::kVarDecl:
      return {&item->data_type, "a data declaration"};
    default:
      return {};
  }
}

}  // namespace

void ElaboratorClassRules::ValidateForwardTypedefsInScope(
    const std::vector<ModuleItem*>& items) {
  for (const auto* item : items) {
    ValidateForwardTypedefsInScope(item->gen_body);
    if (item->gen_else != nullptr) {
      ValidateForwardTypedefsInScope({item->gen_else});
    }
    for (const auto& arm : item->gen_case_items) {
      ValidateForwardTypedefsInScope(arm.body);
    }
    if (item->kind != ModuleItemKind::kTypedef) continue;
    if (item->typedef_type.kind != DataTypeKind::kImplicit) continue;
    bool resolved = ForwardTypedefHasDefinition(items, item);
    if (!resolved && class_names_.count(item->name) > 0) {
      resolved = true;
    }
    if (!resolved) {
      diag_.Error(item->loc,
                  std::format("forward typedef '{}' is never resolved by a "
                              "definition in the same scope",
                              item->name),
                  Subclause("6.18"));
    }
  }
}

void ElaboratorClassRules::ValidateForwardTypedefScopePrefix(
    const ModuleDecl* decl) {
  for (const auto* item : decl->items) {
    auto declared = ScopePrefixedTypeOfItem(item);
    if (declared.type == nullptr) continue;
    if (declared.type->kind != DataTypeKind::kNamed) continue;
    if (declared.type->scope_name.empty()) continue;
    auto scope = declared.type->scope_name;
    bool is_forward_in_scope = false;
    bool resolves_to_class = class_names_.count(scope) > 0;
    ScanForwardScopePrefix(decl, scope, is_forward_in_scope, resolves_to_class);
    if (!is_forward_in_scope) continue;
    if (!resolves_to_class) {
      diag_.Error(item->loc,
                  std::format("scope-resolution prefix '{}' of {} does not "
                              "resolve to a class",
                              scope, declared.construct),
                  Subclause("6.18"));
    }
  }
}

}  // namespace delta
