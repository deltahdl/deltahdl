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

// §23.4: the enclosing chain alone, which is what an implicit net of a nested
// module asks -- whether the name it stands for is an outer module's, the
// module's own declarations having already been searched and found wanting.
bool Elaborator::IsNameInEnclosingScope(std::string_view name) const {
  return NameInEnclosingScope(enclosing_scope_names_, name);
}

// §23.4 makes the enclosing module's names visible inside a module declared
// and instantiated in it, and §6.10 makes an identifier on the left of a
// continuous assignment an implicit net of the assignment's own scope unless
// it was declared previously in that scope or in one the scope can directly
// reference. The reference stands in the nested declaration's text, so the
// names that count are those the enclosing module declared above that text:
// `module M; assign w = 1'b1; endmodule wire w; M m();` gives M an implicit w
// of its own and leaves the outer w undriven, exactly as `assign w = 1'b1;
// wire w;` in one scope makes the second a redeclaration. The snapshot
// ElaborateItems recorded when its loop reached the declaration is therefore
// the one handed on, whether the instance is written below the declaration or
// implied at the end of the items by InstantiateImplicitNestedModules. An
// instance written above its declaration is reached before any snapshot is
// taken; the names declared so far stand in for it, joined with the names the
// text declares above the declaration, which RecordNestedDeclNamesAbove read
// before any item was elaborated: `M m(); wire w; module M; assign w = 1'b1;
// endmodule` has w declared previously to M's assignment, though not to the
// instance, so M's assignment drives the outer w.
void ElaboratorData::BeginNestedDeclScope(
    const ModuleDecl* nested,
    std::unordered_set<std::string_view> at_instance) {
  auto at_decl = nested_decl_scope_names_.find(nested);
  if (at_decl != nested_decl_scope_names_.end()) {
    pending_enclosing_scope_ = at_decl->second;
    has_pending_enclosing_scope_ = true;
    return;
  }
  // The recorded names are owned strings (a ranged enumeration member's
  // constants are spelled by no text); nested_decl_names_above_ keeps them for
  // as long as the elaborator lives, so views into them are handed on.
  auto above = nested_decl_names_above_.find(nested);
  if (above != nested_decl_names_above_.end()) {
    for (const std::string& name : above->second) at_instance.emplace(name);
  }
  pending_enclosing_scope_ = std::move(at_instance);
  has_pending_enclosing_scope_ = true;
}

// §6.19 declares an enumeration's literals as named constants of the scope
// holding the enumeration, and §7.2 with §23.9 has one written as the type of
// a structure or union member declare them in the same scope, the structure
// being no scope of its own. The names one such member declares: its written
// name, or for a `name[N]` or `name[N:M]` member the constants Table 6-10 of
// §6.19.2 (printed page 121) generates from it, name0 through nameN-1 or
// nameN through nameM, which EnumMemberDeclaredNames spells out; the member's
// written name itself declares nothing then. The generated names are owned by
// no text, so `names` owns its strings. The bounds are folded against no
// scope, this walk running on the syntax tree before any item is elaborated;
// a bound naming a parameter does not fold, and the written name is then kept
// in place of the constants. Before, a ranged member was left out altogether,
// and `M m(); enum {C[2] = 5} e; wire [7:0] v; module M; assign v = C1;`
// reported C1 undeclared in M.
static void AddEnumMemberNames(const EnumMember& member,
                               std::unordered_set<std::string>& names) {
  const ScopeMap kNoScope;
  for (std::string& name : EnumMemberDeclaredNames(member, kNoScope)) {
    names.insert(std::move(name));
  }
}

// The names `item` declares as the text alone shows them: the declared name
// of a net, variable, parameter, typedef, class, subroutine, let, property,
// sequence, covergroup, clocking block or nettype, the label of a generate
// block or an assertion, an instance's name and a gate instance's name; the
// constants of each enumeration the item writes inline, which A.2.1.3 has
// the first declarator of a declaration list introduce once; and the
// identifier on the left of a continuous assignment, which §6.10 declares as
// an implicit net of the scope where it was not declared before and which is
// already among the names where it was.
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

// §6.10 counts a name as declared previously by the text above the nested
// declaration, and an instance written above that declaration is elaborated
// before the item loop reaches it, so the names the items above each nested
// declaration declare are read from the text first, for BeginNestedDeclScope
// to join with the names declared so far at such an instance. The text is the
// same each time the enclosing module is elaborated, so the first recording
// for a declaration is kept: the strings it owns are what the views
// BeginNestedDeclScope hands on point into, and a second elaboration of the
// enclosing module must not free them.
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

// The declared type of a module item, paired with the word §6.18's report uses
// for the construct that declares it.
struct ScopePrefixedType {
  const DataType* type = nullptr;
  std::string_view construct;
};

// Parser::ParseNamedType records a class scope resolution prefix in
// DataType::scope_name whatever declares the type, so it reaches a typedef
// (Parser::ParseTypedef), a type parameter assignment
// (Parser::ParseTypeParamDecl) and a variable declaration
// (Parser::ParseVarDeclList) alike. Returns a null `type` for an item that
// declares no such type.
ScopePrefixedType ScopePrefixedTypeOfItem(const ModuleItem* item) {
  switch (item->kind) {
    case ModuleItemKind::kTypedef:
      return {&item->typedef_type, "a typedef"};
    case ModuleItemKind::kParamDecl:
      // Parser::ParseTypeParamDecl marks a type parameter by setting
      // data_type.kind to kVoid and stores the assigned type in typedef_type.
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
    const ModuleDecl* decl) {
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
