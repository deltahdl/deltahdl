#include "elaborator/class_method_reads.h"

#include <cstddef>
#include <format>
#include <functional>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/elaborator_scope_rules_names.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

// The names `this` and `super` stand for the object a method runs on and its
// base (§8.11, §8.15); neither is declared.
bool IsObjectName(std::string_view name) {
  return name == "this" || name == "super";
}

// The methods of `cls` and of the classes it nests, each given to `fn`.
void ForEachMethod(const ClassDecl* cls,
                   const std::function<void(const ModuleItem*)>& fn) {
  for (const ClassMember* m : cls->members) {
    if (m->kind == ClassMemberKind::kMethod && m->method != nullptr) {
      fn(m->method);
    } else if (m->kind == ClassMemberKind::kClassDecl &&
               m->nested_class != nullptr) {
      ForEachMethod(m->nested_class, fn);
    }
  }
}

// Every class of `unit`: those at compilation-unit scope and those the items of
// its packages, modules, interfaces, programs and checkers declare.
template <typename Fn>
void ForEachClass(const CompilationUnit* unit, Fn&& fn) {
  for (const ClassDecl* cls : unit->classes) fn(cls);
  auto in_items = [&fn](const std::vector<ModuleItem*>& items) {
    for (const ModuleItem* item : items) {
      if (item->kind == ModuleItemKind::kClassDecl &&
          item->class_decl != nullptr) {
        fn(item->class_decl);
      }
    }
  };
  for (const auto* scopes :
       {&unit->modules, &unit->interfaces, &unit->programs, &unit->checkers}) {
    for (const ModuleDecl* scope : *scopes) in_items(scope->items);
  }
  for (const PackageDecl* pkg : unit->packages) in_items(pkg->items);
}

}  // namespace

UnitDeclaredNames::UnitDeclaredNames(const CompilationUnit* unit) {
  AddItems(unit->cu_items);
  for (const ClassDecl* cls : unit->classes) AddClass(cls);
  for (const PackageDecl* pkg : unit->packages) {
    names_.insert(pkg->name);
    AddItems(pkg->items);
  }
  for (const auto* scopes :
       {&unit->modules, &unit->interfaces, &unit->programs, &unit->checkers}) {
    for (const ModuleDecl* scope : *scopes) AddScope(scope);
  }
}

bool UnitDeclaredNames::Declares(std::string_view name) const {
  if (names_.contains(name) || IsObjectName(name)) return true;
  size_t digits = name.find_last_not_of("0123456789");
  if (digits == std::string_view::npos || digits + 1 == name.size()) {
    return false;
  }
  return numbered_enum_names_.contains(name.substr(0, digits + 1));
}

void UnitDeclaredNames::AddItems(const std::vector<ModuleItem*>& items) {
  for (const ModuleItem* item : items) {
    if (!item->name.empty()) names_.insert(item->name);
    AddEnumerations(item->data_type);
    if (item->kind == ModuleItemKind::kTypedef) {
      AddEnumerations(item->typedef_type);
    }
    if (item->kind == ModuleItemKind::kClassDecl &&
        item->class_decl != nullptr) {
      AddClass(item->class_decl);
    }
  }
}

void UnitDeclaredNames::AddScope(const ModuleDecl* scope) {
  names_.insert(scope->name);
  for (const PortDecl& port : scope->ports) names_.insert(port.name);
  for (const auto& [name, value] : scope->params) names_.insert(name);
  names_.insert(scope->type_param_names.begin(), scope->type_param_names.end());
  AddItems(scope->items);
}

void UnitDeclaredNames::AddClass(const ClassDecl* cls) {
  names_.insert(cls->name);
  for (const auto& [name, value] : cls->params) names_.insert(name);
  names_.insert(cls->type_param_names.begin(), cls->type_param_names.end());
  for (const ClassMember* m : cls->members) {
    if (!m->name.empty()) names_.insert(m->name);
    AddEnumerations(m->data_type);
    if (m->typedef_item != nullptr) AddItems({m->typedef_item});
    if (m->nested_class != nullptr) AddClass(m->nested_class);
  }
}

void UnitDeclaredNames::AddEnumerations(const DataType& type) {
  for (const EnumMember& member : type.enum_members) {
    if (member.range_start != nullptr) {
      numbered_enum_names_.insert(member.name);
    } else {
      names_.insert(member.name);
    }
  }
}

void ReportClassMethodUnresolved(const CompilationUnit* unit,
                                 DiagEngine& diag) {
  UnitDeclaredNames declared(unit);
  ForEachClass(unit, [&](const ClassDecl* cls) {
    ForEachMethod(cls, [&](const ModuleItem* method) {
      std::unordered_set<std::string_view> locals;
      CollectSubroutineLocalNames(method, locals);
      std::vector<const Expr*> reads;
      for (const Stmt* s : method->func_body_stmts) {
        CollectProcRhsIdents(s, locals, reads);
      }
      for (const Expr* read : reads) {
        if (declared.Declares(read->text)) continue;
        diag.Error(
            read->range.start,
            std::format("reference to unresolved identifier '{}'", read->text),
            Subclause("23.9"));
      }
    });
  });
}

}  // namespace delta
