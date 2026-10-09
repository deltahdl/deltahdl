#include "elaborator/elaborator_call_targets.h"

#include <algorithm>
#include <cstddef>
#include <format>
#include <functional>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

// The names a walk of one module's procedures sees as variables or nets: the
// module's own, and those each block around the statement walked declares,
// the innermost last (§23.9); the other names the module itself declares, or
// imports as data, which a call statement cannot call; the tasks and
// functions the module declares; and, first, whether the scope or a module
// enclosing it sees a name at all.
struct DataScope {
  const std::function<bool(std::string_view)>& visible;
  const CompilationUnit& unit;
  const std::vector<ModuleItem*>& items;
  // The type each variable of the module and of a block around the statement
  // walked was declared with.
  std::unordered_map<std::string_view, const DataType*> module_types = {};
  std::unordered_set<std::string_view> module = {};
  std::vector<std::pair<std::string_view, const DataType*>> blocks = {};
  std::unordered_set<std::string_view> uncallable = {};
  std::unordered_set<std::string_view> subroutines = {};

  bool Names(std::string_view name) const {
    return module.contains(name) ||
           std::ranges::any_of(blocks, [name](const auto& declared) {
             return declared.first == name;
           });
  }

  // The type the variable `name` names in the scope was declared with, the
  // innermost block's first (§23.9); null for a name no variable bears.
  const DataType* TypeOf(std::string_view name) const {
    for (auto it = blocks.rbegin(); it != blocks.rend(); ++it) {
      if (it->first == name) return it->second;
    }
    const auto kFound = module_types.find(name);
    return kFound == module_types.end() ? nullptr : kFound->second;
  }
};

// Reports a call of `name` written at `loc` where the scope sees the name as
// a variable or a net.
void ReportIfData(std::string_view name, SourceLoc loc, const DataScope& scope,
                  DiagEngine& diag) {
  if (!scope.Names(name)) return;
  diag.Error(loc,
             std::format("'{}' names a variable or a net, and a call names a "
                         "task or a function",
                         name),
             Subclause("A.8.2"));
}

// The plain name the call `expr` calls, null where `expr` is no call by a
// plain name. A constructor call is none: its `lhs` is the object a shallow
// copy copies, `new src` (§8.12).
const Expr* NamedCallee(const Expr& expr) {
  const bool kNamed = expr.kind == ExprKind::kCall && expr.lhs != nullptr &&
                      expr.text != "new" &&
                      expr.lhs->kind == ExprKind::kIdentifier;
  return kNamed ? expr.lhs : nullptr;
}

// A.6.9: a call statement, `x;` or `x(...);`, whose name the scope declares
// as no task or function: a variable or a net (A.8.2), or anything else the
// module declares or imports as data, such as a parameter, a let or a
// sequence. A call with an argument list naming nothing the scope, the
// compilation unit or a module enclosing an instance of the module sees
// (§23.8) is an undeclared identifier (§23.9); a bare one is the scope rules'
// report.
void ReportStatementCall(const Stmt& stmt, const DataScope& scope,
                         DiagEngine& diag) {
  const bool kBare = stmt.expr->kind == ExprKind::kIdentifier;
  const Expr* callee = kBare ? stmt.expr : NamedCallee(*stmt.expr);
  if (callee == nullptr) return;
  const std::string_view kName = callee->text;
  if (scope.Names(kName)) {
    // A call with an argument list naming data is the expression walk's.
    if (kBare) ReportIfData(kName, stmt.range.start, scope, diag);
    return;
  }
  if (scope.uncallable.contains(kName)) {
    diag.Error(stmt.range.start,
               std::format("'{}' names no task or function, and a call "
                           "statement calls one",
                           kName),
               Subclause("A.6.9"));
    return;
  }
  if (kBare || scope.subroutines.contains(kName) || scope.visible(kName)) {
    return;
  }
  diag.Error(stmt.range.start, std::format("undeclared identifier '{}'", kName),
             Subclause("23.9"));
}

// Whether `item` declares a task or a function a call may call: one the
// source writes, or one a DPI import or export names (§35.5).
bool IsSubroutineItem(const ModuleItem& item) {
  return item.kind == ModuleItemKind::kTaskDecl ||
         item.kind == ModuleItemKind::kFunctionDecl ||
         item.kind == ModuleItemKind::kDpiImport ||
         item.kind == ModuleItemKind::kDpiExport;
}

// Whether the interface `unit` declares under `iface` declares a task or a
// function `name`.
bool InterfaceDeclaresSubroutine(const CompilationUnit& unit,
                                 std::string_view iface,
                                 std::string_view name) {
  bool declares = false;
  for (const ModuleDecl* decl : unit.interfaces) {
    if (decl->name != iface) continue;
    for (const ModuleItem* item : decl->items) {
      if (IsSubroutineItem(*item) && item->name == name) declares = true;
    }
  }
  return declares;
}

// §25.9: a call `call` through a virtual interface variable of the module,
// v.t(), naming no task or function the interface declares.
// The interface a value declared with `type` refers to an instance of, where
// it is a virtual interface (§25.9); empty for any other type and for none.
std::string_view VifInterface(const DataType* type) {
  return type != nullptr && type->kind == DataTypeKind::kVirtualInterface
             ? type->type_name
             : std::string_view();
}

// The name the item `item` declares, a class's being its declaration's.
std::string_view DeclaredName(const ModuleItem& item) {
  return item.kind == ModuleItemKind::kClassDecl ? item.class_decl->name
                                                 : item.name;
}

// The item of kind `kind` among `items` declaring `name`; null where none
// does.
const ModuleItem* ItemNamed(const std::vector<ModuleItem*>& items,
                            ModuleItemKind kind, std::string_view name) {
  const ModuleItem* found = nullptr;
  for (const ModuleItem* item : items) {
    if (item->kind == kind && DeclaredName(*item) == name) found = item;
  }
  return found;
}

// §26.2: the item of kind `kind` the package `package` of the compilation unit
// declares under `name`; null where it declares none.
const ModuleItem* PackageItem(const CompilationUnit& unit,
                              std::string_view package, ModuleItemKind kind,
                              std::string_view name) {
  const ModuleItem* found = nullptr;
  for (const PackageDecl* decl : unit.packages) {
    if (decl->name == package) found = ItemNamed(decl->items, kind, name);
  }
  return found;
}

// §26.3: the item of kind `kind` named `name` an import among `items` brings
// in, by its item name or with a wildcard; null where none does.
const ModuleItem* ImportedItem(const CompilationUnit& unit,
                               const std::vector<ModuleItem*>& items,
                               ModuleItemKind kind, std::string_view name) {
  const ModuleItem* found = nullptr;
  for (const ModuleItem* item : items) {
    if (item->kind != ModuleItemKind::kImportDecl) continue;
    const ImportItem& import = item->import_item;
    if (!import.is_wildcard && import.item_name != name) continue;
    const ModuleItem* hit = PackageItem(unit, import.package_name, kind, name);
    if (hit != nullptr) found = hit;
  }
  return found;
}

// §26.3: the item of kind `kind` named `name` the scope of the module sees
// by that name: the module's own, else the compilation unit's, else one the
// module's imports bring in, else one the compilation unit's do; null where
// none is.
const ModuleItem* VisibleItem(const DataScope& scope, ModuleItemKind kind,
                              std::string_view name) {
  const CompilationUnit& unit = scope.unit;
  const ModuleItem* found = ItemNamed(scope.items, kind, name);
  if (found == nullptr) found = ItemNamed(unit.cu_items, kind, name);
  if (found == nullptr) found = ImportedItem(unit, scope.items, kind, name);
  if (found == nullptr) found = ImportedItem(unit, unit.cu_items, kind, name);
  return found;
}

// The class the class declaration item `item` declares; null for none.
const ClassDecl* ClassOf(const ModuleItem* item) {
  return item == nullptr ? nullptr : item->class_decl;
}

// §8.3 with §6.18 and §26.3: the class declaration the type `type` names,
// through each typedef it is written as: behind its package scope, p::K, or
// else the module's own, the compilation unit's, then one an import brings
// in; null where none is. The hop limit keeps a
// cyclic typedef from looping.
const ClassDecl* ClassNamed(const DataScope& scope, const DataType& type) {
  const CompilationUnit& unit = scope.unit;
  const DataType* named = &type;
  for (int hops = 0; hops < 8; ++hops) {
    const ModuleItem* def =
        named->scope_name.empty()
            ? VisibleItem(scope, ModuleItemKind::kTypedef, named->type_name)
            : PackageItem(unit, named->scope_name, ModuleItemKind::kTypedef,
                          named->type_name);
    if (def == nullptr) break;
    named = &def->typedef_type;
  }
  if (!named->scope_name.empty()) {
    return ClassOf(PackageItem(unit, named->scope_name,
                               ModuleItemKind::kClassDecl, named->type_name));
  }
  if (const ClassDecl* own = ClassOf(ItemNamed(
          scope.items, ModuleItemKind::kClassDecl, named->type_name))) {
    return own;
  }
  for (const ClassDecl* decl : unit.classes) {
    if (decl->name == named->type_name) return decl;
  }
  return ClassOf(
      VisibleItem(scope, ModuleItemKind::kClassDecl, named->type_name));
}

// §25.9: the interface the virtual interface `prefix` names refers to an
// instance of: a variable of the module or of a block around the call, v, or
// a property of the class a variable holds a handle of, h.vif; empty for
// anything else.
std::string_view VifOf(const Expr& prefix, const DataScope& scope) {
  if (prefix.kind == ExprKind::kIdentifier) {
    return VifInterface(scope.TypeOf(prefix.text));
  }
  if (prefix.kind != ExprKind::kMemberAccess || prefix.is_scope_resolution ||
      prefix.lhs->kind != ExprKind::kIdentifier) {
    return {};
  }
  const DataType* holder = scope.TypeOf(prefix.lhs->text);
  const ClassDecl* cls =
      holder == nullptr ? nullptr : ClassNamed(scope, *holder);
  if (cls == nullptr) return {};
  std::string_view iface;
  for (const ClassMember* member : cls->members) {
    if (member->kind == ClassMemberKind::kProperty &&
        member->name == prefix.rhs->text) {
      iface = VifInterface(&member->data_type);
    }
  }
  return iface;
}

void ReportVifCall(const Expr& call, const DataScope& scope, DiagEngine& diag) {
  const Expr& callee = *call.lhs;
  if (callee.kind != ExprKind::kMemberAccess || callee.is_scope_resolution) {
    return;
  }
  const std::string_view kIface = VifOf(*callee.lhs, scope);
  if (kIface.empty() ||
      InterfaceDeclaresSubroutine(scope.unit, kIface, callee.rhs->text)) {
    return;
  }
  diag.Error(call.range.start,
             std::format("'{}' names no task or function of interface '{}'",
                         callee.rhs->text, kIface),
             Subclause("25.9"));
}

// Each call by a plain name `expr` holds, itself included, and each call
// through a virtual interface.
void CheckExprCalls(const Expr* expr, const DataScope& scope,
                    DiagEngine& diag) {
  if (expr == nullptr) return;
  if (const Expr* callee = NamedCallee(*expr)) {
    ReportIfData(callee->text, expr->range.start, scope, diag);
  }
  if (expr->kind == ExprKind::kCall && expr->lhs != nullptr) {
    ReportVifCall(*expr, scope, diag);
  }
  ForEachExprChild(
      expr, [&](const Expr* child) { CheckExprCalls(child, scope, diag); });
}

// The calls `stmt` and the statements it holds make by a plain name: a bare
// call statement, `x;`, and each call an expression of theirs holds, with the
// variables a block declares in scope over the statements the block holds.
void CheckStmtCalls(const Stmt* stmt, DataScope& scope, DiagEngine& diag) {
  if (stmt == nullptr) return;
  const std::size_t kOuter = scope.blocks.size();
  if (stmt->kind == StmtKind::kBlock || stmt->kind == StmtKind::kFork) {
    const std::vector<Stmt*>& items =
        stmt->kind == StmtKind::kFork ? stmt->fork_stmts : stmt->stmts;
    for (const Stmt* item : items) {
      if (item->kind == StmtKind::kVarDecl) {
        scope.blocks.emplace_back(item->var_name, &item->var_decl_type);
      }
    }
  }
  if (stmt->kind == StmtKind::kExprStmt) {
    ReportStatementCall(*stmt, scope, diag);
  }
  ForEachChildExpr(
      stmt, [&](const Expr* expr) { CheckExprCalls(expr, scope, diag); });
  ForEachChildStmt(stmt,
                   [&](Stmt* const& sub) { CheckStmtCalls(sub, scope, diag); });
  scope.blocks.resize(kOuter);
}

// §26.3: the variables and nets the package `import` names brings in, by its
// item name or with a wildcard, added to `names`.
void AddImportedData(const CompilationUnit& unit, const ImportItem& import,
                     std::unordered_set<std::string_view>& names) {
  for (const PackageDecl* package : unit.packages) {
    if (package->name != import.package_name) continue;
    for (const ModuleItem* item : package->items) {
      const bool kData = item->kind == ModuleItemKind::kVarDecl ||
                         item->kind == ModuleItemKind::kNetDecl;
      if (kData && (import.is_wildcard || item->name == import.item_name)) {
        names.insert(item->name);
      }
    }
  }
}

}  // namespace

std::unordered_set<std::string_view> EnclosingSubroutineNames(
    const CompilationUnit& unit, std::string_view module) {
  std::unordered_set<std::string_view> names;
  std::unordered_set<std::string_view> reached{module};
  std::vector<std::string_view> work{module};
  while (!work.empty()) {
    const std::string_view kChild = work.back();
    work.pop_back();
    for (const ModuleDecl* parent : unit.modules) {
      std::unordered_set<std::string_view> children;
      CollectInstantiatedNames(parent->items, children);
      if (!children.contains(kChild) || !reached.insert(parent->name).second) {
        continue;
      }
      for (const ModuleItem* item : parent->items) {
        if (IsSubroutineItem(*item)) names.insert(item->name);
      }
      work.push_back(parent->name);
    }
  }
  return names;
}

void ReportCallsOfDataNames(
    const ModuleDecl& decl, const CompilationUnit& unit,
    const std::function<bool(std::string_view)>& visible, DiagEngine& diag) {
  DataScope scope{visible, unit, decl.items};
  std::unordered_set<std::string_view>& subroutines = scope.subroutines;
  for (const ModuleItem* item : decl.items) {
    if (item->kind == ModuleItemKind::kVarDecl) {
      scope.module_types[item->name] = &item->data_type;
    }
    if (item->kind == ModuleItemKind::kVarDecl ||
        item->kind == ModuleItemKind::kNetDecl) {
      scope.module.insert(item->name);
    } else if (IsSubroutineItem(*item)) {
      subroutines.insert(item->name);
    } else if (!item->name.empty()) {
      scope.uncallable.insert(item->name);
    }
    if (item->kind == ModuleItemKind::kImportDecl) {
      AddImportedData(unit, item->import_item, scope.uncallable);
    }
  }
  // A name a DPI export gives a function the module also declares stays
  // callable whichever item the walk met first.
  for (std::string_view name : subroutines) scope.uncallable.erase(name);
  // §18.12: a scope randomize call may be written without its std:: prefix.
  subroutines.insert("randomize");
  for (const ModuleItem* item : decl.items) {
    if (IsProceduralItemKind(item->kind))
      CheckStmtCalls(item->body, scope, diag);
  }
}

}  // namespace delta
