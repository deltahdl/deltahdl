#include "elaborator/elaborator_call_targets.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
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

// A variable's declaration: the type it was declared with and the number of
// unpacked dimensions it writes after its name (§7.4).
struct DeclaredVar {
  const DataType* type = nullptr;
  std::size_t dims = 0;
};

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
  // The declaration of each variable of the module and of a block around the
  // statement walked.
  std::unordered_map<std::string_view, DeclaredVar> module_vars = {};
  std::unordered_set<std::string_view> module = {};
  std::vector<std::pair<std::string_view, DeclaredVar>> blocks = {};
  std::unordered_set<std::string_view> uncallable = {};
  std::unordered_set<std::string_view> subroutines = {};

  bool Names(std::string_view name) const {
    return module.contains(name) ||
           std::ranges::any_of(blocks, [name](const auto& declared) {
             return declared.first == name;
           });
  }

  // The declaration of the variable `name` names in the scope, the innermost
  // block's first (§23.9); null for a name no variable bears.
  const DeclaredVar* Declared(std::string_view name) const {
    for (auto it = blocks.rbegin(); it != blocks.rend(); ++it) {
      if (it->first == name) return &it->second;
    }
    const auto kFound = module_vars.find(name);
    return kFound == module_vars.end() ? nullptr : &kFound->second;
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

// The interface a value declared with `type` refers to an instance of, where
// it is a virtual interface (§25.9); empty for any other type.
std::string_view VifInterface(const DataType& type) {
  return type.kind == DataTypeKind::kVirtualInterface ? type.type_name
                                                      : std::string_view();
}

// The name the item `item` declares, a class's being its declaration's.
std::string_view DeclaredName(const ModuleItem& item) {
  return item.kind == ModuleItemKind::kClassDecl ? item.class_decl->name
                                                 : item.name;
}

// The kind of scope a type name is written in (§23.9): a module's, which the
// compilation unit's scope surrounds, the compilation unit's own, or a
// package's, which sees neither (§26.2).
enum class SiteKind : std::uint8_t { kModule, kUnit, kPackage };

// Where a type name is looked up: among the items of the scope it is written
// in, those before `end` alone, as a typedef names only a type declared before
// it (§6.18), then in the scopes around that one.
struct TypeSite {
  const std::vector<ModuleItem*>* items = nullptr;
  std::size_t end = 0;
  SiteKind kind = SiteKind::kModule;
};

// An item a lookup found, with the site the names its declaration writes are
// looked up at: the items of its own scope before it.
struct FoundItem {
  const ModuleItem* item = nullptr;
  TypeSite site = {};
};

// The last item of kind `kind` among the first `end` of `items` declaring
// `name`, a forward typedef (§6.18), which names no type, excepted; `kind`
// is the kind of scope `items` belong to.
FoundItem ItemBefore(const std::vector<ModuleItem*>& items, std::size_t end,
                     ModuleItemKind kind, std::string_view name,
                     SiteKind scope) {
  FoundItem found;
  for (std::size_t i = 0; i < end; ++i) {
    const ModuleItem& item = *items[i];
    if (item.kind == kind && DeclaredName(item) == name &&
        item.forward_type_kind == DataTypeKind::kImplicit) {
      found = {&item, {&items, i, scope}};
    }
  }
  return found;
}

// §26.2: the item of kind `kind` the package `package` of the compilation unit
// declares under `name`.
FoundItem PackageItem(const CompilationUnit& unit, std::string_view package,
                      ModuleItemKind kind, std::string_view name) {
  FoundItem found;
  for (const PackageDecl* decl : unit.packages) {
    if (decl->name == package) {
      found = ItemBefore(decl->items, decl->items.size(), kind, name,
                         SiteKind::kPackage);
    }
  }
  return found;
}

// §26.3: the item of kind `kind` named `name` an import among the first `end`
// of `items` brings in, by its item name or with a wildcard.
FoundItem ImportedItem(const CompilationUnit& unit,
                       const std::vector<ModuleItem*>& items, std::size_t end,
                       ModuleItemKind kind, std::string_view name) {
  FoundItem found;
  for (std::size_t i = 0; i < end; ++i) {
    if (items[i]->kind != ModuleItemKind::kImportDecl) continue;
    const ImportItem& import = items[i]->import_item;
    if (!import.is_wildcard && import.item_name != name) continue;
    const FoundItem kHit = PackageItem(unit, import.package_name, kind, name);
    if (kHit.item != nullptr) found = kHit;
  }
  return found;
}

// §23.9 with §26.3: the item of kind `kind` named `name` the site `site` sees:
// one its scope declares, else one an import of its scope brings in, else,
// for a module, one the compilation unit declares or imports.
FoundItem SiteItem(const CompilationUnit& unit, const TypeSite& site,
                   ModuleItemKind kind, std::string_view name) {
  FoundItem found = ItemBefore(*site.items, site.end, kind, name, site.kind);
  if (found.item == nullptr) {
    found = ImportedItem(unit, *site.items, site.end, kind, name);
  }
  if (found.item == nullptr && site.kind == SiteKind::kModule) {
    const TypeSite kUnit{&unit.cu_items, unit.cu_items.size(), SiteKind::kUnit};
    found = SiteItem(unit, kUnit, kind, name);
  }
  return found;
}

// §8.3: the class named `name` the scope of `site` sees, wherever in that scope
// its declaration stands, as a class may be referred to before it is declared
// once a forward typedef names it (§6.18); null where none is. A module's or
// the compilation unit's search reaches the compilation unit's classes.
const ClassDecl* ClassIn(const CompilationUnit& unit, const TypeSite& site,
                         std::string_view name) {
  const TypeSite kWhole{site.items, site.items->size(), site.kind};
  const FoundItem kFound =
      SiteItem(unit, kWhole, ModuleItemKind::kClassDecl, name);
  if (kFound.item != nullptr) return kFound.item->class_decl;
  if (site.kind == SiteKind::kPackage) return nullptr;
  for (const ClassDecl* decl : unit.classes) {
    if (decl->name == name) return decl;
  }
  return nullptr;
}

// §8.24 with §26.3: the class named `name` written behind the scope
// `scope_name`, p::K or H::Inner: one the package of that name declares, else
// one nested in the class of that name the site sees; null where neither is.
const ClassDecl* ScopedClass(const CompilationUnit& unit, const TypeSite& site,
                             std::string_view scope_name,
                             std::string_view name) {
  const FoundItem kInPackage =
      PackageItem(unit, scope_name, ModuleItemKind::kClassDecl, name);
  if (kInPackage.item != nullptr) return kInPackage.item->class_decl;
  const ClassDecl* outer = ClassIn(unit, site, scope_name);
  if (outer == nullptr) return nullptr;
  for (const ClassMember* member : outer->members) {
    if (member->nested_class != nullptr && member->nested_class->name == name) {
      return member->nested_class;
    }
  }
  return nullptr;
}

// §6.18: the typedef the named type `type`, written at `site`, names: behind
// its package's scope, p::KT, or else the one the site sees.
FoundItem TypedefOf(const CompilationUnit& unit, const TypeSite& site,
                    const DataType& type) {
  if (!type.scope_name.empty()) {
    return PackageItem(unit, type.scope_name, ModuleItemKind::kTypedef,
                       type.type_name);
  }
  return SiteItem(unit, site, ModuleItemKind::kTypedef, type.type_name);
}

// §8.3 with §6.18 and §26.3: the class declaration the type `type` of a
// variable of the module names, through each typedef it is written as, each
// typedef's own type looked up as the scope declaring that typedef sees it
// before the typedef; null where none is. Each step reaches a declaration
// before the last in its scope, or a scope around it or a package, which
// leads to no module; a package reaches only one declared before it, a
// typedef naming no type the parser has not yet read, so the walk ends.
const ClassDecl* ClassNamed(const DataScope& scope, const DataType& type) {
  const CompilationUnit& unit = scope.unit;
  TypeSite site{&scope.items, scope.items.size(), SiteKind::kModule};
  const DataType* named = &type;
  for (FoundItem def = TypedefOf(unit, site, *named); def.item != nullptr;
       def = TypedefOf(unit, site, *named)) {
    named = &def.item->typedef_type;
    site = def.site;
  }
  if (!named->scope_name.empty()) {
    return ScopedClass(unit, site, named->scope_name, named->type_name);
  }
  return ClassIn(unit, site, named->type_name);
}

// §25.9: the interface the virtual interface `prefix` names refers to an
// instance of: a variable of the module or of a block around the call, v, or a
// property of the class a variable holds a handle of, h.vif, or an element of
// an array of either, one select per unpacked dimension (§7.4), va[0] or
// h.vifs[0]; empty for anything else.
std::string_view VifOf(const Expr& prefix, const DataScope& scope) {
  const Expr* root = &prefix;
  std::size_t selects = 0;
  while (root->kind == ExprKind::kSelect) {
    ++selects;
    root = root->base;
  }
  if (root->kind == ExprKind::kIdentifier) {
    const DeclaredVar* var = scope.Declared(root->text);
    return var != nullptr && var->dims == selects ? VifInterface(*var->type)
                                                  : std::string_view();
  }
  if (root->kind != ExprKind::kMemberAccess || root->is_scope_resolution ||
      root->lhs->kind != ExprKind::kIdentifier) {
    return {};
  }
  const DeclaredVar* holder = scope.Declared(root->lhs->text);
  const ClassDecl* cls =
      holder == nullptr ? nullptr : ClassNamed(scope, *holder->type);
  if (cls == nullptr) return {};
  std::string_view iface;
  for (const ClassMember* member : cls->members) {
    if (member->kind == ClassMemberKind::kProperty &&
        member->name == root->rhs->text) {
      iface = member->unpacked_dims.size() == selects
                  ? VifInterface(member->data_type)
                  : std::string_view();
    }
  }
  return iface;
}

// §25.9: a call `call` through a virtual interface, v.t(), naming no task or
// function the interface declares.
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
        scope.blocks.emplace_back(
            item->var_name,
            DeclaredVar{&item->var_decl_type, item->var_unpacked_dims.size()});
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
      scope.module_vars[item->name] =
          DeclaredVar{&item->data_type, item->unpacked_dims.size()};
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
