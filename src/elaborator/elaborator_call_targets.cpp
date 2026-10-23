#include "elaborator/elaborator_call_targets.h"

#include <cstddef>
#include <deque>
#include <format>
#include <functional>
#include <initializer_list>
#include <memory>
#include <string>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/class_member_names.h"
#include "elaborator/elaborator_call_targets_internal.h"
#include "elaborator/elaborator_enclosing_subroutines.h"
#include "elaborator/elaborator_enum_constants.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/local_type_sites.h"
#include "elaborator/operator_result_members.h"
#include "elaborator/package_references.h"
#include "elaborator/struct_member_selects.h"
#include "elaborator/type_site_lookup.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

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

// The interface a value declared with `type` refers to an instance of, where
// it is a virtual interface (§25.9); empty for any other type.
std::string_view VifInterface(const DataType& type) {
  return type.kind == DataTypeKind::kVirtualInterface ? type.type_name
                                                      : std::string_view();
}

// The type the variable `root` names is declared with, as written in the
// scope or the scope within it declaring it, with the unpacked dimensions
// written after its name, or the type of the property a member access `root`
// names of the class a handle holds (HeldPropertyType); no type where `root`
// names no variable, or one whose type is a type parameter, typedef or class
// the scope declares for itself alone.
SitedType DeclaredType(const Expr& root, const DataScope& scope) {
  if (root.kind == ExprKind::kMemberAccess) {
    return HeldPropertyType(root, scope);
  }
  const DeclaredVar* var = scope.Declared(root.text);
  if (var == nullptr || scope.local_types.contains(var->type->type_name)) {
    return {};
  }
  return {var->type, scope.SiteOf(*var), var->dims};
}

// §8.4: the property of the class a variable of the scope holds a handle of
// that the member access `access`, h.vif, names; null for any other
// expression and for a name the class declares no property under.
const ClassMember* HandleProperty(const Expr& access, const DataScope& scope) {
  if (access.kind != ExprKind::kMemberAccess || access.is_scope_resolution ||
      access.lhs->kind != ExprKind::kIdentifier) {
    return nullptr;
  }
  const DeclaredVar* holder = scope.Declared(access.lhs->text);
  const ClassDecl* cls =
      holder == nullptr ? nullptr : ClassNamed(scope, *holder, 0);
  if (cls == nullptr) return nullptr;
  const ClassMember* found = nullptr;
  for (const ClassMember* member : cls->members) {
    if (member->kind == ClassMemberKind::kProperty &&
        member->name == access.rhs->text) {
      found = member;
    }
  }
  return found;
}

// The variable the root `root` of a prefix names: the innermost declaration
// of a plain name, v, or a property of the class whose method writes the
// prefix, reached through `this`, this.vif (§8.11); null for anything else.
const DeclaredVar* RootVar(const Expr& root, const DataScope& scope) {
  if (root.kind == ExprKind::kIdentifier) return scope.Declared(root.text);
  const bool kThis =
      root.kind == ExprKind::kMemberAccess && !root.is_scope_resolution &&
      root.lhs->kind == ExprKind::kIdentifier && root.lhs->text == "this";
  return kThis ? scope.Property(root.rhs->text) : nullptr;
}

// §25.9: the interface the virtual interface `prefix` names refers to an
// instance of: a variable of the module or of a block around the call, v, a
// property of the class whose method writes the call, vif or this.vif, or a
// property of the class a variable holds a handle of, h.vif, or an element of
// an array of any of them, one select per unpacked dimension (§7.4), va[0] or
// h.vifs[0]; empty for anything else.
std::string_view VifOf(const Expr& prefix, const DataScope& scope) {
  std::size_t selects = 0;
  const Expr& root = SelectRoot(prefix, selects);
  if (const DeclaredVar* var = RootVar(root, scope)) {
    return var->dims == selects ? VifInterface(*var->type) : std::string_view();
  }
  const ClassMember* property = HandleProperty(root, scope);
  return property != nullptr && property->unpacked_dims.size() == selects
             ? VifInterface(property->data_type)
             : std::string_view();
}

// §8.11: the property of the class whose method writes `root` that `root`
// names, vif where no local variable of the method hides it, or this.vif;
// null for anything else.
const DeclaredVar* OwnProperty(const Expr& root, const DataScope& scope) {
  if (root.kind != ExprKind::kIdentifier) return RootVar(root, scope);
  const DeclaredVar* property = scope.Property(root.text);
  return property != nullptr && scope.Declared(root.text) == property ? property
                                                                      : nullptr;
}

// The declaration of the class property `root` names: one of the class whose
// method writes it, vif or this.vif, or one of the class a variable holds a
// handle of, h.vif; one with no type for anything else.
DeclaredVar SelectedProperty(const Expr& root, const DataScope& scope) {
  if (const DeclaredVar* own = OwnProperty(root, scope)) return *own;
  const ClassMember* held = HandleProperty(root, scope);
  return held == nullptr
             ? DeclaredVar{}
             : DeclaredVar{&held->data_type, held->unpacked_dims.size()};
}

// §8.5 and §8.6: a member access `access`, h.m, applied to a handle of a class
// that, with the classes it extends or implements, declares nothing `m`
// names; reported under `rule`, §8.6 where the access is what a call calls and
// §8.5 otherwise.
void ReportUndeclaredMember(const Expr& access, std::string_view rule,
                            const DataScope& scope, DiagEngine& diag) {
  const ClassDecl* cls = HandleClass(*access.lhs, scope);
  std::unordered_set<std::string_view> names;
  if (cls == nullptr || !scope.classes->SelectableNames(*cls, names) ||
      names.contains(access.rhs->text)) {
    return;
  }
  diag.Error(access.rhs->range.start,
             std::format("class '{}' has no member named '{}'", cls->name,
                         access.rhs->text),
             Subclause(rule));
}

// §25.9 with §7.4: a select `select` into a class property that is a virtual
// interface, past the property's unpacked dimensions, vif[0], this.vif[0] or
// h.vif[0], which selects into a virtual interface; reported once, at the
// first select past them.
void ReportPropertyVifSelect(const Expr& select, const DataScope& scope,
                             DiagEngine& diag) {
  std::size_t selects = 0;
  const DeclaredVar kProperty =
      SelectedProperty(SelectRoot(select, selects), scope);
  if (kProperty.type == nullptr ||
      kProperty.type->kind != DataTypeKind::kVirtualInterface ||
      kProperty.dims + 1 != selects) {
    return;
  }
  diag.Error(select.range.start, "bit-select on virtual interface is illegal",
             Subclause("25.9"));
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

// Each call by a plain name `expr` holds, itself included, each call through a
// virtual interface, each select into a class property that is one, and each
// member access naming nothing its class, its string or enumeration type or
// the operator result it is applied to has, `rule` being the subclause one
// `expr` itself makes on a class is reported under. A scope resolution, C::m or
// p::m, selects from no value.
void CheckExprCalls(const Expr* expr, const DataScope& scope, DiagEngine& diag,
                    std::string_view rule = "8.5") {
  if (expr == nullptr) return;
  if (expr->kind == ExprKind::kMemberAccess && !expr->is_scope_resolution) {
    ReportUndeclaredMember(*expr, rule, scope, diag);
    ReportNoBuiltInMethod(*expr, scope, diag);
    ReportUndeclaredAggregateMember(
        *expr, scope.unit,
        [&scope](const Expr& root) { return DeclaredType(root, scope); }, diag);
    ReportOperatorResultMember(
        *expr, [&scope](const Expr& e) { return AppliedValueKind(e, scope); },
        kStringMethods, diag);
  }
  if (const Expr* callee = NamedCallee(*expr)) {
    ReportIfData(callee->text, expr->range.start, scope, diag);
  }
  if (expr->kind == ExprKind::kCall && expr->lhs != nullptr) {
    ReportVifCall(*expr, scope, diag);
  }
  if (expr->kind == ExprKind::kSelect)
    ReportPropertyVifSelect(*expr, scope, diag);
  const Expr* called = expr->kind == ExprKind::kCall ? expr->lhs : nullptr;
  ForEachExprChild(expr, [&](const Expr* child) {
    CheckExprCalls(child, scope, diag, child == called ? "8.6" : "8.5");
  });
}

// The calls `stmt` and the statements it holds make by a plain name: a bare
// call statement, `x;`, and each call an expression of theirs holds, with the
// variables a block declares in scope over the statements the block holds,
// their types named at the block's site.
void CheckStmtCalls(const Stmt* stmt, DataScope& scope, DiagEngine& diag) {
  if (stmt == nullptr) return;
  const std::size_t kOuter = scope.blocks.size();
  const LocalTypeSites::Depth kOuterSites = scope.local_sites.Here();
  if (stmt->kind == StmtKind::kBlock || stmt->kind == StmtKind::kFork) {
    const std::vector<Stmt*>& items =
        stmt->kind == StmtKind::kFork ? stmt->fork_stmts : stmt->stmts;
    scope.local_sites.OpenStmts(items, scope.Site());
    for (const Stmt* item : items) {
      if (item->kind == StmtKind::kVarDecl) {
        scope.blocks.emplace_back(
            item->var_name,
            DeclaredVar{&item->var_decl_type, item->var_unpacked_dims.size(),
                        scope.local_sites.Innermost()});
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
  scope.local_sites.Restore(kOuterSites);
}

// §13.3: each call the body of the task or function `item` writes, the
// subroutine's formal arguments and the variables its body declares in scope
// over its statements as a block's are (§23.9), the body's types named at the
// body's site.
void CheckSubroutineCalls(const ModuleItem& item, DataScope& scope,
                          DiagEngine& diag) {
  const std::size_t kOuter = scope.blocks.size();
  const LocalTypeSites::Depth kOuterSites = scope.local_sites.Here();
  for (const FunctionArg& arg : item.func_args) {
    scope.blocks.emplace_back(
        arg.name, DeclaredVar{&arg.data_type, arg.unpacked_dims.size(),
                              scope.local_sites.Innermost()});
  }
  scope.local_sites.OpenStmts(item.func_body_stmts, scope.Site());
  for (const Stmt* stmt : item.func_body_stmts) {
    if (stmt->kind == StmtKind::kVarDecl) {
      scope.blocks.emplace_back(
          stmt->var_name,
          DeclaredVar{&stmt->var_decl_type, stmt->var_unpacked_dims.size(),
                      scope.local_sites.Innermost()});
    }
  }
  for (const Stmt* stmt : item.func_body_stmts) {
    CheckStmtCalls(stmt, scope, diag);
  }
  scope.blocks.resize(kOuter);
  scope.local_sites.Restore(kOuterSites);
}

// §6.19.3: each named constant the enumeration `type` writes, as a value of
// `scope` of that enumeration; a member a range names, R[2], declares the
// numbered constants §6.19.2 gives it, R0 and R1, and not its own name, its
// bounds being numbers, which fold with no scope. A variable of the
// constant's name keeps its own declaration.
void DeclareEnumConstants(const DataType& type, DataScope& scope) {
  for (const EnumMember& member : type.enum_members) {
    if (member.range_start == nullptr) {
      scope.module_vars.emplace(member.name, DeclaredVar{&type, 0});
      continue;
    }
    for (const std::string& name : EnumMemberDeclaredNames(member, {})) {
      const std::string& kept = scope.numbered_names.emplace_back(name);
      scope.module_vars.emplace(kept, DeclaredVar{&type, 0});
    }
  }
}

// The declaration of each variable the module `decl` declares, as a variable
// of `scope`: each of its ports (§23.2.2), each object an explicitly named
// port of it stands for (§23.2.2.1), and each variable its items declare, a
// body declaration of a port's name giving the port its type; and each named
// constant of an enumeration a port or an item writes.
void DeclareModuleVars(const ModuleDecl& decl, DataScope& scope) {
  for (const auto* ports : {&decl.ports, &decl.port_expr_objects}) {
    for (const PortDecl& port : *ports) {
      scope.module_vars[port.name] =
          DeclaredVar{&port.data_type, port.unpacked_dims.size()};
      DeclareEnumConstants(port.data_type, scope);
    }
  }
  for (const ModuleItem* item : decl.items) {
    if (item->kind == ModuleItemKind::kVarDecl) {
      scope.module_vars[item->name] =
          DeclaredVar{&item->data_type, item->unpacked_dims.size()};
    }
    DeclareEnumConstants(item->data_type, scope);
    DeclareEnumConstants(item->typedef_type, scope);
  }
}

// §3.12.1: each variable and net the compilation unit `unit` declares, as data
// of `scope`, but for a name the module declares as something else, which
// hides it (§23.9).
void DeclareUnitData(const CompilationUnit& unit, DataScope& scope) {
  for (const ModuleItem* item : unit.cu_items) {
    const bool kData = item->kind == ModuleItemKind::kVarDecl ||
                       item->kind == ModuleItemKind::kNetDecl;
    if (kData && !scope.subroutines.contains(item->name) &&
        !scope.uncallable.contains(item->name)) {
      scope.module.insert(item->name);
    }
  }
}

// The names the items of module `decl` declare, each in the set of `scope`
// its kind puts it in: data, subroutines and the rest, which no call names.
void DeclareModuleItems(const ModuleDecl& decl, const CompilationUnit& unit,
                        DataScope& scope) {
  DeclareModuleVars(decl, scope);
  std::unordered_set<std::string_view>& subroutines = scope.subroutines;
  for (const ModuleItem* item : decl.items) {
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
}

// §8.13: the properties the class `cls` declares and those it inherits, as
// the properties of `scope`, a derived class's shadowing a base's of its name.
// Each base is looked up from the scope's site; no class is its own ancestor
// (§8.13), so the walk ends at a class that extends none.
void DeclareClassProperties(const ClassDecl& cls, DataScope& scope) {
  const TypeSite kSite = scope.Site();
  for (const ClassDecl* walked = &cls; walked != nullptr;
       walked = BaseClassIn(scope.unit, kSite, *walked)) {
    for (const ClassMember* member : walked->members) {
      if (member->kind == ClassMemberKind::kProperty) {
        scope.properties.emplace(
            member->name,
            DeclaredVar{&member->data_type, member->unpacked_dims.size()});
      }
    }
  }
}

// The scope a method of the class `cls`, declared in the scope `site` sees,
// is walked in: the site's, its variables among them (§23.9), with the
// class's properties hiding those of their names.
DataScope ClassScope(const ClassDecl& cls, const DataScope& site) {
  DataScope scope{site.visible, site.unit, site.items};
  scope.site = site.site;
  scope.module_vars = site.module_vars;
  scope.local_types = site.local_types;
  scope.classes = site.classes;
  scope.classes->AddLocalTypes(cls, scope.local_types);
  scope.cls = &cls;
  DeclareClassProperties(cls, scope);
  return scope;
}

// §8.3: each call the methods of the class `cls`, declared in the scope
// `site`, write, and those of each class nested in it (§8.23).
void CheckClassCalls(const ClassDecl& cls, const DataScope& site,
                     DiagEngine& diag) {
  DataScope scope = ClassScope(cls, site);
  for (const ClassMember* member : cls.members) {
    if (member->kind == ClassMemberKind::kMethod) {
      CheckSubroutineCalls(*member->method, scope, diag);
    }
    if (member->nested_class != nullptr) {
      CheckClassCalls(*member->nested_class, site, diag);
    }
  }
}

// Each call the classes the scope `site` declares write in their methods,
// `classes` among them where the site's items do not hold its classes, and
// each a method defined out of its class's body there writes (§8.24), in the
// scope of the class the site sees under the name the method is written
// behind.
void CheckSiteClasses(const DataScope& site,
                      const std::vector<ClassDecl*>& classes,
                      DiagEngine& diag) {
  for (const ClassDecl* cls : classes) CheckClassCalls(*cls, site, diag);
  const TypeSite kSite = site.Site();
  for (const ModuleItem* item : site.items) {
    if (item->kind == ModuleItemKind::kClassDecl) {
      CheckClassCalls(*item->class_decl, site, diag);
      continue;
    }
    const bool kOutOfBody = (item->kind == ModuleItemKind::kTaskDecl ||
                             item->kind == ModuleItemKind::kFunctionDecl) &&
                            !item->method_class.empty();
    const ClassDecl* cls =
        kOutOfBody ? ClassIn(site.unit, kSite, item->method_class) : nullptr;
    if (cls == nullptr) continue;
    DataScope scope = ClassScope(*cls, site);
    CheckSubroutineCalls(*item, scope, diag);
  }
}

void CheckItemCalls(const std::vector<ModuleItem*>& items, DataScope& scope,
                    DiagEngine& diag);

// §27: each call the generate block whose items are `items` writes, the
// variables and nets it declares in scope over its items as a block's are,
// their types named at the block's site (§27.5), and the tasks and functions
// it declares callable there (§23.9).
void CheckGenerateBlockCalls(const std::vector<ModuleItem*>& items,
                             DataScope& scope, DiagEngine& diag) {
  const std::size_t kOuter = scope.blocks.size();
  const std::unordered_set<std::string_view> kOuterSubroutines =
      scope.subroutines;
  const LocalTypeSites::Depth kOuterSites = scope.local_sites.Here();
  scope.local_sites.OpenItems(items, scope.Site());
  for (const ModuleItem* item : items) {
    if (item->kind == ModuleItemKind::kVarDecl ||
        item->kind == ModuleItemKind::kNetDecl) {
      scope.blocks.emplace_back(
          item->name, DeclaredVar{&item->data_type, item->unpacked_dims.size(),
                                  scope.local_sites.Innermost()});
    } else if (IsSubroutineItem(*item)) {
      scope.subroutines.insert(item->name);
    }
  }
  CheckItemCalls(items, scope, diag);
  scope.blocks.resize(kOuter);
  scope.subroutines = kOuterSubroutines;
  scope.local_sites.Restore(kOuterSites);
}

// §27.4 and §27.5: each call the blocks of the generate construct `construct`
// write: a loop's one block, each block of a conditional construct and of the
// else chain after it, and each case item's block.
void CheckGenerateCalls(const ModuleItem& construct, DataScope& scope,
                        DiagEngine& diag) {
  for (const ModuleItem* branch = &construct; branch != nullptr;
       branch = branch->gen_else) {
    CheckGenerateBlockCalls(branch->gen_body, scope, diag);
    for (const GenerateCaseItem& item : branch->gen_case_items) {
      CheckGenerateBlockCalls(item.body, scope, diag);
    }
  }
}

// Each call the items `items` of a module or of a generate block write: in
// their procedures, in the tasks and functions they declare, a method defined
// out of its class's body (§8.24) excepted, and in the generate constructs
// among them.
void CheckItemCalls(const std::vector<ModuleItem*>& items, DataScope& scope,
                    DiagEngine& diag) {
  for (const ModuleItem* item : items) {
    if (IsProceduralItemKind(item->kind)) {
      CheckStmtCalls(item->body, scope, diag);
    } else if ((item->kind == ModuleItemKind::kTaskDecl ||
                item->kind == ModuleItemKind::kFunctionDecl) &&
               item->method_class.empty()) {
      CheckSubroutineCalls(*item, scope, diag);
    } else if (item->kind == ModuleItemKind::kGenerateFor ||
               item->kind == ModuleItemKind::kGenerateIf ||
               item->kind == ModuleItemKind::kGenerateCase) {
      CheckGenerateCalls(*item, scope, diag);
    }
  }
}

}  // namespace

void ReportCallsOfDataNames(
    const ModuleDecl& decl, const CompilationUnit& unit,
    const std::function<bool(std::string_view)>& visible, DiagEngine& diag) {
  DataScope scope{visible, unit, decl.items};
  scope.local_types = decl.type_param_names;
  scope.classes = std::make_shared<const SoleClassIndex>(unit);
  DeclareModuleItems(decl, unit, scope);
  DeclareUnitData(unit, scope);
  CheckItemCalls(decl.items, scope, diag);
}

void ReportClassMethodCalls(const CompilationUnit& unit, DiagEngine& diag) {
  const std::function<bool(std::string_view)> kSeesAll = [](std::string_view) {
    return true;
  };
  const auto kClasses = std::make_shared<const SoleClassIndex>(unit);
  DataScope at_unit{kSeesAll, unit, unit.cu_items};
  at_unit.site = SiteKind::kUnit;
  at_unit.classes = kClasses;
  CheckSiteClasses(at_unit, unit.classes, diag);
  for (const PackageDecl* package : unit.packages) {
    DataScope at_package{kSeesAll, unit, package->items};
    at_package.site = SiteKind::kPackage;
    at_package.classes = kClasses;
    CheckSiteClasses(at_package, {}, diag);
  }
  for (const std::vector<ModuleDecl*>* decls :
       {&unit.modules, &unit.interfaces, &unit.programs, &unit.checkers}) {
    for (const ModuleDecl* decl : *decls) {
      DataScope at_module{kSeesAll, unit, decl->items};
      at_module.local_types = decl->type_param_names;
      at_module.classes = kClasses;
      DeclareModuleVars(*decl, at_module);
      CheckSiteClasses(at_module, {}, diag);
    }
  }
}

}  // namespace delta
