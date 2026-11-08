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
#include "elaborator/assertion_body_slots.h"
#include "elaborator/assertion_walk.h"
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

void ReportDataCall(std::string_view name, SourceLoc loc, DiagEngine& diag) {
  diag.Error(loc,
             std::format("'{}' names a variable or a net, and a call names a "
                         "task or a function",
                         name),
             Subclause("A.8.2"));
}

void ReportIfData(std::string_view name, SourceLoc loc, const DataScope& scope,
                  DiagEngine& diag) {
  if (scope.Names(name)) ReportDataCall(name, loc, diag);
}

const Expr* NamedCallee(const Expr& expr) {
  const bool kNamed = expr.kind == ExprKind::kCall && expr.lhs != nullptr &&
                      expr.text != "new" &&
                      expr.lhs->kind == ExprKind::kIdentifier;
  return kNamed ? expr.lhs : nullptr;
}

const Expr* StatementCallExpr(const Expr* e) {
  if (e->kind == ExprKind::kCast && (e->lhs->kind == ExprKind::kIdentifier ||
                                     e->lhs->kind == ExprKind::kMemberAccess)) {
    return e->lhs;
  }
  return e;
}

void ReportStatementCall(const Stmt& stmt, const DataScope& scope,
                         DiagEngine& diag) {
  const Expr* e = StatementCallExpr(stmt.expr);
  const bool kBare = e->kind == ExprKind::kIdentifier;
  const Expr* callee = kBare ? e : NamedCallee(*e);
  if (callee == nullptr) return;
  const std::string_view kName = callee->text;
  if (scope.Names(kName)) {
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

std::string_view VifInterface(const DataType& type) {
  return type.kind == DataTypeKind::kVirtualInterface ? type.type_name
                                                      : std::string_view();
}

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

const DeclaredVar* RootVar(const Expr& root, const DataScope& scope) {
  if (root.kind == ExprKind::kIdentifier) return scope.Declared(root.text);
  const bool kThis =
      root.kind == ExprKind::kMemberAccess && !root.is_scope_resolution &&
      root.lhs->kind == ExprKind::kIdentifier && root.lhs->text == "this";
  return kThis ? scope.Property(root.rhs->text) : nullptr;
}

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

const DeclaredVar* OwnProperty(const Expr& root, const DataScope& scope) {
  if (root.kind != ExprKind::kIdentifier) return RootVar(root, scope);
  const DeclaredVar* property = scope.Property(root.text);
  return property != nullptr && scope.Declared(root.text) == property ? property
                                                                      : nullptr;
}

DeclaredVar SelectedProperty(const Expr& root, const DataScope& scope) {
  if (const DeclaredVar* own = OwnProperty(root, scope)) return *own;
  const ClassMember* held = HandleProperty(root, scope);
  return held == nullptr
             ? DeclaredVar{}
             : DeclaredVar{&held->data_type, held->unpacked_dims.size()};
}

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
  for (std::string_view name : subroutines) scope.uncallable.erase(name);
  subroutines.insert("randomize");
}

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

struct AttachedNames {
  std::unordered_set<std::string_view> locals;
  std::unordered_set<std::string_view> formals;
};

void CheckAttachedItems(const std::vector<SeqMatchAssign>& items,
                        const AttachedNames& names, const DataScope& scope,
                        DiagEngine& diag) {
  for (const SeqMatchAssign& item : items) {
    const Expr* callee =
        item.call == nullptr ? nullptr : NamedCallee(*item.call);
    if (callee == nullptr || names.formals.contains(callee->text)) continue;
    if (names.locals.contains(callee->text)) {
      ReportDataCall(callee->text, item.call->range.start, diag);
    } else {
      ReportIfData(callee->text, item.call->range.start, scope, diag);
    }
  }
}

void CheckAttachedCalls(const SeqLinearBody& body, const AttachedNames& names,
                        const DataScope& scope, DiagEngine& diag) {
  ForEachBody(body, [&](const SeqLinearBody& nested) {
    for (const std::vector<SeqMatchAssign>& items : nested.match_items) {
      CheckAttachedItems(items, names, scope, diag);
    }
    CheckAttachedItems(nested.first_match_items, names, scope, diag);
  });
}

void CheckTreeAttachedCalls(const PropertyExprNode* node,
                            const AttachedNames& names, const DataScope& scope,
                            DiagEngine& diag) {
  ForEachTreeNode(node, [&](const PropertyExprNode& at) {
    if (at.sequence != nullptr) {
      CheckAttachedCalls(at.sequence->seq_linear, names, scope, diag);
    }
  });
}

void CheckDeclarationCalls(const ModuleItem& decl, const DataScope& scope,
                           DiagEngine& diag) {
  AttachedNames names;
  CollectBodyLocals(decl.seq_linear, names.locals);
  if (decl.prop_body_tree != nullptr) {
    CollectTreeLocals(decl.prop_body_tree, names.locals);
  }
  for (const SeqLocalDecl& local : decl.prop_locals) {
    names.locals.insert(local.name);
  }
  names.formals.insert(decl.prop_formals.begin(), decl.prop_formals.end());
  CheckAttachedCalls(decl.seq_linear, names, scope, diag);
  CheckTreeAttachedCalls(decl.prop_body_tree, names, scope, diag);
}

void CheckAssertionCalls(const Stmt& stmt, const DataScope& scope,
                         DiagEngine& diag) {
  const AttachedNames kNone;
  CheckTreeAttachedCalls(stmt.assert_property, kNone, scope, diag);
  if (stmt.assert_sequence != nullptr) {
    CheckAttachedCalls(stmt.assert_sequence->seq_linear, kNone, scope, diag);
  }
}

void CheckItemCalls(const std::vector<ModuleItem*>& items, DataScope& scope,
                    DiagEngine& diag);

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
    } else if (item->kind == ModuleItemKind::kSequenceDecl ||
               item->kind == ModuleItemKind::kPropertyDecl) {
      CheckDeclarationCalls(*item, scope, diag);
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
  ForEachConcurrentAssertion(&decl, [&](const Stmt* stmt) {
    CheckAssertionCalls(*stmt, scope, diag);
  });
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
