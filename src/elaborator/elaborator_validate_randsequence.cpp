#include <format>
#include <functional>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/aggregate_shape.h"
#include "elaborator/covergroup_variables.h"
#include "elaborator/declared_types.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_scope_rules_names.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/implication_operator_rules.h"
#include "elaborator/net_data_type.h"
#include "elaborator/nettype_uses.h"
#include "elaborator/return_value_fit.h"
#include "elaborator/virtual_interface_target.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "parser/override_specifier_placement.h"

namespace delta {

namespace {

NameSet DeclaredProductions(const Stmt* s) {
  NameSet declared;
  for (const auto& production : s->rs_productions) {
    declared.insert(production.name);
  }
  return declared;
}

void CheckProductionItem(const RsProductionItem& item, const NameSet& declared,
                         DiagEngine& diag) {
  if (item.name.empty()) return;
  if (declared.count(item.name) != 0) return;
  diag.Error(item.loc,
             std::format("randsequence production item names '{}', which is "
                         "not one of the productions this randsequence "
                         "statement declares",
                         item.name),
             Subclause("18.17"));
}

void CheckReturnValue(const Stmt* s, const RsProduction& production,
                      const CheckedType& ret, const ReturnCtx& ctx,
                      DiagEngine& diag) {
  if (s->expr == nullptr) {
    diag.Error(s->range.start,
               std::format("return in production '{}', which returns a value, "
                           "gives no value to return",
                           production.name),
               Subclause("18.17.7"));
    return;
  }
  if (ReturnValueFits(ret, CheckedTypeOfValue(s->expr, ctx), ctx.unit)) return;
  diag.Error(s->range.start,
             std::format("return expression in production '{}' is not "
                         "assignment-compatible with the production's return "
                         "type",
                         production.name),
             Subclause("18.17.7"));
}

void CheckProductionReturns(const Stmt* s, const RsProduction& production,
                            const CheckedType& ret, const ReturnCtx& ctx,
                            DiagEngine& diag) {
  if (s == nullptr || s->kind == StmtKind::kRandsequence) return;
  if (s->kind == StmtKind::kReturn) {
    CheckReturnValue(s, production, ret, ctx, diag);
    return;
  }
  ForEachChildInScope(s, ctx, [&](const Stmt* sub, const ReturnCtx& inner) {
    CheckProductionReturns(sub, production, ret, inner, diag);
  });
}

DeclaredLocals CodeBlockLocals(const RsProduction& production,
                               const std::vector<Stmt*>& block,
                               const DeclaredLocals& outer) {
  DeclaredLocals locals = outer;
  for (const auto& port : production.ports)
    locals[port.name] = {&port.data_type, &port.unpacked_dims};
  EnterDeclaredLocals(block, locals);
  return locals;
}

void CheckRandsequenceNames(const Stmt* s, const ReturnCtx& outer,
                            DiagEngine& diag);

bool ReturnsAValue(const RsProduction& production) {
  return production.has_return_type &&
         production.return_type.kind != DataTypeKind::kVoid;
}

void CheckCodeBlock(const std::vector<Stmt*>& block,
                    const RsProduction& production, const ReturnCtx& outer,
                    DiagEngine& diag) {
  const ReturnCtx kCtx{outer.typedefs, outer.unit,
                       CodeBlockLocals(production, block, outer.locals)};
  for (const Stmt* s : block) CheckRandsequenceNames(s, kCtx, diag);
  if (!ReturnsAValue(production)) return;
  const CheckedType kRet = CheckedTypeOf(production.return_type, kCtx);
  for (const Stmt* s : block)
    CheckProductionReturns(s, production, kRet, kCtx, diag);
}

void CheckRuleCodeBlocks(const RsRule& rule, const RsProduction& production,
                         const ReturnCtx& outer, DiagEngine& diag) {
  for (const RsProd& prod : rule.prods)
    CheckCodeBlock(prod.code_stmts, production, outer, diag);
  CheckCodeBlock(rule.weight_code, production, outer, diag);
}

void CheckCodeBlocks(const Stmt* s, const ReturnCtx& outer, DiagEngine& diag) {
  for (const RsProduction& production : s->rs_productions) {
    for (const RsRule& rule : production.rules)
      CheckRuleCodeBlocks(rule, production, outer, diag);
  }
}

void CheckRandsequence(const Stmt* s, const ReturnCtx& outer,
                       DiagEngine& diag) {
  NameSet declared = DeclaredProductions(s);
  if (!s->rs_top_production.empty() &&
      declared.count(s->rs_top_production) == 0) {
    diag.Error(s->range.start,
               std::format("randsequence names '{}' as its top-level "
                           "production, which is not one of the productions it "
                           "declares",
                           s->rs_top_production),
               Subclause("18.17"));
  }
  ForEachRandsequenceItem(s, [&](const RsProductionItem& item) {
    CheckProductionItem(item, declared, diag);
  });
  CheckCodeBlocks(s, outer, diag);
}

void CheckRandsequenceNames(const Stmt* s, const ReturnCtx& outer,
                            DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kRandsequence) {
    CheckRandsequence(s, outer, diag);
    return;
  }
  ForEachChildInScope(s, outer, [&](const Stmt* sub, const ReturnCtx& inner) {
    CheckRandsequenceNames(sub, inner, diag);
  });
}

std::function<bool(std::string_view)> UnitCovergroups(
    const CompilationUnit* unit) {
  return [unit](std::string_view name) {
    return UnitDeclaresCovergroup(unit, name);
  };
}

}  // namespace

void Elaborator::ValidateRandsequenceProductionNames(const ModuleDecl* decl) {
  CheckRandsequenceNamesIn(decl->items);
}

void Elaborator::CheckRandsequenceNamesIn(
    const std::vector<ModuleItem*>& items) {
  SubroutineScopes scopes(items, typedefs_, *unit_);
  ForEachBodyOwningItem(items, [&](const ModuleItem* item) {
    const ReturnCtx kAround = scopes.Around(item);
    if (IsProceduralItemKind(item->kind)) {
      CheckRandsequenceNames(item->body, kAround, diag_);
      return;
    }
    if (item->kind == ModuleItemKind::kFunctionDecl ||
        item->kind == ModuleItemKind::kTaskDecl) {
      const ReturnCtx kBody{kAround.typedefs, kAround.unit,
                            SubroutineLocals(item, kAround.locals)};
      for (const auto* s : item->func_body_stmts) {
        CheckRandsequenceNames(s, kBody, diag_);
      }
    }
  });
}

void Elaborator::ValidatePerDeclarationRulesInUnitScopes() {
  if (unit_ == nullptr) return;
  ValidateUnitScopeTypeRefArgs();
  ElaborateUnitScopeProcedures();

  auto elaborate_let = [this](ModuleItem* let) {
    ElaborateLetFormals(let, nullptr);
  };
  auto run_over = [this,
                   &elaborate_let](const std::vector<ModuleItem*>& items) {
    ForEachScopeLet(items, elaborate_let);
    CheckJumpStatementsIn(items);
    CheckRandsequenceNamesIn(items);
    CheckForeachLoopsIn(items);
    CheckPatternsIn(items);
    for (const ModuleItem* item : items) {
      ReportItemImplicationOperators(*item, diag_);
      if (item->kind == ModuleItemKind::kFunctionDecl ||
          item->kind == ModuleItemKind::kTaskDecl) {
        ReportMisplacedOverrideSpecifiers(*item, diag_);
      }
    }
  };

  run_over(unit_->cu_items);
  CheckUnitLetActualTypes();
  for (const auto* pkg : unit_->packages) {
    if (pkg != nullptr) run_over(pkg->items);
  }
  CheckUnitNettypeUses(unit_, nettype_names_, diag_);
  ForEachUnitDeclaredType(unit_, [this](const DeclaredType& declared) {
    CheckDeclaredTypeRules(
        declared,
        AggregateShapeCtx{
            TypeShapeTables{typedefs_, td_array_dims_, class_names_}, nullptr,
            diag_},
        UnitCovergroups(unit_));
    ValidateVirtualInterfaceType(
        declared.type, declared.loc,
        [this](std::string_view name) { return FindModule(name); }, diag_);
  });
  const UnitScopeNames kNames{cu_scope_names_, cu_param_scope_, typedefs_,
                              class_names_};
  if (units_.views.empty()) {
    ReportUnresolvedInUnitSubroutines(unit_, kNames, pkg_provided_names_,
                                      diag_);
  }
  ReportUnresolvedInPackageSubroutines(unit_, kNames, pkg_provided_names_,
                                       diag_);
  for (const auto* cls : unit_->classes) {
    std::vector<ModuleItem*> methods;
    ForEachClassBodyItem(cls, [&](const ModuleItem* m) {
      methods.push_back(const_cast<ModuleItem*>(m));
    });
    ForEachScopeLet(methods, elaborate_let);
    CheckJumpStatementsIn(methods);
    CheckRandsequenceNamesIn(methods);
    CheckForeachLoopsInClass(cls);
    CheckPatternsInClass(cls);
    ReportClassImplicationOperators(cls, diag_);
  }
}

}  // namespace delta
