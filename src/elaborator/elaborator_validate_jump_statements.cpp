#include <format>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/return_value_fit.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

struct JumpScope {
  int loop_depth = 0;
  int fork_depth = 0;
  bool in_subroutine = false;
  bool in_production_code_block = false;
};

void CheckJumpRules(const Stmt* s, const JumpScope& scope, DiagEngine& diag);

void CheckBreakScope(const Stmt* s, const JumpScope& scope, DiagEngine& diag) {
  if (scope.loop_depth > 0 || scope.in_production_code_block) return;
  if (scope.fork_depth > 0) {
    diag.Error(s->range.start,
               "break inside fork-join cannot exit a loop outside the "
               "fork-join block",
               Subclause("12.8"));
    return;
  }
  diag.Error(s->range.start, "break statement is not inside a loop",
             Subclause("12.8"));
}

void CheckContinueScope(const Stmt* s, const JumpScope& scope,
                        DiagEngine& diag) {
  if (scope.loop_depth > 0) return;
  if (scope.fork_depth > 0) {
    diag.Error(s->range.start,
               "continue inside fork-join cannot affect a loop outside "
               "the fork-join block",
               Subclause("12.8"));
    return;
  }
  diag.Error(s->range.start, "continue statement is not inside a loop",
             Subclause("12.8"));
}

bool CheckJumpLeaf(const Stmt* s, const JumpScope& scope, DiagEngine& diag) {
  switch (s->kind) {
    case StmtKind::kBreak:
      CheckBreakScope(s, scope, diag);
      return true;
    case StmtKind::kContinue:
      CheckContinueScope(s, scope, diag);
      return true;
    case StmtKind::kReturn:
      if (!scope.in_subroutine && !scope.in_production_code_block) {
        diag.Error(s->range.start,
                   "return statement is only allowed inside a subroutine",
                   Subclause("12.8"));
      }
      return true;
    default:
      return false;
  }
}

bool IsLoopStmtKind(StmtKind k) {
  return k == StmtKind::kFor || k == StmtKind::kForeach ||
         k == StmtKind::kWhile || k == StmtKind::kForever ||
         k == StmtKind::kRepeat || k == StmtKind::kDoWhile;
}

void CheckJumpRulesChildren(const Stmt* s, const JumpScope& scope,
                            DiagEngine& diag) {
  ForEachChildStmt(s,
                   [&](Stmt* const& sub) { CheckJumpRules(sub, scope, diag); });
}

void CheckJumpRules(const Stmt* s, const JumpScope& scope, DiagEngine& diag) {
  if (!s) return;

  if (CheckJumpLeaf(s, scope, diag)) return;

  if (IsLoopStmtKind(s->kind)) {
    JumpScope inner = scope;
    inner.loop_depth = scope.loop_depth + 1;
    CheckJumpRules(s->body, inner, diag);
    CheckJumpRules(s->for_body, inner, diag);
    for (auto* init : s->for_inits) CheckJumpRules(init, scope, diag);
    for (auto* step : s->for_steps) CheckJumpRules(step, scope, diag);
    return;
  }

  if (s->kind == StmtKind::kFork) {
    JumpScope inner = scope;
    inner.loop_depth = 0;
    inner.fork_depth = scope.fork_depth + 1;
    for (auto* sub : s->fork_stmts) CheckJumpRules(sub, inner, diag);
    return;
  }

  if (s->kind == StmtKind::kRandsequence) {
    JumpScope production = scope;
    production.in_production_code_block = true;
    CheckJumpRulesChildren(s, production, diag);
    return;
  }

  CheckJumpRulesChildren(s, scope, diag);
}

void CheckValueReturningFuncReturn(const Stmt* s, std::string_view func_name,
                                   const CheckedType& ret, const ReturnCtx& ctx,
                                   DiagEngine& diag) {
  if (!s) return;
  if (s->kind == StmtKind::kReturn) {
    if (s->expr == nullptr) {
      diag.Error(s->range.start,
                 std::format("return statement in non-void function '{}' "
                             "gives no value to return",
                             func_name),
                 Subclause("12.8"));
      return;
    }
    if (!ReturnValueFits(ret, CheckedTypeOfValue(s->expr, ctx), ctx.unit)) {
      diag.Error(s->range.start,
                 std::format("return expression in function '{}' is not "
                             "assignment-compatible with the function's "
                             "return type",
                             func_name),
                 Subclause("12.8"));
    }
    return;
  }
  if (s->kind == StmtKind::kRandsequence) return;

  ForEachChildInScope(s, ctx, [&](const Stmt* sub, const ReturnCtx& inner) {
    CheckValueReturningFuncReturn(sub, func_name, ret, inner, diag);
  });
}

void CheckSubroutineJumpRules(const ModuleItem* item, const ReturnCtx& outer,
                              bool enum_check_reads_outer, DiagEngine& diag) {
  bool is_value_returning = false;
  if (item->kind == ModuleItemKind::kFunctionDecl) {
    is_value_returning =
        item->name != "new" && item->return_type.kind != DataTypeKind::kVoid;
  }
  JumpScope scope;
  scope.in_subroutine = true;
  for (auto* s : item->func_body_stmts) CheckJumpRules(s, scope, diag);
  if (!is_value_returning) return;
  const CheckedType kRet = CheckedTypeOf(item->return_type, outer);
  const bool kOuterLeftToEnumCheck =
      enum_check_reads_outer && kRet.type.kind == DataTypeKind::kEnum;
  const ReturnCtx kCtx{
      outer.typedefs, outer.unit,
      SubroutineLocals(
          item, kOuterLeftToEnumCheck ? DeclaredLocals{} : outer.locals)};
  for (auto* s : item->func_body_stmts) {
    CheckValueReturningFuncReturn(s, item->name, kRet, kCtx, diag);
  }
}

}  // namespace

void Elaborator::ValidateJumpStatements(const ModuleDecl* decl) {
  CheckJumpStatementsIn(decl->items);
}

void Elaborator::CheckJumpStatementsIn(const std::vector<ModuleItem*>& items) {
  SubroutineScopes scopes(items, typedefs_, *unit_);
  ForEachBodyOwningItem(items, [&](const ModuleItem* item) {
    if (IsProceduralItemKind(item->kind) && item->body) {
      CheckJumpRules(item->body, JumpScope{}, diag_);
      return;
    }
    if (item->kind == ModuleItemKind::kFunctionDecl ||
        item->kind == ModuleItemKind::kTaskDecl) {
      CheckSubroutineJumpRules(item, scopes.Around(item),
                               !scopes.IsMethod(item), diag_);
    }
  });
}

}  // namespace delta
