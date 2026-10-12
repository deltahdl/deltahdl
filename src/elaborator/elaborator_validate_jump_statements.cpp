// §12.8 "Jump statements" — the elaboration-time rules for break, continue and
// return, together with the one clause that gives two of them another meaning:
// §18.17.6 "Aborting productions—break and return". Split out of
// elaborator_validate_funcchecks.cpp, which keeps §12.7.3's foreach rules and
// §13.4.3's constant-function rules.

#include <format>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/elaborator.h"
#include "elaborator/elaborator_class_lookup.h"
#include "elaborator/elaborator_validate_classes_internal.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/type_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

// §18.17.6 lets break and return stand in any code block, the two differing in
// which scope they leave. This is that scope, as the two clauses that give a
// jump statement a meaning describe it: what encloses the statement being
// walked.
struct JumpScope {
  // §12.8 confines continue and break to a loop. Counts the enclosing loops a
  // jump reaches without crossing a fork-join boundary.
  int loop_depth = 0;
  // §12.8: a continue or break inside a fork-join block may not control a loop
  // outside it. Counts the enclosing fork-join blocks.
  int fork_depth = 0;
  // §12.8 confines return to a subroutine. True when the walk started in a
  // function or task body.
  bool in_subroutine = false;
  // §18.17.6: inside a randsequence production code block, break leaves the
  // randsequence block and return ends the generation of the current
  // production. Neither needs the enclosing loop or the enclosing subroutine
  // §12.8 asks for, so this term is what withholds those two reports. It stays
  // set through a fork-join written inside the code block: §12.8's fork
  // sentence is about controlling a loop outside the fork-join block, and the
  // randsequence block a break leaves is not a loop.
  bool in_production_code_block = false;
};

void CheckJumpRules(const Stmt* s, const JumpScope& scope, DiagEngine& diag);

// §12.8 — a break shall stand in a loop, and not in a fork-join block that
// the loop it breaks encloses. §18.17.6 gives it a randsequence block to leave
// instead where it stands in a production code block, so no loop is required
// there; where that code block writes a loop of its own, §12.8 binds the break
// to it, which is why `loop_depth` is still counted inside a production rather
// than reset.
//
// A break in a production code block whose only enclosing loop stands outside
// the randsequence block binds to the randsequence block and not to that loop.
// §18.17.6 states without qualification that a break executed in a production
// code block leaves the randsequence block, and the sentence about a loop
// statement that defers to §12.8 is about a loop the code block itself writes.
// Elaboration accepts the source on either reading, one clause finding a
// production and the other a loop, so what fixes the reading is this comment
// and
// JumpStatementElaboration.BreakInARandsequenceProductionCodeBlockInsideAnOuterLoopOk
// in test/src/unit/test_elaborator_subclause_12_08a.cpp; the randsequence
// executor is where the difference is observable.
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

// §12.8 — the same two rules for continue, with no §18.17.6 term: that clause
// names break and return and says nothing of continue, so a continue in a
// production code block still has to stand in a loop.
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

// Returns true when `s` is itself a jump leaf (break/continue/return) and
// reports any §12.8 violation for it. Caller stops descending on true.
bool CheckJumpLeaf(const Stmt* s, const JumpScope& scope, DiagEngine& diag) {
  switch (s->kind) {
    case StmtKind::kBreak:
      CheckBreakScope(s, scope, diag);
      return true;
    case StmtKind::kContinue:
      CheckContinueScope(s, scope, diag);
      return true;
    case StmtKind::kReturn:
      // §18.17.6: a return in a production code block aborts the production
      // rather than a subroutine, so §12.8's subroutine requirement is not
      // what governs it.
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

// Recurses into every child statement of `s` carrying `scope` unchanged.
//
// The links come from ForEachChildStmt in elaborator_validate_internal.h,
// which is the one list of the thirteen fields of Stmt that hold a
// statement. This walk may take all thirteen from it even though four of them
// stand in a scope of their own, because CheckJumpRules answers every
// statement kind that fills those four before reaching here. Stmt::for_inits,
// Stmt::for_steps and Stmt::for_body are filled by Parser::ParseForStmt in
// src/parser/parser_stmt.cpp alone, Stmt::fork_stmts by Parser::ParseForkStmt
// in src/parser/parser_stmt_block.cpp alone, and Stmt::rs_productions by
// Parser::ParseRandsequenceStmt in src/parser/parser_verify.cpp alone. All
// five are therefore empty at every statement that reaches this function, and
// visiting them here changes nothing.
//
// Stmt::body is the one link that is not empty here. The five loop statements
// of §12.7 other than for fill it and are answered above, but
// Parser::ParseDelayStmt, Parser::ParseCycleDelayStmt,
// Parser::ParseEventControlStmt and Parser::ParseWaitStmt fill it too, and
// none of those four is a loop. §12.8 confines continue and break to a loop
// without qualifying it by what a statement is waiting for, so
// `initial #5 break;` is a break outside a loop and is reported as one.
void CheckJumpRulesChildren(const Stmt* s, const JumpScope& scope,
                            DiagEngine& diag) {
  ForEachChildStmt(s,
                   [&](Stmt* const& sub) { CheckJumpRules(sub, scope, diag); });
}

// Walks one statement subtree enforcing §12.8's rules for break, continue and
// return, and §18.17.6's exemption from two of them.
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

  // §18.17.6 gives break and return a meaning in a randsequence production
  // code block that they have nowhere else, so the statements a randsequence
  // statement holds are walked with that term set.
  // Parser::ParseRandsequenceStmt in src/parser/parser_verify.cpp fills
  // Stmt::rs_productions and no other child-statement link, so handing the
  // whole of ForEachChildStmt the production scope reaches those statements and
  // nothing besides. A.6.12 keeps them in two lists: an rs_prod may be an
  // rs_code_block, whose statements the parser puts in RsProd::code_stmts, and
  // an rs_rule admits a second rs_code_block after a weight_specification,
  // whose statements go in RsRule::weight_code.
  if (s->kind == StmtKind::kRandsequence) {
    JumpScope production = scope;
    production.in_production_code_block = true;
    CheckJumpRulesChildren(s, production, diag);
    return;
  }

  CheckJumpRulesChildren(s, scope, diag);
}

// Map literal expression kinds whose type is obvious from the syntax alone
// to the corresponding DataTypeKind. Returns kImplicit when no narrow
// classification is possible without full expression type inference. §5.9
// makes a string literal in an assignment an unsigned integer constant, eight
// bits a character, so it maps to a bit vector.
DataTypeKind ObviousLiteralKind(const Expr* e) {
  if (!e) return DataTypeKind::kImplicit;
  switch (e->kind) {
    case ExprKind::kStringLiteral:
      return DataTypeKind::kBit;
    case ExprKind::kRealLiteral:
      return DataTypeKind::kReal;
    case ExprKind::kIntegerLiteral:
      return DataTypeKind::kInt;
    case ExprKind::kTimeLiteral:
      return DataTypeKind::kTime;
    default:
      return DataTypeKind::kImplicit;
  }
}

// What §12.8's return check reads besides the return statement: the typedefs
// and classes a type name may stand for, and the declared type of each name
// the subroutine declares, its formals and the variables its body declares,
// which no name outside the subroutine hides.
struct ReturnCtx {
  const TypedefMap& typedefs;
  const CompilationUnit* unit;
  std::unordered_map<std::string_view, const DataType*> locals;
};

// The type a return compares, as far as the check can see it: a class, or a
// type IsAssignmentCompatible answers for, or neither where the type is not
// one the check reads (`type.kind` is kImplicit and `cls` null).
struct CheckedType {
  DataType type;
  const ClassDecl* cls = nullptr;
  bool is_string_literal = false;
};

// The type `declared` stands for, followed through typedef names to the type
// it was declared with. A name the typedefs do not hold is a class or a type
// the check does not read.
CheckedType CheckedTypeOf(const DataType& declared, const ReturnCtx& ctx) {
  const DataType& t = LastTypeInChain(declared, ctx.typedefs);
  CheckedType out;
  if (t.kind != DataTypeKind::kNamed) {
    out.type = t;
  } else if (ctx.unit != nullptr) {
    out.cls = ClassOfDeclaredType(t, {}, ctx.unit);
  }
  return out;
}

// §6.22.3: the type of a return expression as far as it is plain from the
// source: a literal's, or the declared type of a variable or formal of the
// subroutine named whole. A variable of an unpacked array type, a member, a
// select, a call or an operation is not read.
CheckedType CheckedTypeOfValue(const Expr* e, const ReturnCtx& ctx) {
  if (e->kind == ExprKind::kIdentifier) {
    auto it = ctx.locals.find(e->text);
    return it == ctx.locals.end() ? CheckedType{}
                                  : CheckedTypeOf(*it->second, ctx);
  }
  CheckedType out;
  out.type.kind = ObviousLiteralKind(e);
  out.is_string_literal = e->kind == ExprKind::kStringLiteral;
  return out;
}

// §6.22.3 with §8.4: whether a value of `value` may be returned where `ret` is
// the return type. A class handle fits a class it is or derives from (§8.13)
// and no other type, and no other value fits a class; two other types fit as
// IsAssignmentCompatible says of the value's type assigned to the return
// type, but for a string literal, which a string takes as it is (§6.16). A
// type the check does not read fits anything.
bool ReturnValueFits(const CheckedType& ret, const CheckedType& value,
                     const CompilationUnit* unit) {
  if (value.is_string_literal && ret.type.kind == DataTypeKind::kString)
    return true;
  bool ret_read = ret.type.kind != DataTypeKind::kImplicit;
  bool value_read = value.type.kind != DataTypeKind::kImplicit;
  if (ret.cls != nullptr) {
    if (value.cls == nullptr) return !value_read;
    return value.cls == ret.cls ||
           IsClassDeclDerivedFrom(value.cls, ret.cls->name, unit);
  }
  if (value.cls != nullptr) return !ret_read;
  return !ret_read || !value_read ||
         IsAssignmentCompatible(value.type, ret.type);
}

// §12.8: a return in a function that yields a value needs an expression, and
// one whose type fits the function. The void-with-expression case is
// reported elsewhere.
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
  // §18.17.6 makes a return written in a randsequence production code block
  // abort the generation of the current production rather than return from the
  // enclosing function: return ends the generation of the current production.
  // It is therefore not the function's return, and neither §12.8's demand that
  // a return in a value-returning function carry an expression of the right
  // type nor §13.4.1's that a nonvoid function's return carry an expression is
  // about it. Stopping at the randsequence statement excludes exactly those
  // statements: Parser::ParseRandsequenceStmt in src/parser/parser_verify.cpp
  // fills Stmt::rs_productions and no other child-statement link, so nothing
  // else is left unreached by stopping here.
  if (s->kind == StmtKind::kRandsequence) return;

  // Every other link comes from ForEachChildStmt in
  // elaborator_validate_internal.h, which is the one list of the fields of Stmt
  // that hold a statement.
  ForEachChildStmt(s, [&](Stmt* const& sub) {
    CheckValueReturningFuncReturn(sub, func_name, ret, ctx, diag);
  });
}

// The names subroutine `item` declares with a type the return check reads
// whole: its formals and the variables its body declares at its top level, each
// written with no unpacked dimension.
std::unordered_map<std::string_view, const DataType*> SubroutineLocals(
    const ModuleItem* item) {
  std::unordered_map<std::string_view, const DataType*> locals;
  for (const auto& arg : item->func_args) {
    if (arg.unpacked_dims.empty()) locals[arg.name] = &arg.data_type;
  }
  for (const Stmt* s : item->func_body_stmts) {
    if (s->kind == StmtKind::kVarDecl && s->var_unpacked_dims.empty())
      locals[s->var_name] = &s->var_decl_type;
  }
  return locals;
}

// §12.8 — applies the jump rules to a function/task body and, for a
// value-returning function, also checks each return statement's expression.
void CheckSubroutineJumpRules(const ModuleItem* item,
                              const TypedefMap& typedefs,
                              const CompilationUnit* unit, DiagEngine& diag) {
  bool is_value_returning = false;
  if (item->kind == ModuleItemKind::kFunctionDecl) {
    // §8.7: a class constructor has no return type, so a `return;` in one is
    // the whole of what a return there can be. It reaches this walk as an
    // ordinary kFunctionDecl whose return_type was never written, which is not
    // kVoid either, so without this a constructor's return would be reported
    // for lacking an expression it may not have.
    is_value_returning =
        item->name != "new" && item->return_type.kind != DataTypeKind::kVoid;
  }
  JumpScope scope;
  scope.in_subroutine = true;
  for (auto* s : item->func_body_stmts) CheckJumpRules(s, scope, diag);
  if (!is_value_returning) return;
  const ReturnCtx kCtx{typedefs, unit, SubroutineLocals(item)};
  const CheckedType kRet = CheckedTypeOf(item->return_type, kCtx);
  for (auto* s : item->func_body_stmts) {
    CheckValueReturningFuncReturn(s, item->name, kRet, kCtx, diag);
  }
}

}  // namespace

void Elaborator::ValidateJumpStatements(const ModuleDecl* decl) {
  CheckJumpStatementsIn(decl->items);
}

// §12.8 names no enclosing declaration the rule is suspended in, so every body
// a declaration owns is walked -- ForEachBodyOwningItem in
// elaborator_validate_internal.h is the one list of those.
void Elaborator::CheckJumpStatementsIn(const std::vector<ModuleItem*>& items) {
  ForEachBodyOwningItem(items, [this](const ModuleItem* item) {
    if (IsProceduralItemKind(item->kind) && item->body) {
      CheckJumpRules(item->body, JumpScope{}, diag_);
      return;
    }
    if (item->kind == ModuleItemKind::kFunctionDecl ||
        item->kind == ModuleItemKind::kTaskDecl) {
      CheckSubroutineJumpRules(item, typedefs_, unit_, diag_);
    }
  });
}

}  // namespace delta
