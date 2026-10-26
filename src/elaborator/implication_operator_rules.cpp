#include "elaborator/implication_operator_rules.h"

#include <format>
#include <vector>

#include "common/diagnostic.h"
#include "elaborator/elaborator_validate_internal.h"
#include "lexer/token.h"
#include "parser/ast_class.h"
#include "parser/ast_covergroup.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

// Whether the statement `stmt` holds a property in its own expressions rather
// than ordinary ones: a concurrent assertion or an expect statement in
// procedural code, which the parser marks is_procedural_concurrent, or the
// statement it builds for a static concurrent assertion's clocked boolean
// form, which it marks is_concurrent_clocked.
bool HoldsProperty(const Stmt& stmt) {
  return stmt.is_procedural_concurrent || stmt.is_concurrent_clocked;
}

void ReportStmtImplicationOperators(const Stmt* stmt, DiagEngine& diag) {
  if (stmt == nullptr) return;
  // A let, typedef, nettype or import among a block's items is carried over
  // the item its declaration makes; a let's body is an expression.
  if (stmt->kind == StmtKind::kBlockItemDecl) {
    ReportItemImplicationOperators(*stmt->decl_item, diag);
  }
  if (!HoldsProperty(*stmt)) {
    ForEachChildExpr(stmt, [&diag](const Expr* expr) {
      ReportImplicationOperators(expr, diag);
    });
  }
  ForEachChildStmt(stmt, [&diag](const Stmt* sub) {
    ReportStmtImplicationOperators(sub, diag);
  });
}

// A generate construct's header (A.4.2): an if-generate's condition and the
// else-if that follows it, a case-generate's selector and item values, and a
// loop-generate's initialization, condition and iteration. Each is held in the
// fields of its kind, and the others are empty.
void ReportGenerateImplicationOperators(const ModuleItem& item,
                                        DiagEngine& diag) {
  ReportImplicationOperators(item.gen_cond, diag);
  ReportStmtImplicationOperators(item.gen_init, diag);
  ReportStmtImplicationOperators(item.gen_step, diag);
  for (const GenerateCaseItem& case_item : item.gen_case_items) {
    for (const Expr* pattern : case_item.patterns) {
      ReportImplicationOperators(pattern, diag);
    }
  }
  if (item.gen_else != nullptr) {
    ReportItemImplicationOperators(*item.gen_else, diag);
  }
}

// The values of a covergroup_range_list (A.2.11).
void ReportRangesImplicationOperators(
    const std::vector<CovergroupValueRange>& ranges, DiagEngine& diag) {
  for (const CovergroupValueRange& range : ranges) {
    ReportImplicationOperators(range.lo, diag);
    ReportImplicationOperators(range.hi, diag);
  }
}

// A bin's or a coverpoint option's expressions (A.2.11): an option's value, a
// bin's array size, its values, its `with` filter, its set expression, each
// transition step's values and repeat range, and its guard.
void ReportBinsImplicationOperators(const BinsOrOptions& bins,
                                    DiagEngine& diag) {
  ReportImplicationOperators(bins.option.value, diag);
  ReportImplicationOperators(bins.array_size, diag);
  ReportRangesImplicationOperators(bins.ranges, diag);
  ReportImplicationOperators(bins.with_expr, diag);
  ReportImplicationOperators(bins.set_expr, diag);
  for (const TransSet& set : bins.transitions) {
    for (const TransRangeList& step : set.steps) {
      ReportRangesImplicationOperators(step.items, diag);
      ReportImplicationOperators(step.repeat_lo, diag);
      ReportImplicationOperators(step.repeat_hi, diag);
    }
  }
  ReportImplicationOperators(bins.iff, diag);
}

// A select expression's intersect values, `with` filter or cross set
// expression, and matches count, and those of its operands (A.2.11).
void ReportSelectImplicationOperators(const SelectExpression* select,
                                      DiagEngine& diag) {
  if (select == nullptr) return;
  ReportRangesImplicationOperators(select->intersect, diag);
  ReportImplicationOperators(select->expr, diag);
  ReportImplicationOperators(select->matches, diag);
  ReportSelectImplicationOperators(select->lhs, diag);
  ReportSelectImplicationOperators(select->rhs, diag);
}

// A cross's guard, and each of its options' values and bins selections'
// guards and select expressions (A.2.11).
void ReportCrossImplicationOperators(const CoverCrossDecl& cross,
                                     DiagEngine& diag) {
  ReportImplicationOperators(cross.iff, diag);
  for (const CrossBodyItem& item : cross.body) {
    ReportImplicationOperators(item.option.value, diag);
    ReportImplicationOperators(item.bins.iff, diag);
    ReportSelectImplicationOperators(item.bins.select, diag);
  }
}

// A covergroup's options, each coverpoint's expression, guard and bins, and
// each cross (A.2.11).
void ReportCovergroupImplicationOperators(const CovergroupDecl& covergroup,
                                          DiagEngine& diag) {
  for (const CoverageSpecOrOption& spec : covergroup.items) {
    ReportImplicationOperators(spec.option.value, diag);
    if (spec.cover_cross != nullptr) {
      ReportCrossImplicationOperators(*spec.cover_cross, diag);
    }
    if (spec.cover_point == nullptr) continue;
    ReportImplicationOperators(spec.cover_point->expr, diag);
    ReportImplicationOperators(spec.cover_point->iff, diag);
    for (const BinsOrOptions& bins : spec.cover_point->bins) {
      ReportBinsImplicationOperators(bins, diag);
    }
  }
}

// A class member's initializer and constraints, and its method's, nested
// class's or embedded covergroup's expressions. A constraint is built from
// expressions (A.1.10); the implication it does hold is `->`.
void ReportMemberImplicationOperators(const ClassMember& member,
                                      DiagEngine& diag) {
  ReportImplicationOperators(member.init_expr, diag);
  for (const Expr* expr : member.constraint_exprs) {
    ReportImplicationOperators(expr, diag);
  }
  for (const Expr* expr : member.constraint_soft_exprs) {
    ReportImplicationOperators(expr, diag);
  }
  if (member.method != nullptr) {
    ReportItemImplicationOperators(*member.method, diag);
  }
  ReportClassImplicationOperators(member.nested_class, diag);
  if (member.covergroup != nullptr) {
    ReportCovergroupImplicationOperators(*member.covergroup, diag);
  }
}

}  // namespace

void ReportImplicationOperators(const Expr* expr, DiagEngine& diag) {
  auto report = [&diag](const Expr* sub) {
    if (sub->kind != ExprKind::kBinary) return;
    if (sub->op != TokenKind::kPipeDashGt && sub->op != TokenKind::kPipeEqGt) {
      return;
    }
    // An item elaborated more than once, in each instance of its module or of
    // a loop generate block, is reported once.
    diag.ErrorOnce(
        sub->range.start,
        std::format(
            "the property operator '{}' joins the operands of an ordinary "
            "expression",
            sub->op == TokenKind::kPipeDashGt ? "|->" : "|=>"),
        Subclause("A.8.6"));
  };
  ForEachExprUnder(expr, report);
}

void ReportClassImplicationOperators(const ClassDecl* cls, DiagEngine& diag) {
  if (cls == nullptr) return;
  for (const auto& param : cls->params) {
    ReportImplicationOperators(param.second, diag);
  }
  for (const Expr* arg : cls->extends_args) {
    ReportImplicationOperators(arg, diag);
  }
  for (const ClassMember* member : cls->members) {
    ReportMemberImplicationOperators(*member, diag);
  }
}

void ReportItemImplicationOperators(const ModuleItem& item, DiagEngine& diag) {
  switch (item.kind) {
    case ModuleItemKind::kContAssign:
      ReportImplicationOperators(item.assign_lhs, diag);
      ReportImplicationOperators(item.assign_rhs, diag);
      break;
    case ModuleItemKind::kNetDecl:
    case ModuleItemKind::kVarDecl:
    case ModuleItemKind::kParamDecl:
    case ModuleItemKind::kLetDecl:
      ReportImplicationOperators(item.init_expr, diag);
      break;
    case ModuleItemKind::kClassDecl:
      ReportClassImplicationOperators(item.class_decl, diag);
      break;
    case ModuleItemKind::kModuleInst:
      // A.4.1.1: the parameter values written in the instantiation. A checker
      // instance takes none (A.4.1.4).
      for (const auto& param : item.inst_params) {
        ReportImplicationOperators(param.second, diag);
      }
      break;
    case ModuleItemKind::kGateInst:
    case ModuleItemKind::kUdpInst:
      // A.3.3 and A.5.4: a gate's or a primitive's terminals.
      for (const Expr* terminal : item.gate_terminals) {
        ReportImplicationOperators(terminal, diag);
      }
      break;
    case ModuleItemKind::kGenerateIf:
    case ModuleItemKind::kGenerateCase:
    case ModuleItemKind::kGenerateFor:
      ReportGenerateImplicationOperators(item, diag);
      break;
    case ModuleItemKind::kCovergroupDecl:
      ReportCovergroupImplicationOperators(*item.covergroup, diag);
      break;
    default:
      break;
  }
  // A subroutine's or a let's port defaults (A.2.7, A.2.12).
  for (const FunctionArg& arg : item.func_args) {
    ReportImplicationOperators(arg.default_value, diag);
  }
  ReportStmtImplicationOperators(item.body, diag);
  for (const Stmt* stmt : item.func_body_stmts) {
    ReportStmtImplicationOperators(stmt, diag);
  }
}

}  // namespace delta
