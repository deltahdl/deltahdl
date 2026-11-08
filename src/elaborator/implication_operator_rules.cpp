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

bool HoldsProperty(const Stmt& stmt) {
  return stmt.is_procedural_concurrent || stmt.is_concurrent_clocked;
}

void ReportStmtImplicationOperators(const Stmt* stmt, DiagEngine& diag) {
  if (stmt == nullptr) return;
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

void ReportRangesImplicationOperators(
    const std::vector<CovergroupValueRange>& ranges, DiagEngine& diag) {
  for (const CovergroupValueRange& range : ranges) {
    ReportImplicationOperators(range.lo, diag);
    ReportImplicationOperators(range.hi, diag);
  }
}

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

void ReportSelectImplicationOperators(const SelectExpression* select,
                                      DiagEngine& diag) {
  if (select == nullptr) return;
  ReportRangesImplicationOperators(select->intersect, diag);
  ReportImplicationOperators(select->expr, diag);
  ReportImplicationOperators(select->matches, diag);
  ReportSelectImplicationOperators(select->lhs, diag);
  ReportSelectImplicationOperators(select->rhs, diag);
}

void ReportCrossImplicationOperators(const CoverCrossDecl& cross,
                                     DiagEngine& diag) {
  ReportImplicationOperators(cross.iff, diag);
  for (const CrossBodyItem& item : cross.body) {
    ReportImplicationOperators(item.option.value, diag);
    ReportImplicationOperators(item.bins.iff, diag);
    ReportSelectImplicationOperators(item.bins.select, diag);
    if (item.function != nullptr) {
      ReportItemImplicationOperators(*item.function, diag);
    }
  }
}

void ReportPortDefaultImplicationOperators(const std::vector<FunctionArg>& args,
                                           DiagEngine& diag) {
  for (const FunctionArg& arg : args) {
    ReportImplicationOperators(arg.default_value, diag);
  }
}

void ReportCovergroupImplicationOperators(const CovergroupDecl& covergroup,
                                          DiagEngine& diag) {
  ReportPortDefaultImplicationOperators(covergroup.formals, diag);
  ReportPortDefaultImplicationOperators(covergroup.event.sample_formals, diag);
  for (const EventExpr& event : covergroup.event.clocking) {
    ReportImplicationOperators(event.signal, diag);
    ReportImplicationOperators(event.iff_condition, diag);
  }
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
      for (const auto& param : item.inst_params) {
        ReportImplicationOperators(param.second, diag);
      }
      break;
    case ModuleItemKind::kGateInst:
    case ModuleItemKind::kUdpInst:
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
  ReportPortDefaultImplicationOperators(item.func_args, diag);
  ReportStmtImplicationOperators(item.body, diag);
  for (const Stmt* stmt : item.func_body_stmts) {
    ReportStmtImplicationOperators(stmt, diag);
  }
}

}  // namespace delta
