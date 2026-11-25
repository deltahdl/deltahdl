#include "elaborator/specify_parameter_uses.h"

#include <format>
#include <initializer_list>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/elaborator_validate_internal.h"
#include "elaborator/value_scopes.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_specify.h"

namespace delta {

namespace {

bool HasOperandsReportedAsDelays(ExprKind kind) {
  switch (kind) {
    case ExprKind::kUnary:
    case ExprKind::kBinary:
    case ExprKind::kTernary:
    case ExprKind::kMinTypMax:
    case ExprKind::kSelect:
    case ExprKind::kConcatenation:
    case ExprKind::kAssignmentPattern:
    case ExprKind::kReplicate:
      return true;
    default:
      return false;
  }
}

class SpecifyParameterCheck {
 public:
  SpecifyParameterCheck(const CompilationUnit& unit, DiagEngine& diag)
      : scopes_(unit), diag_(diag) {}

  void CheckModule(const ModuleDecl& decl) {
    scope_ = &scopes_.ModuleScope(decl);
    for (const ModuleItem* item : decl.items) {
      for (const SpecifyItem* specify : item->specify_items)
        CheckItem(*specify);
    }
    for (const ModuleItem* item : decl.items) {
      if (item->nested_module_decl != nullptr) {
        CheckModule(*item->nested_module_decl);
      }
    }
  }

 private:
  void CheckItem(const SpecifyItem& item) {
    CheckPath(item.path);
    CheckTimingCheck(item.timing_check);
    CheckTerminals(item.path_outputs);
    CheckEach({item.param_packed_left, item.param_packed_right});
  }

  void CheckPath(const SpecifyPathDecl& path) {
    CheckTerminals(path.src_ports);
    CheckTerminals(path.dst_ports);
    CheckEach({path.condition, path.data_source});
    for (const Expr* delay : path.delays) CheckDelay(delay);
  }

  void CheckTimingCheck(const TimingCheckDecl& check) {
    CheckTerminals({check.ref_terminal, check.data_terminal});
    CheckEach({check.ref_condition, check.data_condition, check.timestamp_cond,
               check.timecheck_cond, check.delayed_ref_expr,
               check.delayed_data_expr, check.event_based_flag,
               check.remain_active_flag});
    for (const Expr* limit : check.limits) CheckDelay(limit);
  }

  void CheckTerminals(const std::vector<SpecifyTerminal>& terminals) {
    for (const SpecifyTerminal& terminal : terminals) {
      CheckEach({terminal.range_left, terminal.range_right});
    }
  }

  void CheckEach(std::initializer_list<const Expr*> exprs) {
    for (const Expr* e : exprs) CheckExpr(e);
  }

  void CheckDelay(const Expr* e) {
    if (e == nullptr || IsBareName(*e)) return;
    if (!HasOperandsReportedAsDelays(e->kind)) {
      CheckExpr(e);
      return;
    }
    ForEachExprChild(e, [this](const Expr* child) { CheckDelay(child); });
  }

  static bool IsBareName(const Expr& e) {
    return e.kind == ExprKind::kIdentifier && e.scope_prefix.empty();
  }

  void CheckExpr(const Expr* e) {
    if (e == nullptr) return;
    if (e->kind == ExprKind::kIdentifier) {
      Judge(e->text, scopes_.ConstantNamedBy(*e, *scope_), *e);
      return;
    }
    if (e->kind == ExprKind::kMemberAccess) {
      if (e->is_scope_resolution) {
        Judge(e->rhs->text, scopes_.ConstantNamedBy(*e, *scope_), *e);
      }
      CheckExpr(e->lhs);
      return;
    }
    if (e->kind == ExprKind::kCast) {
      Judge(e->text, scopes_.ConstantNamed(e->text, *scope_), *e);
    }
    ForEachExprChild(e, [this](const Expr* child) { CheckExpr(child); });
  }

  void Judge(std::string_view name, ConstantKind constant, const Expr& at) {
    if (constant != ConstantKind::kParameter) return;
    diag_.Error(
        at.range.start,
        std::format("parameter '{}' may not be used inside a specify block",
                    name),
        Subclause("6.20.5"));
  }

  ValueScopes scopes_;
  DiagEngine& diag_;
  const NameScope* scope_ = nullptr;
};

}  // namespace

void ReportParametersUsedInSpecifyBlocks(const CompilationUnit& unit,
                                         DiagEngine& diag) {
  SpecifyParameterCheck check(unit, diag);
  for (const ModuleDecl* decl : unit.modules) check.CheckModule(*decl);
}

}  // namespace delta
