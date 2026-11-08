#ifndef DELTA_ELABORATOR_GLOBAL_CLOCK_ASSERTION_EVENT_H
#define DELTA_ELABORATOR_GLOBAL_CLOCK_ASSERTION_EVENT_H

#include <cstddef>
#include <string_view>
#include <vector>

#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "parser/expr_substitute.h"

namespace delta {

class Arena;

bool IsGlobalClockLeadingEvent(const std::vector<EventExpr>& sensitivity);

bool SubstituteGlobalClockLeadingEvent(
    std::vector<EventExpr>& sensitivity,
    const std::vector<EventExpr>& global_event);

Stmt* SubstituteGlobalClockEventControls(
    Stmt* stmt, const std::vector<EventExpr>& global_event, Arena& arena);

Expr* SubstituteGlobalClockInActual(Expr* actual,
                                    const std::vector<EventExpr>& global_event,
                                    Arena& arena);

Expr* SubstituteGlobalClockInInstanceActuals(
    Expr* call, const std::vector<EventExpr>& global_event, Arena& arena);

const std::vector<EventExpr>* EffectiveGlobalClockingEvent(
    const std::vector<EventExpr>* declared_events,
    std::string_view declaring_inst_path,
    std::string_view referencing_inst_path, Arena& arena);

template <typename Scope>
void ResolveGlobalClockInCheckerActuals(ActualsByFormal& actuals,
                                        const std::vector<Scope>& scopes,
                                        std::string_view checker_inst_path,
                                        Arena& arena) {
  if (scopes.empty()) return;
  size_t last_dot = checker_inst_path.rfind('.');
  std::string_view parent = checker_inst_path.substr(
      0, last_dot == std::string_view::npos ? 0 : last_dot);
  const std::vector<EventExpr>* in_parent = EffectiveGlobalClockingEvent(
      scopes.back().events, scopes.back().inst_path, parent, arena);
  for (auto& entry : actuals) {
    entry.second =
        SubstituteGlobalClockInActual(entry.second, *in_parent, arena);
  }
}

}  // namespace delta

#endif
