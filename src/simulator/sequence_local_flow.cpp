#include "simulator/sequence_local_flow.h"

#include <cstddef>
#include <cstdint>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_name_tables.h"
#include "simulator/statement_assign.h"
#include "simulator/variable.h"

namespace delta {

bool PassedAsWholeActual(const Expr* instance, std::string_view name) {
  for (const Expr* arg : instance->args) {
    if (arg != nullptr && arg->kind == ExprKind::kIdentifier &&
        arg->text == name) {
      return true;
    }
  }
  return false;
}

std::vector<DeclaredNameTables::MatchLocals> NamedMatchLocals(
    const std::vector<SeqLocalDecl>& locals,
    const std::vector<std::vector<Logic4Vec>>& ended) {
  std::vector<DeclaredNameTables::MatchLocals> matches;
  for (const std::vector<Logic4Vec>& values : ended) {
    DeclaredNameTables::MatchLocals match;
    for (size_t i = 0; i < values.size(); ++i) {
      match.emplace_back(locals[i].name, values[i]);
    }
    matches.push_back(std::move(match));
  }
  return matches;
}

const std::vector<DeclaredNameTables::MatchLocals>* FlowedMatches(
    const Expr* operand, SimContext& ctx) {
  if (operand->kind != ExprKind::kMemberAccess ||
      operand->lhs->kind != ExprKind::kCall ||
      operand->rhs->text != "triggered") {
    return nullptr;
  }
  return ctx.EndpointLocals(ctx.FindSequenceInstanceEndpoint(operand->lhs),
                            ctx.CurrentTime().ticks);
}

void TakeFlowedLocals(const Expr* operand, uint32_t pick, SimContext& ctx,
                      Arena& arena) {
  const std::vector<DeclaredNameTables::MatchLocals>* matches =
      FlowedMatches(operand, ctx);
  if (matches == nullptr) return;
  for (const auto& [name, value] : (*matches)[pick]) {
    Variable* var = PassedAsWholeActual(operand->lhs, name)
                        ? ctx.FindLocalVariable(name)
                        : nullptr;
    if (var == nullptr) continue;
    var->value = ResizeToWidth(value, var->value.width, arena);
  }
}

}  // namespace delta
