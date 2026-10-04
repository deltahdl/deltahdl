#include "simulator/modport_expression.h"

#include <cstdint>
#include <string>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/evaluation.h"
#include "simulator/instance_prefix_override.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"

namespace delta {

// The modport expression port `expr` names, `i.P` with i an interface port
// of the running instance, or null.
static const ModportExpressionPort* PortNamedBy(const Expr* expr,
                                                SimContext& ctx) {
  if (expr == nullptr || !ctx.HasModportExpressions() ||
      expr->kind != ExprKind::kMemberAccess || expr->is_scope_resolution ||
      expr->lhs == nullptr || expr->lhs->kind != ExprKind::kIdentifier ||
      expr->rhs == nullptr || expr->rhs->kind != ExprKind::kIdentifier) {
    return nullptr;
  }
  return ctx.FindModportExpression(ctx.ActiveInstancePrefix() +
                                   std::string(expr->lhs->text) + "." +
                                   std::string(expr->rhs->text));
}

bool TryModportExpressionRead(const Expr* expr, SimContext& ctx, Arena& arena,
                              Logic4Vec& out) {
  const ModportExpressionPort* port = PortNamedBy(expr, ctx);
  if (port == nullptr) return false;
  InstancePrefixOverride in_instance(ctx.InstancePrefixOverride(),
                                     port->instance_prefix);
  out = EvalExpr(port->expr, ctx, arena);
  return true;
}

bool TryModportExpressionWrite(const Expr* lhs, const Logic4Vec& value,
                               SimContext& ctx, Arena& arena) {
  const ModportExpressionPort* port = PortNamedBy(lhs, ctx);
  if (port == nullptr) return false;
  InstancePrefixOverride in_instance(ctx.InstancePrefixOverride(),
                                     port->instance_prefix);
  PerformBlockingAssign(port->expr, value, ctx, arena);
  return true;
}

bool TryModportExpressionAssign(const Stmt* stmt, SimContext& ctx,
                                Arena& arena) {
  if (stmt->rhs == nullptr || PortNamedBy(stmt->lhs, ctx) == nullptr)
    return false;
  return TryModportExpressionWrite(stmt->lhs, EvalExpr(stmt->rhs, ctx, arena),
                                   ctx, arena);
}

// The statement `stmt` with the expression `port` stands for as its target in
// place of the port, built once per statement and port.
static const Stmt* NonblockingOfExpression(const Stmt* stmt,
                                           const ModportExpressionPort* port,
                                           SimContext& ctx, Arena& arena) {
  if (const Stmt* built = ctx.FindModportExpressionNba(stmt, port))
    return built;
  auto* nba = arena.Create<Stmt>(*stmt);
  nba->lhs = port->expr;
  ctx.RecordModportExpressionNba(stmt, port, nba);
  return nba;
}

bool TryModportExpressionNonblocking(const Stmt* stmt, const NbaSample& sample,
                                     uint64_t delay_ticks, SimContext& ctx,
                                     Arena& arena) {
  const ModportExpressionPort* port = PortNamedBy(stmt->lhs, ctx);
  if (port == nullptr) return false;
  const Stmt* nba = NonblockingOfExpression(stmt, port, ctx, arena);
  InstancePrefixOverride in_instance(ctx.InstancePrefixOverride(),
                                     port->instance_prefix);
  ScheduleNonblockingAssign(nba, sample, delay_ticks, ctx, arena);
  return true;
}

}  // namespace delta
