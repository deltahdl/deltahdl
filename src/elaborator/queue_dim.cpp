#include "elaborator/queue_dim.h"

#include <cstdint>
#include <optional>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator_validate_internal.h"
#include "parser/ast.h"

namespace delta {

bool IsQueueDim(const Expr* dim) {
  return dim && dim->kind == ExprKind::kIdentifier && dim->text == "$";
}

std::optional<int32_t> QueueBoundMaxSize(int64_t bound) {
  if (bound <= 0) return std::nullopt;
  return static_cast<int32_t>(bound + 1);
}

static void CheckStmtQueueBound(const Stmt* s, const ScopeMap& scope,
                                DiagEngine& diag) {
  if (s->kind != StmtKind::kVarDecl || s->var_unpacked_dims.empty()) return;
  const auto* dim = s->var_unpacked_dims[0];
  if (!IsQueueDim(dim) || !dim->rhs) return;
  auto bound = ConstEvalInt(dim->rhs, scope);
  if (!bound || QueueBoundMaxSize(*bound)) return;
  diag.Error(s->range.start, "queue bound must be a positive integer",
             Subclause("7.10"));
}

// §7.10, Syntax 7-4 says the constant_expression of a queue_dimension "shall
// evaluate to a positive integer value" and names no position, so the rule is
// owed wherever a declaration carrying a queue dimension can be written. A.6.3
// gives `seq_block ::= begin [ : block_identifier ] { block_item_declaration }
// { statement_or_null } end` and A.6.12 gives `rs_code_block ::= { {
// data_declaration } { statement_or_null } }`, so that is every position a
// statement holds a statement in.
//
// ForEachChildStmt in elaborator_validate_internal.h states those positions,
// once for the whole elaborator, which is why the list is not written out again
// here. It hands the visitor the field itself, so a walk that only reads the
// tree takes a `Stmt* const&`.
//
// Stmt::for_steps is walked because the shared list is walked whole, and no
// conforming source puts a declaration in it: A.6.8 gives `for_step_assignment
// ::= operator_assignment | inc_or_dec_expression | function_subroutine_call`,
// none of which is a data_declaration. Stmt::for_inits is the same case, A.6.8
// admitting a list_of_variable_assignments or a for_variable_declaration whose
// variable_identifier carries no dimension.
void CheckBlockQueueBounds(const Stmt* s, const ScopeMap& scope,
                           DiagEngine& diag) {
  if (!s) return;
  CheckStmtQueueBound(s, scope, diag);
  ForEachChildStmt(
      s, [&](Stmt* const& sub) { CheckBlockQueueBounds(sub, scope, diag); });
}

}  // namespace delta
