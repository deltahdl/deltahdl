#pragma once

// §25.5.4: a modport expression port, `modport A(output .P(r[3:0]), input
// .Q(x))`, gives an expression over the interface's own declarations a name
// of its own, and a module connected through the modport reads and writes the
// expression by that name, `i.P = i.Q`. The lowerer records each such port of
// the modport a connection selects under the port's path, "u1.i.P"
// (DeclaredNameTables::RegisterModportExpression); a read of the path
// evaluates the expression in the interface instance, and a write assigns to
// it there.

namespace delta {

class Arena;
class SimContext;
struct Expr;
struct Logic4Vec;
struct Stmt;

// Answers true and puts in `out` the value of the expression `expr` names
// where `expr`, `i.Q` written in the running instance, is a modport
// expression port; false for any other expression.
bool TryModportExpressionRead(const Expr* expr, SimContext& ctx, Arena& arena,
                              Logic4Vec& out);

// Answers true having assigned `value` to the expression `lhs` names where
// `lhs` is a modport expression port; false for any other target.
bool TryModportExpressionWrite(const Expr* lhs, const Logic4Vec& value,
                               SimContext& ctx, Arena& arena);

// The blocking assignment statement `stmt` with such a port as its target,
// its right-hand side evaluated where the statement stands; false for any
// other statement.
bool TryModportExpressionAssign(const Stmt* stmt, SimContext& ctx,
                                Arena& arena);

}  // namespace delta
