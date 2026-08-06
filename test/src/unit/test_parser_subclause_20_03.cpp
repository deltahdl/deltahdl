// §20.3 Simulation time system functions — head clause. The head owns
// Syntax 20-2: the single production
//   time_function ::= $time | $stime | $realtime
// naming exactly these three system function names as the ways to read the
// current simulation time. The per-function return semantics ($time's 64-bit
// rounded value, $stime's 32-bit truncation, $realtime's real result) live in
// the descendant subclauses §20.3.1–§20.3.3 and are tested in their own files.
// These tests observe the parser accepting each of the three grammar
// alternatives as a system function call primary (ExprKind::kSystemCall),
// carrying the corresponding callee name, in the bare argument-less form the
// syntax shows and as an operand inside a larger expression.
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

// Syntax 20-2, alternative 1: $time parses as a system call whose callee is
// "$time", in the bare form (no parentheses) the grammar shows — no arguments.
TEST(TimeFunctionSyntax, TimeAlternativeParses) {
  auto r = Parse(
      "module m;\n"
      "  integer t;\n"
      "  initial t = $time;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSystemCall);
  EXPECT_EQ(rhs->callee, "$time");
  EXPECT_TRUE(rhs->args.empty());
}

// Syntax 20-2, alternative 2: $stime parses as a system call named "$stime".
TEST(TimeFunctionSyntax, StimeAlternativeParses) {
  auto r = Parse(
      "module m;\n"
      "  integer t;\n"
      "  initial t = $stime;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSystemCall);
  EXPECT_EQ(rhs->callee, "$stime");
  EXPECT_TRUE(rhs->args.empty());
}

// Syntax 20-2, alternative 3: $realtime parses as a system call named
// "$realtime".
TEST(TimeFunctionSyntax, RealtimeAlternativeParses) {
  auto r = Parse(
      "module m;\n"
      "  real t;\n"
      "  initial t = $realtime;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kSystemCall);
  EXPECT_EQ(rhs->callee, "$realtime");
  EXPECT_TRUE(rhs->args.empty());
}

// Syntax 20-2: a time_function is a primary expression, so it may appear as an
// operand of a larger expression rather than only as a bare right-hand side.
// Here $time feeds an addition; the parser must place the system call as the
// binary operator's left operand.
TEST(TimeFunctionSyntax, TimeFunctionAsExpressionOperand) {
  auto r = Parse(
      "module m;\n"
      "  integer t;\n"
      "  initial t = $time + 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kBinary);
  ASSERT_NE(rhs->lhs, nullptr);
  EXPECT_EQ(rhs->lhs->kind, ExprKind::kSystemCall);
  EXPECT_EQ(rhs->lhs->callee, "$time");
}

// Syntax 20-2: a further syntactic position for the time_function primary — as
// an argument of an enclosing system task call. The parser must nest the inner
// $time system call inside the outer call's argument list rather than folding
// the two together.
TEST(TimeFunctionSyntax, TimeFunctionAsCallArgument) {
  auto r = Parse(
      "module m;\n"
      "  initial $display($time);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* call = FirstInitialExpr(r);
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(call->kind, ExprKind::kSystemCall);
  EXPECT_EQ(call->callee, "$display");
  ASSERT_EQ(call->args.size(), 1u);
  EXPECT_EQ(call->args[0]->kind, ExprKind::kSystemCall);
  EXPECT_EQ(call->args[0]->callee, "$time");
}

// Negative form for the production: the grammar requires the $-prefixed system
// name. The closest non-matching input — a plain identifier spelled "stime"
// with no leading $ (a legal, non-keyword identifier) — is an ordinary
// reference (ExprKind::kIdentifier), not a time_function system call. This
// shows the production is keyed on the $ form rather than the bare word.
TEST(TimeFunctionSyntax, PlainIdentifierIsNotTimeFunction) {
  auto r = Parse(
      "module m;\n"
      "  integer stime;\n"
      "  integer t;\n"
      "  initial t = stime;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  EXPECT_EQ(rhs->kind, ExprKind::kIdentifier);
  EXPECT_NE(rhs->kind, ExprKind::kSystemCall);
}

}  // namespace
