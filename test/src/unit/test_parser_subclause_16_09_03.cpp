#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

TEST(AssertionParsing, SampledFunctionInAssert) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a |-> b)\n"
      "    else $error(\"a=%b b=%b\", $sampled(a), $sampled(b));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AssertionParsing, RoseFunctionInProperty) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) $rose(req) |-> ##[1:3] ack);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AssertionParsing, PastFunctionWithTicks) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) $past(req, 2) |-> ack);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AssertionParsing, PastTicksAsParameter) {
  auto r = Parse(
      "module m;\n"
      "  parameter N = 2;\n"
      "  assert property (@(posedge clk) $past(req, N) |-> ack);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AssertionParsing, PastTicksAsLocalparam) {
  auto r = Parse(
      "module m;\n"
      "  localparam int K = 3;\n"
      "  assert property (@(posedge clk) $past(req, K) |-> ack);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AssertionParsing, PastOmittedMiddleArgument) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) $past(in1, , enable) |-> ack);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AssertionParsing, RoseWithExplicitClockingEvent) {
  auto r = Parse(
      "module m;\n"
      "  assert property\n"
      "    (@(posedge clk) en && $rose(req, @(posedge fclk)) |=> gnt);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AssertionParsing, RoseInProceduralAssignment) {
  auto r = Parse(
      "module m;\n"
      "  always @(posedge clk) reg1 <= a & $rose(b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AssertionParsing, PastInProceduralAssignment) {
  auto r = Parse(
      "module m;\n"
      "  always @(posedge clk) reg1 <= a & $past(b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AssertionParsing, ValueChangeFunctionKeepsItsParenthesisedClock) {
  auto r = Parse(
      "module m;\n"
      "  logic clk, s, x;\n"
      "  initial x = $rose(s, @(posedge clk));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const Stmt* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  ASSERT_NE(stmt->rhs->sampled_clock, nullptr);
  ASSERT_EQ(stmt->rhs->sampled_clock->size(), 1u);
  const EventExpr& ev = (*stmt->rhs->sampled_clock)[0];
  EXPECT_EQ(ev.edge, Edge::kPosedge);
  ASSERT_NE(ev.signal, nullptr);
  EXPECT_EQ(ev.signal->text, "clk");
}

TEST(AssertionParsing, ValueChangeFunctionKeepsItsBareNamedClock) {
  auto r = Parse(
      "module m;\n"
      "  logic clk, s, x;\n"
      "  initial x = $fell(s, @clk);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const Stmt* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_NE(stmt->rhs, nullptr);
  ASSERT_NE(stmt->rhs->sampled_clock, nullptr);
  ASSERT_EQ(stmt->rhs->sampled_clock->size(), 1u);
  const EventExpr& ev = (*stmt->rhs->sampled_clock)[0];
  EXPECT_EQ(ev.edge, Edge::kNone);
  ASSERT_NE(ev.signal, nullptr);
  EXPECT_EQ(ev.signal->text, "clk");
}

}  // namespace
