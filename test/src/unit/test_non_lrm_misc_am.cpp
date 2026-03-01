// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §9.4.2.1: mixed or and comma
TEST(ParserA605, EventExprMixedOrComma) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(a or b, c) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->events.size(), 3u);
}

// §9.4.2.1: posedge with comma
TEST(ParserA605, EventExprPosedgeComma) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(posedge clk, negedge rstn) x <= 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_EQ(stmt->events.size(), 2u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
  EXPECT_EQ(stmt->events[1].edge, Edge::kNegedge);
}

// ---------------------------------------------------------------------------
// procedural_timing_control ::=
//   delay_control | event_control | cycle_delay
// ---------------------------------------------------------------------------
// §9.4: procedural_timing_control with delay_control
TEST(ParserA605, ProceduralTimingControlDelayControl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    #5 x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDelay);
}

// §9.4: procedural_timing_control with event_control
TEST(ParserA605, ProceduralTimingControlEventControl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(negedge clk) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
}

// ---------------------------------------------------------------------------
// jump_statement ::= return [ expression ] ; | break ; | continue ;
// ---------------------------------------------------------------------------
// §12.8: return with expression from non-void function
TEST(ParserA605, JumpReturnWithExpr) {
  auto r = Parse(
      "module m;\n"
      "  function int f(); return 42; endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* func = FirstFunctionDecl(r);
  ASSERT_NE(func, nullptr);
  ASSERT_GE(func->func_body_stmts.size(), 1u);
  auto* stmt = func->func_body_stmts[0];
  EXPECT_EQ(stmt->kind, StmtKind::kReturn);
  EXPECT_NE(stmt->expr, nullptr);
}

// §12.8: return without expression from void function
TEST(ParserA605, JumpReturnVoid) {
  auto r = Parse(
      "module m;\n"
      "  function void f(); return; endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* func = FirstFunctionDecl(r);
  ASSERT_NE(func, nullptr);
  ASSERT_GE(func->func_body_stmts.size(), 1u);
  auto* stmt = func->func_body_stmts[0];
  EXPECT_EQ(stmt->kind, StmtKind::kReturn);
  EXPECT_EQ(stmt->expr, nullptr);
}

// §12.8: break statement
TEST(ParserA605, JumpBreak) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    forever begin\n"
      "      break;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  VerifyForeverLoopJump(body, StmtKind::kBreak);
}

// §12.8: continue statement
TEST(ParserA605, JumpContinue) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    forever begin\n"
      "      continue;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  VerifyForeverLoopJump(body, StmtKind::kContinue);
}

// ---------------------------------------------------------------------------
// wait_statement ::=
//   wait ( expression ) statement_or_null
//   | wait fork ;
//   | wait_order ( hierarchical_identifier { , hierarchical_identifier } )
//     action_block
// ---------------------------------------------------------------------------
// §9.4.3: wait (condition) statement
TEST(ParserA605, WaitConditionStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait (ready) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
  EXPECT_NE(stmt->condition, nullptr);
  EXPECT_NE(stmt->body, nullptr);
}

// §9.4.3: wait (condition) null statement
TEST(ParserA605, WaitConditionNull) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait (ready) ;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
  EXPECT_NE(stmt->body, nullptr);
  EXPECT_EQ(stmt->body->kind, StmtKind::kNull);
}

// §9.6.1: wait fork
TEST(ParserA605, WaitFork) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait fork;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWaitFork);
}

// §15.5.4: wait_order with semicolon (null action)
TEST(ParserA605, WaitOrderNull) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait_order(a, b, c);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWaitOrder);
  ASSERT_EQ(stmt->wait_order_events.size(), 3u);
}

// §15.5.4: wait_order with success statement
TEST(ParserA605, WaitOrderWithAction) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait_order(a, b) success = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWaitOrder);
  EXPECT_NE(stmt->then_branch, nullptr);
}

// §15.5.4: wait_order with else clause
TEST(ParserA605, WaitOrderWithElse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait_order(a, b, c) success = 1;\n"
      "    else success = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWaitOrder);
  EXPECT_NE(stmt->then_branch, nullptr);
  EXPECT_NE(stmt->else_branch, nullptr);
}

// §15.5.4: wait_order with only else clause
TEST(ParserA605, WaitOrderElseOnly) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait_order(a, b)\n"
      "    else x = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWaitOrder);
  EXPECT_NE(stmt->else_branch, nullptr);
}

}  // namespace
