#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

namespace {

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static Stmt *FirstInitialStmt(ParseResult &r) {
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock)
      continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

static Stmt *InitialBody(ParseResult &r) {
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock)
      continue;
    return item->body;
  }
  return nullptr;
}

static ModuleItem *FirstFunctionDecl(ParseResult &r) {
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kFunctionDecl)
      return item;
  }
  return nullptr;
}

} // namespace

// =============================================================================
// A.6.5 Timing control statements
// =============================================================================

// ---------------------------------------------------------------------------
// procedural_timing_control_statement ::=
//   procedural_timing_control statement_or_null
// ---------------------------------------------------------------------------

// §9.4: delay control followed by statement
TEST(ParserA605, ProceduralTimingControlDelay) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    #10 x = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDelay);
  EXPECT_NE(stmt->delay, nullptr);
  EXPECT_NE(stmt->body, nullptr);
  EXPECT_EQ(stmt->body->kind, StmtKind::kBlockingAssign);
}

// §9.4: delay control followed by null statement
TEST(ParserA605, ProceduralTimingControlDelayNull) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    #10 ;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDelay);
  EXPECT_NE(stmt->body, nullptr);
  EXPECT_EQ(stmt->body->kind, StmtKind::kNull);
}

// §9.4.2: event control followed by statement
TEST(ParserA605, ProceduralTimingControlEvent) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    @(posedge clk) x = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_FALSE(stmt->events.empty());
  EXPECT_NE(stmt->body, nullptr);
}

// §9.4.2: event control followed by null statement
TEST(ParserA605, ProceduralTimingControlEventNull) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    @(posedge clk) ;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_NE(stmt->body, nullptr);
  EXPECT_EQ(stmt->body->kind, StmtKind::kNull);
}

// ---------------------------------------------------------------------------
// delay_or_event_control ::=
//   delay_control | event_control | repeat ( expression ) event_control
// (used in intra-assignment context — §9.4.5)
// ---------------------------------------------------------------------------

// §9.4.5: intra-assignment delay in blocking assignment
TEST(ParserA605, IntraAssignDelayBlocking) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    a = #5 b;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_NE(stmt->delay, nullptr);
  EXPECT_NE(stmt->rhs, nullptr);
}

// §9.4.5: intra-assignment event in blocking assignment
TEST(ParserA605, IntraAssignEventBlocking) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    a = @(posedge clk) b;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_FALSE(stmt->events.empty());
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
}

// §9.4.5: repeat event control in blocking assignment
TEST(ParserA605, IntraAssignRepeatEventBlocking) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    a = repeat(3) @(posedge clk) b;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_NE(stmt->repeat_event_count, nullptr);
  EXPECT_FALSE(stmt->events.empty());
}

// §9.4.5: intra-assignment delay in nonblocking assignment
TEST(ParserA605, IntraAssignDelayNonblocking) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    a <= #5 b;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  EXPECT_NE(stmt->delay, nullptr);
}

// §9.4.5: intra-assignment event in nonblocking assignment
TEST(ParserA605, IntraAssignEventNonblocking) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    a <= @(posedge clk) b;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  EXPECT_FALSE(stmt->events.empty());
}

// §9.4.5: repeat event control in nonblocking assignment
TEST(ParserA605, IntraAssignRepeatEventNonblocking) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    a <= repeat(5) @(posedge clk) data;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  EXPECT_NE(stmt->repeat_event_count, nullptr);
  EXPECT_FALSE(stmt->events.empty());
}

// ---------------------------------------------------------------------------
// delay_control ::= # delay_value | # ( mintypmax_expression )
// ---------------------------------------------------------------------------

// §9.4.1: simple numeric delay
TEST(ParserA605, DelayControlNumeric) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    #10 x = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDelay);
  EXPECT_NE(stmt->delay, nullptr);
}

// §9.4.1: identifier-based delay
TEST(ParserA605, DelayControlIdentifier) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    #d x = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDelay);
  EXPECT_NE(stmt->delay, nullptr);
  EXPECT_EQ(stmt->delay->kind, ExprKind::kIdentifier);
}

// §9.4.1: parenthesized delay expression
TEST(ParserA605, DelayControlParenthesized) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    #(10) x = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDelay);
  EXPECT_NE(stmt->delay, nullptr);
}

// §9.4.1/§11.11: parenthesized mintypmax delay
TEST(ParserA605, DelayControlMintypmax) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    #(1:2:3) x = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDelay);
  EXPECT_NE(stmt->delay, nullptr);
  EXPECT_EQ(stmt->delay->kind, ExprKind::kMinTypMax);
}

// ---------------------------------------------------------------------------
// event_control ::= clocking_event | @ * | @ ( * )
// ---------------------------------------------------------------------------

// §9.4.2.2: @* implicit sensitivity
TEST(ParserA605, EventControlAtStar) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    @* y = a & b;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_TRUE(stmt->is_star_event);
}

// §9.4.2.2: @(*) implicit sensitivity
TEST(ParserA605, EventControlAtStarParen) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    @(*) y = a & b;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_TRUE(stmt->is_star_event);
}

// §9.4.2: @identifier simple event control
TEST(ParserA605, EventControlBareIdentifier) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    @r x = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_EQ(stmt->events.size(), 1u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kNone);
  EXPECT_NE(stmt->events[0].signal, nullptr);
}

// §9.4.2: @(expression) parenthesized event control
TEST(ParserA605, EventControlParenthesized) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    @(clk) x = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_EQ(stmt->events.size(), 1u);
}

// ---------------------------------------------------------------------------
// clocking_event ::=
//   @ ps_identifier | @ hierarchical_identifier | @ ( event_expression )
// ---------------------------------------------------------------------------

// §9.4.2: @(posedge clk) — clocking event with edge
TEST(ParserA605, ClockingEventPosedge) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    @(posedge clk) x = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->events.size(), 1u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
}

// §9.4.2: @(negedge clk) — clocking event with negedge
TEST(ParserA605, ClockingEventNegedge) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    @(negedge clk) x = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->events.size(), 1u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kNegedge);
}

// ---------------------------------------------------------------------------
// event_expression ::=
//   [ edge_identifier ] expression [ iff expression ]
//   | sequence_instance [ iff expression ]
//   | event_expression or event_expression
//   | event_expression , event_expression
//   | ( event_expression )
// ---------------------------------------------------------------------------

// §9.4.2: edge_identifier = edge (generic)
TEST(ParserA605, EventExprEdge) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    @(edge clk) x = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->events.size(), 1u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kEdge);
}

// §9.4.2: expression without edge (any change)
TEST(ParserA605, EventExprAnyChange) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    @(a) x = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->events.size(), 1u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kNone);
}

// §9.4.2.3: iff qualifier on event expression
TEST(ParserA605, EventExprIff) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    @(a iff enable) x = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->events.size(), 1u);
  EXPECT_NE(stmt->events[0].iff_condition, nullptr);
}

// §9.4.2.3: posedge with iff qualifier
TEST(ParserA605, EventExprPosedgeIff) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    @(posedge a iff enable == 1) x = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->events.size(), 1u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
  EXPECT_NE(stmt->events[0].iff_condition, nullptr);
}

// §9.4.2.1: or-separated event list
TEST(ParserA605, EventExprOr) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    @(posedge clk_a or posedge clk_b) x = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->events.size(), 2u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
  EXPECT_EQ(stmt->events[1].edge, Edge::kPosedge);
}

// §9.4.2.1: comma-separated event list
TEST(ParserA605, EventExprComma) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    @(a, b, c) x = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->events.size(), 3u);
}

// §9.4.2.1: mixed or and comma
TEST(ParserA605, EventExprMixedOrComma) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    @(a or b, c) x = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->events.size(), 3u);
}

// §9.4.2.1: posedge with comma
TEST(ParserA605, EventExprPosedgeComma) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    @(posedge clk, negedge rstn) x <= 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
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
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    #5 x = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDelay);
}

// §9.4: procedural_timing_control with event_control
TEST(ParserA605, ProceduralTimingControlEventControl) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    @(negedge clk) x = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
}

// ---------------------------------------------------------------------------
// jump_statement ::= return [ expression ] ; | break ; | continue ;
// ---------------------------------------------------------------------------

// §12.8: return with expression from non-void function
TEST(ParserA605, JumpReturnWithExpr) {
  auto r = Parse("module m;\n"
                 "  function int f(); return 42; endfunction\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *func = FirstFunctionDecl(r);
  ASSERT_NE(func, nullptr);
  ASSERT_GE(func->func_body_stmts.size(), 1u);
  auto *stmt = func->func_body_stmts[0];
  EXPECT_EQ(stmt->kind, StmtKind::kReturn);
  EXPECT_NE(stmt->expr, nullptr);
}

// §12.8: return without expression from void function
TEST(ParserA605, JumpReturnVoid) {
  auto r = Parse("module m;\n"
                 "  function void f(); return; endfunction\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *func = FirstFunctionDecl(r);
  ASSERT_NE(func, nullptr);
  ASSERT_GE(func->func_body_stmts.size(), 1u);
  auto *stmt = func->func_body_stmts[0];
  EXPECT_EQ(stmt->kind, StmtKind::kReturn);
  EXPECT_EQ(stmt->expr, nullptr);
}

// §12.8: break statement
TEST(ParserA605, JumpBreak) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    forever begin\n"
                 "      break;\n"
                 "    end\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  auto *forever_stmt = body->stmts[0];
  ASSERT_NE(forever_stmt, nullptr);
  EXPECT_EQ(forever_stmt->kind, StmtKind::kForever);
  auto *loop_body = forever_stmt->body;
  ASSERT_NE(loop_body, nullptr);
  EXPECT_EQ(loop_body->stmts[0]->kind, StmtKind::kBreak);
}

// §12.8: continue statement
TEST(ParserA605, JumpContinue) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    forever begin\n"
                 "      continue;\n"
                 "    end\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  auto *forever_stmt = body->stmts[0];
  auto *loop_body = forever_stmt->body;
  ASSERT_NE(loop_body, nullptr);
  EXPECT_EQ(loop_body->stmts[0]->kind, StmtKind::kContinue);
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
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    wait (ready) x = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
  EXPECT_NE(stmt->condition, nullptr);
  EXPECT_NE(stmt->body, nullptr);
}

// §9.4.3: wait (condition) null statement
TEST(ParserA605, WaitConditionNull) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    wait (ready) ;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
  EXPECT_NE(stmt->body, nullptr);
  EXPECT_EQ(stmt->body->kind, StmtKind::kNull);
}

// §9.6.1: wait fork
TEST(ParserA605, WaitFork) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    wait fork;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWaitFork);
}

// §15.5.4: wait_order with semicolon (null action)
TEST(ParserA605, WaitOrderNull) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    wait_order(a, b, c);\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWaitOrder);
  ASSERT_EQ(stmt->wait_order_events.size(), 3u);
}

// §15.5.4: wait_order with success statement
TEST(ParserA605, WaitOrderWithAction) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    wait_order(a, b) success = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWaitOrder);
  EXPECT_NE(stmt->then_branch, nullptr);
}

// §15.5.4: wait_order with else clause
TEST(ParserA605, WaitOrderWithElse) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    wait_order(a, b, c) success = 1;\n"
                 "    else success = 0;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWaitOrder);
  EXPECT_NE(stmt->then_branch, nullptr);
  EXPECT_NE(stmt->else_branch, nullptr);
}

// §15.5.4: wait_order with only else clause
TEST(ParserA605, WaitOrderElseOnly) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    wait_order(a, b)\n"
                 "    else x = 0;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWaitOrder);
  EXPECT_NE(stmt->else_branch, nullptr);
}

// ---------------------------------------------------------------------------
// event_trigger ::=
//   -> hierarchical_event_identifier nonrange_select ;
//   | ->> [ delay_or_event_control ] hierarchical_event_identifier
//     nonrange_select ;
// ---------------------------------------------------------------------------

// §15.5.1: blocking event trigger
TEST(ParserA605, EventTriggerBlocking) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    -> ev;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventTrigger);
  EXPECT_NE(stmt->expr, nullptr);
}

// §15.5.1: nonblocking event trigger
TEST(ParserA605, EventTriggerNonblocking) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    ->> ev;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNbEventTrigger);
  EXPECT_NE(stmt->expr, nullptr);
}

// ---------------------------------------------------------------------------
// disable_statement ::=
//   disable hierarchical_task_identifier ;
//   | disable hierarchical_block_identifier ;
//   | disable fork ;
// ---------------------------------------------------------------------------

// §9.6.2: disable named block
TEST(ParserA605, DisableBlock) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    disable my_block;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDisable);
  EXPECT_NE(stmt->expr, nullptr);
}

// §9.6.3: disable fork
TEST(ParserA605, DisableFork) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    disable fork;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDisableFork);
}

// ---------------------------------------------------------------------------
// edge_identifier ::= posedge | negedge | edge
// ---------------------------------------------------------------------------

// §9.4.2: all three edge identifiers parsed correctly
TEST(ParserA605, EdgeIdentifiers) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    @(posedge a or negedge b or edge c) x = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->events.size(), 3u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
  EXPECT_EQ(stmt->events[1].edge, Edge::kNegedge);
  EXPECT_EQ(stmt->events[2].edge, Edge::kEdge);
}
