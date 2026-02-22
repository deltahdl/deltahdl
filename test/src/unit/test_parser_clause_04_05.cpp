#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult4b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

static ParseResult4b Parse(const std::string &src) {
  ParseResult4b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static ModuleItem *FirstItem(ParseResult4b &r) {
  if (!r.cu || r.cu->modules.empty() || r.cu->modules[0]->items.empty())
    return nullptr;
  return r.cu->modules[0]->items[0];
}

static Stmt *FirstInitialStmt(ParseResult4b &r) {
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

static ModuleItem *FirstAlwaysItem(ParseResult4b &r) {
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysBlock ||
        item->kind == ModuleItemKind::kAlwaysCombBlock ||
        item->kind == ModuleItemKind::kAlwaysFFBlock ||
        item->kind == ModuleItemKind::kAlwaysLatchBlock) {
      return item;
    }
  }
  return nullptr;
}

static ModuleItem *FindItemByKind(ParseResult4b &r, ModuleItemKind kind) {
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == kind)
      return item;
  }
  return nullptr;
}

static ModuleItem *FindContAssign(ParseResult4b &r) {
  return FindItemByKind(r, ModuleItemKind::kContAssign);
}

static ModuleItem *FindInitialBlock(ParseResult4b &r) {
  return FindItemByKind(r, ModuleItemKind::kInitialBlock);
}

// =============================================================================
// LRM section 4.5 -- Simulation scheduling semantics
//
// These tests verify that all syntactic constructs related to the simulation
// scheduling regions (Active, Inactive, NBA, Observed, Reactive, Preponed,
// Postponed) parse correctly.
// =============================================================================

// ---------------------------------------------------------------------------
// 1. Blocking assignment in always block (Active region)
// ---------------------------------------------------------------------------

TEST(ParserSection4, Sec4_5_BlockingAssignInAlways) {
  auto r = Parse("module m;\n"
                 "  reg a, b;\n"
                 "  always @(b) a = b;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kAlwaysBlock);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
  EXPECT_NE(item->body->lhs, nullptr);
  EXPECT_NE(item->body->rhs, nullptr);
}

// ---------------------------------------------------------------------------
// 2. Non-blocking assignment in always block (NBA region)
// ---------------------------------------------------------------------------

TEST(ParserSection4, Sec4_5_NonblockingAssignInAlways) {
  auto r = Parse("module m;\n"
                 "  reg q, d, clk;\n"
                 "  always @(posedge clk) q <= d;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kNonblockingAssign);
  EXPECT_NE(item->body->lhs, nullptr);
  EXPECT_NE(item->body->rhs, nullptr);
}

// ---------------------------------------------------------------------------
// 3. Continuous assignment with assign (Active region)
// ---------------------------------------------------------------------------

TEST(ParserSection4, Sec4_5_ContinuousAssign) {
  auto r = Parse("module m;\n"
                 "  wire y;\n"
                 "  wire a, b;\n"
                 "  assign y = a & b;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *ca = FindContAssign(r);
  ASSERT_NE(ca, nullptr);
  EXPECT_NE(ca->assign_lhs, nullptr);
  EXPECT_NE(ca->assign_rhs, nullptr);
}

// ---------------------------------------------------------------------------
// 4. #0 delay control (Inactive region)
// ---------------------------------------------------------------------------

TEST(ParserSection4, Sec4_5_ZeroDelayControl) {
  auto r = Parse("module m;\n"
                 "  reg a;\n"
                 "  initial begin\n"
                 "    #0 a = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDelay);
  EXPECT_NE(stmt->delay, nullptr);
  EXPECT_NE(stmt->body, nullptr);
}

// ---------------------------------------------------------------------------
// 5. #1 delay control with blocking assign
// ---------------------------------------------------------------------------

TEST(ParserSection4, Sec4_5_UnitDelayControl) {
  auto r = Parse("module m;\n"
                 "  reg a;\n"
                 "  initial begin\n"
                 "    #1 a = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDelay);
  EXPECT_NE(stmt->delay, nullptr);
  EXPECT_NE(stmt->body, nullptr);
}

// ---------------------------------------------------------------------------
// 6. Multiple non-blocking assignments in sequence
// ---------------------------------------------------------------------------

TEST(ParserSection4, Sec4_5_MultipleNonblockingAssigns) {
  auto r = Parse("module m;\n"
                 "  reg a, b, c, d;\n"
                 "  initial begin\n"
                 "    a <= b;\n"
                 "    c <= d;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *init_item = FindInitialBlock(r);
  ASSERT_NE(init_item, nullptr);
  auto *body = init_item->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kNonblockingAssign);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kNonblockingAssign);
}

// ---------------------------------------------------------------------------
// 7. Mix of blocking and non-blocking assignments
// ---------------------------------------------------------------------------

TEST(ParserSection4, Sec4_5_MixBlockingNonblocking) {
  auto r = Parse("module m;\n"
                 "  reg a, b, c, d;\n"
                 "  initial begin\n"
                 "    a = b;\n"
                 "    c <= d;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *init_item = FindInitialBlock(r);
  ASSERT_NE(init_item, nullptr);
  auto *body = init_item->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kNonblockingAssign);
}

// ---------------------------------------------------------------------------
// 8. $display system call (Active region)
// ---------------------------------------------------------------------------

TEST(ParserSection4, Sec4_5_DisplaySystemCall) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    $display(\"hello\");\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
  EXPECT_EQ(stmt->expr->callee, "$display");
}

// ---------------------------------------------------------------------------
// 9. $monitor system call
// ---------------------------------------------------------------------------

TEST(ParserSection4, Sec4_5_MonitorSystemCall) {
  auto r = Parse("module m;\n"
                 "  reg a;\n"
                 "  initial begin\n"
                 "    $monitor(\"a=%b\", a);\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
  EXPECT_EQ(stmt->expr->callee, "$monitor");
}

// ---------------------------------------------------------------------------
// 10. $strobe system call (Postponed region sampling)
// ---------------------------------------------------------------------------

TEST(ParserSection4, Sec4_5_StrobeSystemCall) {
  auto r = Parse("module m;\n"
                 "  reg a;\n"
                 "  initial begin\n"
                 "    $strobe(\"a=%b\", a);\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kExprStmt);
  ASSERT_NE(stmt->expr, nullptr);
  EXPECT_EQ(stmt->expr->kind, ExprKind::kSystemCall);
  EXPECT_EQ(stmt->expr->callee, "$strobe");
}

// ---------------------------------------------------------------------------
// 11. @(posedge clk) event control
// ---------------------------------------------------------------------------

TEST(ParserSection4, Sec4_5_PosedgeEventControl) {
  auto r = Parse("module m;\n"
                 "  reg clk, a;\n"
                 "  initial begin\n"
                 "    @(posedge clk) a = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_FALSE(stmt->events.empty());
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
  EXPECT_NE(stmt->body, nullptr);
}

// ---------------------------------------------------------------------------
// 12. @(negedge clk) event control
// ---------------------------------------------------------------------------

TEST(ParserSection4, Sec4_5_NegedgeEventControl) {
  auto r = Parse("module m;\n"
                 "  reg clk, a;\n"
                 "  initial begin\n"
                 "    @(negedge clk) a = 0;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_FALSE(stmt->events.empty());
  EXPECT_EQ(stmt->events[0].edge, Edge::kNegedge);
  EXPECT_NE(stmt->body, nullptr);
}

// ---------------------------------------------------------------------------
// 13. @* (implicit sensitivity) event control
// ---------------------------------------------------------------------------

TEST(ParserSection4, Sec4_5_StarEventControl) {
  auto r = Parse("module m;\n"
                 "  reg a, b;\n"
                 "  initial begin\n"
                 "    @* a = b;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_TRUE(stmt->is_star_event);
  EXPECT_TRUE(stmt->events.empty());
}

// ---------------------------------------------------------------------------
// 14. @(*) -- parenthesized implicit sensitivity
// ---------------------------------------------------------------------------

TEST(ParserSection4, Sec4_5_ParenStarEventControl) {
  auto r = Parse("module m;\n"
                 "  reg a, b;\n"
                 "  initial begin\n"
                 "    @(*) a = b;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_TRUE(stmt->is_star_event);
  EXPECT_TRUE(stmt->events.empty());
}

// ---------------------------------------------------------------------------
// 15. wait statement for level-sensitive control
// ---------------------------------------------------------------------------

TEST(ParserSection4, Sec4_5_WaitStatement) {
  auto r = Parse("module m;\n"
                 "  reg done, a;\n"
                 "  initial begin\n"
                 "    wait (done) a = 1;\n"
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

// ---------------------------------------------------------------------------
// 16. fork-join block (concurrent scheduling)
// ---------------------------------------------------------------------------

TEST(ParserSection4, Sec4_5_ForkJoin) {
  auto r = Parse("module m;\n"
                 "  reg a, b;\n"
                 "  initial begin\n"
                 "    fork\n"
                 "      #10 a = 1;\n"
                 "      #20 b = 1;\n"
                 "    join\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoin);
  EXPECT_GE(stmt->fork_stmts.size(), 2u);
}

// ---------------------------------------------------------------------------
// 17. fork-join_any block
// ---------------------------------------------------------------------------

TEST(ParserSection4, Sec4_5_ForkJoinAny) {
  auto r = Parse("module m;\n"
                 "  reg a, b;\n"
                 "  initial begin\n"
                 "    fork\n"
                 "      #10 a = 1;\n"
                 "      #20 b = 1;\n"
                 "    join_any\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoinAny);
}

// ---------------------------------------------------------------------------
// 18. fork-join_none block
// ---------------------------------------------------------------------------

TEST(ParserSection4, Sec4_5_ForkJoinNone) {
  auto r = Parse("module m;\n"
                 "  reg a, b;\n"
                 "  initial begin\n"
                 "    fork\n"
                 "      #10 a = 1;\n"
                 "      #20 b = 1;\n"
                 "    join_none\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoinNone);
}

// ---------------------------------------------------------------------------
// 19. always_comb block (scheduling semantics)
// ---------------------------------------------------------------------------

TEST(ParserSection4, Sec4_5_AlwaysComb) {
  auto r = Parse("module m;\n"
                 "  reg a, b, c;\n"
                 "  always_comb a = b & c;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kAlwaysBlock);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysComb);
  ASSERT_NE(item->body, nullptr);
}

// ---------------------------------------------------------------------------
// 20. always_ff block
// ---------------------------------------------------------------------------

TEST(ParserSection4, Sec4_5_AlwaysFF) {
  auto r = Parse("module m;\n"
                 "  reg q, d, clk;\n"
                 "  always_ff @(posedge clk) q <= d;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kAlwaysBlock);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysFF);
  ASSERT_FALSE(item->sensitivity.empty());
  EXPECT_EQ(item->sensitivity[0].edge, Edge::kPosedge);
}

// ---------------------------------------------------------------------------
// 21. always_latch block
// ---------------------------------------------------------------------------

TEST(ParserSection4, Sec4_5_AlwaysLatch) {
  auto r = Parse("module m;\n"
                 "  reg q, d, en;\n"
                 "  always_latch\n"
                 "    if (en) q <= d;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kAlwaysBlock);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysLatch);
  ASSERT_NE(item->body, nullptr);
}

// ---------------------------------------------------------------------------
// 22. initial block with delays
// ---------------------------------------------------------------------------

TEST(ParserSection4, Sec4_5_InitialBlockWithDelays) {
  auto r = Parse("module m;\n"
                 "  reg a, b;\n"
                 "  initial begin\n"
                 "    #5 a = 1;\n"
                 "    #10 b = 0;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *init_item = FindInitialBlock(r);
  ASSERT_NE(init_item, nullptr);
  ASSERT_NE(init_item->body, nullptr);
  EXPECT_EQ(init_item->body->kind, StmtKind::kBlock);
  ASSERT_GE(init_item->body->stmts.size(), 2u);
  EXPECT_EQ(init_item->body->stmts[0]->kind, StmtKind::kDelay);
  EXPECT_EQ(init_item->body->stmts[1]->kind, StmtKind::kDelay);
}

// ---------------------------------------------------------------------------
// 23. final block
// ---------------------------------------------------------------------------

TEST(ParserSection4, Sec4_5_FinalBlock) {
  auto r = Parse("module m;\n"
                 "  final begin\n"
                 "    $display(\"simulation done\");\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kFinalBlock);
  ASSERT_NE(item->body, nullptr);
}

// ---------------------------------------------------------------------------
// 24. Program block (Reactive region)
// ---------------------------------------------------------------------------

TEST(ParserSection4, Sec4_5_ProgramBlock) {
  auto r = Parse("program test_prog;\n"
                 "  initial begin\n"
                 "    $display(\"reactive region\");\n"
                 "  end\n"
                 "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->name, "test_prog");
  EXPECT_EQ(r.cu->programs[0]->decl_kind, ModuleDeclKind::kProgram);
  ASSERT_FALSE(r.cu->programs[0]->items.empty());
  EXPECT_EQ(r.cu->programs[0]->items[0]->kind, ModuleItemKind::kInitialBlock);
}

// ---------------------------------------------------------------------------
// 25. Assert immediate (Observed region)
// ---------------------------------------------------------------------------

TEST(ParserSection4, Sec4_5_AssertImmediate) {
  auto r = Parse("module m;\n"
                 "  reg a;\n"
                 "  initial begin\n"
                 "    assert (a == 1);\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
  EXPECT_NE(stmt->assert_expr, nullptr);
}

// ---------------------------------------------------------------------------
// 26. Assign with delay (assign #5 y = a & b)
// ---------------------------------------------------------------------------

TEST(ParserSection4, Sec4_5_ContinuousAssignWithDelay) {
  auto r = Parse("module m;\n"
                 "  wire y;\n"
                 "  wire a, b;\n"
                 "  assign #5 y = a & b;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *ca = FindContAssign(r);
  ASSERT_NE(ca, nullptr);
  ASSERT_NE(ca->assign_delay, nullptr);
  EXPECT_EQ(ca->assign_delay->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(ca->assign_delay->int_val, 5u);
  EXPECT_NE(ca->assign_lhs, nullptr);
  EXPECT_NE(ca->assign_rhs, nullptr);
}

// ---------------------------------------------------------------------------
// 27. Non-blocking assign with intra-assignment delay (a <= #2 b)
// ---------------------------------------------------------------------------

TEST(ParserSection4, Sec4_5_NonblockingAssignWithDelay) {
  auto r = Parse("module m;\n"
                 "  reg a, b;\n"
                 "  initial begin\n"
                 "    a <= #2 b;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  EXPECT_NE(stmt->delay, nullptr);
  EXPECT_NE(stmt->lhs, nullptr);
  EXPECT_NE(stmt->rhs, nullptr);
}

// ---------------------------------------------------------------------------
// 28. Intra-assignment delay on blocking assign (a = #5 b)
// ---------------------------------------------------------------------------

TEST(ParserSection4, Sec4_5_BlockingIntraAssignDelay) {
  auto r = Parse("module m;\n"
                 "  reg a, b;\n"
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
  EXPECT_NE(stmt->lhs, nullptr);
  EXPECT_NE(stmt->rhs, nullptr);
}

// ---------------------------------------------------------------------------
// 29. Multiple event control in always block
// ---------------------------------------------------------------------------

TEST(ParserSection4, Sec4_5_MultipleEventControlInAlways) {
  auto r = Parse("module m;\n"
                 "  reg clk, rst, a;\n"
                 "  always @(posedge clk or negedge rst) begin\n"
                 "    if (!rst)\n"
                 "      a <= 0;\n"
                 "    else\n"
                 "      a <= 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_GE(item->sensitivity.size(), 2u);
  EXPECT_EQ(item->sensitivity[0].edge, Edge::kPosedge);
  EXPECT_EQ(item->sensitivity[1].edge, Edge::kNegedge);
}

// ---------------------------------------------------------------------------
// 30. Disable statement (task/block disable)
// ---------------------------------------------------------------------------

TEST(ParserSection4, Sec4_5_DisableStatement) {
  auto r = Parse("module m;\n"
                 "  initial begin : blk\n"
                 "    disable blk;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDisable);
}
