#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// --- Test helpers ---

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
};

static ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

static Stmt *FirstInitialStmt(ParseResult &r) {
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

static ModuleItem *FirstAlwaysItem(ParseResult &r) {
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysBlock) return item;
  }
  return nullptr;
}

// =============================================================================
// LRM section 9.2.1 -- Initial and final blocks
// =============================================================================

TEST(ParserSection9, InitialBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial x = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  bool found = false;
  for (auto *item : mod->items) {
    if (item->kind == ModuleItemKind::kInitialBlock) {
      found = true;
      ASSERT_NE(item->body, nullptr);
    }
  }
  EXPECT_TRUE(found);
}

TEST(ParserSection9, FinalBlock) {
  auto r = Parse(
      "module m;\n"
      "  final $display(\"done\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  bool found = false;
  for (auto *item : mod->items) {
    if (item->kind == ModuleItemKind::kFinalBlock) {
      found = true;
      ASSERT_NE(item->body, nullptr);
    }
  }
  EXPECT_TRUE(found);
}

// =============================================================================
// LRM section 9.2.2 -- Always blocks (always, always_comb, always_ff,
// always_latch)
// =============================================================================

TEST(ParserSection9, AlwaysBlock) {
  auto r = Parse(
      "module m;\n"
      "  always @(posedge clk) q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlways);
  ASSERT_FALSE(item->sensitivity.empty());
  EXPECT_EQ(item->sensitivity[0].edge, Edge::kPosedge);
}

TEST(ParserSection9, AlwaysComb) {
  auto r = Parse(
      "module m;\n"
      "  always_comb a = b & c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysComb);
  ASSERT_NE(item->body, nullptr);
}

TEST(ParserSection9, AlwaysFF) {
  auto r = Parse(
      "module m;\n"
      "  always_ff @(posedge clk) q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysFF);
  ASSERT_FALSE(item->sensitivity.empty());
  EXPECT_EQ(item->sensitivity[0].edge, Edge::kPosedge);
}

TEST(ParserSection9, AlwaysLatch) {
  auto r = Parse(
      "module m;\n"
      "  always_latch\n"
      "    if (en) q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysLatch);
  ASSERT_NE(item->body, nullptr);
}

// =============================================================================
// LRM section 9.3.2 -- Fork / join variants
// =============================================================================

TEST(ParserSection9, ForkJoin) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      #10 a = 1;\n"
      "      #20 b = 1;\n"
      "    join\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoin);
  EXPECT_GE(stmt->fork_stmts.size(), 2u);
}

TEST(ParserSection9, ForkJoinAny) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      #10 a = 1;\n"
      "      #20 b = 1;\n"
      "    join_any\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoinAny);
}

TEST(ParserSection9, ForkJoinNone) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      #10 a = 1;\n"
      "    join_none\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoinNone);
}

// =============================================================================
// LRM section 9.4.1 -- Delay control (#)
// =============================================================================

TEST(ParserSection9, DelayControl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    #10 a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDelay);
  EXPECT_NE(stmt->delay, nullptr);
  EXPECT_NE(stmt->body, nullptr);
}

// =============================================================================
// LRM section 9.4.2 -- Event control (@)
// =============================================================================

TEST(ParserSection9, EventControlPosedgeKind) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(posedge clk) a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_NE(stmt->body, nullptr);
}

TEST(ParserSection9, EventControlPosedgeEdge) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(posedge clk) a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_FALSE(stmt->events.empty());
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
}

TEST(ParserSection9, EventControlNegedge) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(negedge rst) a = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_FALSE(stmt->events.empty());
  EXPECT_EQ(stmt->events[0].edge, Edge::kNegedge);
}

TEST(ParserSection9, EventControlMultiple) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(posedge clk or negedge rst) a = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_GE(stmt->events.size(), 2u);
  const Edge kExpectedEdges[] = {Edge::kPosedge, Edge::kNegedge};
  for (size_t i = 0; i < 2; ++i) {
    EXPECT_EQ(stmt->events[i].edge, kExpectedEdges[i]);
  }
}

TEST(ParserSection9, EventControlComma) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(posedge clk, negedge rst) a = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_GE(stmt->events.size(), 2u);
}

// =============================================================================
// LRM section 9.4.3 -- Wait statement
// =============================================================================

TEST(ParserSection9, WaitStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait (done == 1) a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
  EXPECT_NE(stmt->condition, nullptr);
  EXPECT_NE(stmt->body, nullptr);
}

// =============================================================================
// LRM section 9.4.2.2 -- @* and @(*) implicit event list
// =============================================================================

TEST(ParserSection9, StarEventBareAlways) {
  // always @* consumes the @* at the always-block level; body is the stmt.
  auto r = Parse(
      "module m;\n"
      "  always @* a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->sensitivity.empty());
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlockingAssign);
}

TEST(ParserSection9, StarEventParenAlways) {
  // always @(*) consumes the @(*) at the always-block level.
  auto r = Parse(
      "module m;\n"
      "  always @(*) begin a = b; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->sensitivity.empty());
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
}

TEST(ParserSection9, StarEventBareStmt) {
  // @* at the statement level produces an kEventControl stmt.
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @* a = b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_TRUE(stmt->is_star_event);
  EXPECT_TRUE(stmt->events.empty());
}

TEST(ParserSection9, StarEventParenStmt) {
  // @(*) at the statement level produces an kEventControl stmt.
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(*) a = b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_TRUE(stmt->is_star_event);
  EXPECT_TRUE(stmt->events.empty());
}

// =============================================================================
// LRM section 9.4.2 -- iff guards on event expressions
// =============================================================================

TEST(ParserSection9, IffGuardPosedgeEdge) {
  auto r = Parse(
      "module m;\n"
      "  reg clk, reset, a, b;\n"
      "  always @(posedge clk iff reset == 0) a <= b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  // iff guard goes through always-block sensitivity path.
  ASSERT_EQ(item->sensitivity.size(), 1u);
  EXPECT_EQ(item->sensitivity[0].edge, Edge::kPosedge);
}

TEST(ParserSection9, IffGuardPosedgeFields) {
  auto r = Parse(
      "module m;\n"
      "  reg clk, reset, a, b;\n"
      "  always @(posedge clk iff reset == 0) a <= b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 1u);
  EXPECT_NE(item->sensitivity[0].signal, nullptr);
  EXPECT_NE(item->sensitivity[0].iff_condition, nullptr);
}

TEST(ParserSection9, IffGuardNoEdge) {
  auto r = Parse(
      "module m;\n"
      "  reg clk, en, a, b;\n"
      "  always @(clk iff en) a <= b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 1u);
  EXPECT_EQ(item->sensitivity[0].edge, Edge::kNone);
  EXPECT_NE(item->sensitivity[0].iff_condition, nullptr);
}

TEST(ParserSection9, IffGuardMultipleEventsFirst) {
  auto r = Parse(
      "module m;\n"
      "  reg clk, reset, a, b;\n"
      "  always @(posedge clk iff reset == 0 or negedge reset) a <= b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 2u);
  EXPECT_NE(item->sensitivity[0].iff_condition, nullptr);
}

TEST(ParserSection9, IffGuardMultipleEventsSecond) {
  auto r = Parse(
      "module m;\n"
      "  reg clk, reset, a, b;\n"
      "  always @(posedge clk iff reset == 0 or negedge reset) a <= b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 2u);
  EXPECT_EQ(item->sensitivity[1].iff_condition, nullptr);
  EXPECT_EQ(item->sensitivity[1].edge, Edge::kNegedge);
}

TEST(ParserSection9, IffGuardStmtLevelKind) {
  auto r = Parse(
      "module m;\n"
      "  reg clk, reset, a, b;\n"
      "  initial @(posedge clk iff reset == 0) a <= b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_EQ(stmt->events.size(), 1u);
}

TEST(ParserSection9, IffGuardStmtLevelEvent) {
  auto r = Parse(
      "module m;\n"
      "  reg clk, reset, a, b;\n"
      "  initial @(posedge clk iff reset == 0) a <= b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_EQ(stmt->events.size(), 1u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
  EXPECT_NE(stmt->events[0].iff_condition, nullptr);
}

// =============================================================================
// LRM section 9.6.1 -- wait fork
// =============================================================================

TEST(ParserSection9, WaitFork) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      #10;\n"
      "    join_none\n"
      "    wait fork;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 2u);
  auto *wf = body->stmts[1];
  EXPECT_EQ(wf->kind, StmtKind::kWaitFork);
}

TEST(ParserSection9, WaitExprStillWorks) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait (done) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
}

// =============================================================================
// LRM section 9.6.3 -- disable fork
// =============================================================================

TEST(ParserSection9, DisableFork) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      #10;\n"
      "    join_none\n"
      "    disable fork;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 2u);
  auto *df = body->stmts[1];
  EXPECT_EQ(df->kind, StmtKind::kDisableFork);
}

TEST(ParserSection9, DisableIdentStillWorks) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    disable my_block;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDisable);
}

// =============================================================================
// LRM section 9.4.5 -- repeat event control
// =============================================================================

TEST(ParserSection9, RepeatEventControl) {
  auto r = Parse(
      "module m;\n"
      "  reg clk, a, b;\n"
      "  initial a = repeat(3) @(posedge clk) b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_NE(stmt->repeat_event_count, nullptr);
  EXPECT_FALSE(stmt->events.empty());
}

TEST(ParserSection9, RepeatEventControlNonblocking) {
  auto r = Parse(
      "module m;\n"
      "  reg clk, a, b;\n"
      "  initial a <= repeat(2) @(posedge clk) b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  EXPECT_NE(stmt->repeat_event_count, nullptr);
  EXPECT_FALSE(stmt->events.empty());
}

// =============================================================================
// §9.3.5 -- Statement labels
// =============================================================================

TEST(ParserSection9, StatementLabelOnBeginBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    name: begin\n"
      "      a = 1;\n"
      "    end: name\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  EXPECT_EQ(item->body->label, "name");
}

TEST(ParserSection9, StatementLabelOnForkBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    name: fork\n"
      "      a = 1;\n"
      "    join: name\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->label, "name");
}

// =============================================================================
// §9.4.2 -- edge keyword in event control
// =============================================================================

TEST(ParserSection9, EventControlEdge) {
  auto r = Parse(
      "module m;\n"
      "  reg [3:0] a;\n"
      "  wire clk;\n"
      "  always @(edge clk) a = ~a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->sensitivity.size(), 1u);
  EXPECT_EQ(item->sensitivity[0].edge, Edge::kEdge);
}

// =============================================================================
// §7.5.1 / §8.7 -- new[N] dynamic array constructor
// =============================================================================

TEST(ParserSection9, DynamicArrayNew) {
  auto r = Parse(
      "module m;\n"
      "  int arr[];\n"
      "  initial arr = new[5];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

// =============================================================================
// §9.3.1 -- automatic variable declarations in fork blocks
// =============================================================================

TEST(ParserSection9, AutomaticVarInFork) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      automatic int k = 0;\n"
      "      begin k = 1; end\n"
      "    join_none\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  ASSERT_GE(stmt->fork_stmts.size(), 1u);
  EXPECT_EQ(stmt->fork_stmts[0]->kind, StmtKind::kVarDecl);
}
