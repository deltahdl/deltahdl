#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult9b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

static ParseResult9b Parse(const std::string &src) {
  ParseResult9b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static Stmt *FirstInitialStmt(ParseResult9b &r) {
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

// =============================================================================
// Section 9.7 -- Fine-grain process control
// =============================================================================

TEST(ParserSection9b, WaitForkStatement) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    fork\n"
                 "      #10 a = 1;\n"
                 "    join_none\n"
                 "    wait fork;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kWaitFork);
}

TEST(ParserSection9b, DisableForkStatement) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    fork\n"
                 "      #10 a = 1;\n"
                 "      #20 b = 1;\n"
                 "    join_any\n"
                 "    disable fork;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kDisableFork);
}

TEST(ParserSection9b, ForkJoinNoneWithWaitFork) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    fork\n"
                 "      begin #10 a = 1; end\n"
                 "      begin #20 b = 1; end\n"
                 "    join_none\n"
                 "    wait fork;\n"
                 "    $display(\"all done\");\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserSection9b, ForkJoinAnyWithDisableFork) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    fork\n"
                 "      @(posedge clk) a = 1;\n"
                 "      #100 a = 0;\n"
                 "    join_any\n"
                 "    disable fork;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  auto *fork_stmt = body->stmts[0];
  EXPECT_EQ(fork_stmt->kind, StmtKind::kFork);
  EXPECT_EQ(fork_stmt->join_kind, TokenKind::kKwJoinAny);
}

static ModuleItem *FirstAlwaysItem(ParseResult9b &r) {
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

// =============================================================================
// §9.2 -- Structured procedures (initial, always, final)
// =============================================================================

TEST(ParserSection9b, StructuredProcInitialAndAlways) {
  auto r = Parse("module m;\n"
                 "  initial a = 0;\n"
                 "  always #5 clk = ~clk;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kInitialBlock);
  EXPECT_EQ(r.cu->modules[0]->items[1]->kind, ModuleItemKind::kAlwaysBlock);
}

TEST(ParserSection9b, StructuredProcFinalBlock) {
  auto r = Parse("module m;\n"
                 "  final $display(\"done\");\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kFinalBlock);
}

TEST(ParserSection9b, StructuredProcMultipleInitial) {
  auto r = Parse("module m;\n"
                 "  initial a = 0;\n"
                 "  initial b = 1;\n"
                 "  initial c = 2;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock)
      count++;
  }
  EXPECT_EQ(count, 3);
}

// =============================================================================
// §9.2.2 -- always_comb procedure
// =============================================================================

TEST(ParserSection9b, AlwaysCombWithAssertion) {
  auto r = Parse("module m;\n"
                 "  always_comb begin\n"
                 "    a = b & c;\n"
                 "    assert (a != 0);\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// §9.2.2.4 -- always_ff procedure
// =============================================================================

TEST(ParserSection9b, AlwaysLatchMultipleOutputs) {
  auto r = Parse("module m;\n"
                 "  always_latch begin\n"
                 "    if (en) begin\n"
                 "      q1 <= d1;\n"
                 "      q2 <= d2;\n"
                 "    end\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// §9.4.2.3 -- Conditional event controls (iff)
// =============================================================================

TEST(ParserSection9b, ConditionalEventIffBasic) {
  auto r = Parse("module m;\n"
                 "  always @(a iff enable == 1)\n"
                 "    y <= a;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_GE(item->sensitivity.size(), 1u);
  EXPECT_NE(item->sensitivity[0].iff_condition, nullptr);
}

TEST(ParserSection9b, ConditionalEventIffWithEdge) {
  auto r = Parse("module m;\n"
                 "  always @(posedge clk iff reset == 0)\n"
                 "    q <= d;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_GE(item->sensitivity.size(), 1u);
  EXPECT_EQ(item->sensitivity[0].edge, Edge::kPosedge);
  EXPECT_NE(item->sensitivity[0].iff_condition, nullptr);
}

TEST(ParserSection9b, ConditionalEventIffMultipleEvents) {
  auto r = Parse("module m;\n"
                 "  always @(posedge clk iff en or negedge rst)\n"
                 "    q <= d;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_GE(item->sensitivity.size(), 2u);
}

// =============================================================================
// §9.4.2.4 -- Sequence events
// =============================================================================

TEST(ParserSection9b, SequenceEventInEventControl) {
  auto r = Parse("module m;\n"
                 "  sequence abc;\n"
                 "    @(posedge clk) a ##1 b ##1 c;\n"
                 "  endsequence\n"
                 "  initial @(abc) $display(\"match\");\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// §9.4.3 / §9.4.2.4 -- Wait statement
// =============================================================================

TEST(ParserSection9b, WaitStatementBasic) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    wait (!enable) #10 a = b;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
}

TEST(ParserSection9b, WaitStatementExpression) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    wait (done == 1) $display(\"done\");\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
  EXPECT_NE(stmt->condition, nullptr);
}

TEST(ParserSection9b, WaitStatementWithBlock) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    wait (ready) begin\n"
                 "      a = 1;\n"
                 "      b = 2;\n"
                 "    end\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// §10.4.1 -- Blocking procedural assignments
// =============================================================================

TEST(ParserSection9b, BlockingAssignSimple) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    rega = 0;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ParserSection9b, BlockingAssignBitSelect) {
  auto r = Parse("module m;\n"
                 "  initial rega[3] = 1;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
}

TEST(ParserSection9b, BlockingAssignPartSelect) {
  auto r = Parse("module m;\n"
                 "  initial rega[3:5] = 7;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ParserSection9b, BlockingAssignConcatLhs) {
  auto r = Parse("module m;\n"
                 "  initial {carry, acc} = rega + regb;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kConcatenation);
}

TEST(ParserSection9b, BlockingAssignCompound) {
  auto r = Parse("module m;\n"
                 "  initial x += 1;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

// =============================================================================
// §10.4.2 -- Nonblocking procedural assignments
// =============================================================================

TEST(ParserSection9b, NonblockingAssignSimple) {
  auto r = Parse("module m;\n"
                 "  initial q <= d;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
}

TEST(ParserSection9b, NonblockingAssignWithDelay) {
  auto r = Parse("module m;\n"
                 "  initial q <= #5 d;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  EXPECT_NE(stmt->delay, nullptr);
}

TEST(ParserSection9b, NonblockingAssignMultiple) {
  auto r = Parse("module m;\n"
                 "  initial begin\n"
                 "    a <= b;\n"
                 "    b <= a;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kNonblockingAssign);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kNonblockingAssign);
}

TEST(ParserSection9b, NonblockingAssignWithEventControl) {
  auto r = Parse("module m;\n"
                 "  initial a <= @(posedge clk) b;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
}
