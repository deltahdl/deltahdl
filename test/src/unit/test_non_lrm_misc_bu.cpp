// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

struct ParseResult9c {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult9c Parse(const std::string& src) {
  ParseResult9c result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static ModuleItem* FirstAlwaysItem(ParseResult9c& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysBlock) return item;
  }
  return nullptr;
}

static Stmt* FirstInitialStmt(ParseResult9c& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kInitialBlock) continue;
    if (item->body && item->body->kind == StmtKind::kBlock) {
      return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
    }
    return item->body;
  }
  return nullptr;
}

static bool HasItemKind(ParseResult9c& r, ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return true;
  }
  return false;
}

namespace {

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
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  ASSERT_GE(stmt->fork_stmts.size(), 1u);
  EXPECT_EQ(stmt->fork_stmts[0]->kind, StmtKind::kVarDecl);
}

// =============================================================================
// §9.3.5 -- Statement labels (additional tests)
// =============================================================================
TEST(ParserSection9, StatementLabelOnAssignment) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    my_label: a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->label, "my_label");
}

TEST(ParserSection9, StatementLabelOnIf) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    check: if (x) a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->label, "check");
}

TEST(ParserSection9, StatementLabelOnForLoop) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    loop: for (int i = 0; i < 10; i++) a = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
}

// =============================================================================
// §9.4.4 -- Level-sensitive sequence controls
// =============================================================================
TEST(ParserSection9, WaitSequenceTriggered) {
  auto r = Parse(
      "module m;\n"
      "  sequence abc;\n"
      "    @(posedge clk) a ##1 b ##1 c;\n"
      "  endsequence\n"
      "  initial begin\n"
      "    wait(abc.triggered);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ParserSection9, WaitSequenceTriggeredOr) {
  auto r = Parse(
      "module m;\n"
      "  sequence s1;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "  sequence s2;\n"
      "    @(negedge clk) c ##1 d;\n"
      "  endsequence\n"
      "  initial begin\n"
      "    wait(s1.triggered || s2.triggered);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ParserSection9, WaitSequenceTriggeredIfCheck) {
  auto r = Parse(
      "module m;\n"
      "  sequence abc;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "  initial begin\n"
      "    wait(abc.triggered);\n"
      "    if (abc.triggered) $display(\"ok\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

// =============================================================================
// §9.6.2 -- Disable statement (additional tests)
// =============================================================================
TEST(ParserSection9, DisableNamedBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : blk\n"
      "    disable blk;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kDisable);
}

TEST(ParserSection9, DisableTaskName) {
  auto r = Parse(
      "module m;\n"
      "  task my_task;\n"
      "  endtask\n"
      "  initial begin\n"
      "    disable my_task;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDisable);
}

TEST(ParserSection9, DisableForkAfterJoinNone) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      #100;\n"
      "    join_none\n"
      "    #50;\n"
      "    disable fork;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 3u);
  EXPECT_EQ(body->stmts[2]->kind, StmtKind::kDisableFork);
}

// =============================================================================
// LRM section 9.4 -- Procedural timing controls (additional coverage)
// =============================================================================
TEST(ParserSection9, DelayControlReal) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    #3.5 a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDelay);
  EXPECT_NE(stmt->delay, nullptr);
}

TEST(ParserSection9, EventControlBareSignal) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(data) a = data;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_FALSE(stmt->events.empty());
  EXPECT_EQ(stmt->events[0].edge, Edge::kNone);
}

TEST(ParserSection9, WaitStatementWithBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait (ready) begin\n"
      "      a = 1;\n"
      "      b = 2;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
  EXPECT_NE(stmt->condition, nullptr);
  ASSERT_NE(stmt->body, nullptr);
  EXPECT_EQ(stmt->body->kind, StmtKind::kBlock);
}

// =============================================================================
// LRM section 9.3.1 -- Sequential blocks (additional tests)
// =============================================================================
TEST(ParserSection9, SequentialBlockNamedBeginEnd) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : my_seq\n"
      "    a = 1;\n"
      "    b = 2;\n"
      "  end : my_seq\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  EXPECT_EQ(item->body->label, "my_seq");
  EXPECT_EQ(item->body->stmts.size(), 2u);
}

TEST(ParserSection9, SequentialBlockVarDecl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int temp;\n"
      "    temp = 42;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  ASSERT_GE(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
}

TEST(ParserSection9, SequentialBlockNestedBeginEnd) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    begin\n"
      "      a = 1;\n"
      "    end\n"
      "    begin\n"
      "      b = 2;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kBlock);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kBlock);
}

TEST(ParserSection9, SequentialBlockMultipleVarDecls) {
  auto r = Parse(
      "module m;\n"
      "  initial begin int x; logic [7:0] y; x = 1; end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 3u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kVarDecl);
}

// =============================================================================
// LRM section 9.3.2 -- Parallel blocks (additional tests)
// =============================================================================
TEST(ParserSection9, ParallelBlockNamedForkJoin) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork : par_blk\n"
      "      #10 a = 1;\n"
      "      #20 b = 2;\n"
      "    join : par_blk\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->label, "par_blk");
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoin);
}

TEST(ParserSection9, ParallelBlockVarDeclInFork) {
  auto r = Parse(
      "module m;\n"
      "  initial fork\n"
      "    int local_var;\n"
      "    begin local_var = 1; end\n"
      "  join\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  ASSERT_GE(stmt->fork_stmts.size(), 1u);
}

TEST(ParserSection9, ParallelBlockNestedBeginInFork) {
  auto r = Parse(
      "module m;\n"
      "  initial fork\n"
      "    begin #10 a = 1; #20 a = 2; end\n"
      "    begin #15 b = 3; end\n"
      "  join\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  ASSERT_EQ(stmt->fork_stmts.size(), 2u);
  EXPECT_EQ(stmt->fork_stmts[0]->kind, StmtKind::kBlock);
  EXPECT_EQ(stmt->fork_stmts[1]->kind, StmtKind::kBlock);
}

// =============================================================================
// Section 9.7 -- Fine-grain process control
// =============================================================================
TEST(ParserSection9b, WaitForkStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      #10 a = 1;\n"
      "    join_none\n"
      "    wait fork;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kWaitFork);
}

TEST(ParserSection9b, DisableForkStatement) {
  auto r = Parse(
      "module m;\n"
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
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kDisableFork);
}

TEST(ParserSection9b, ForkJoinNoneWithWaitFork) {
  auto r = Parse(
      "module m;\n"
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
  auto r = Parse(
      "module m;\n"
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
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  auto* fork_stmt = body->stmts[0];
  EXPECT_EQ(fork_stmt->kind, StmtKind::kFork);
  EXPECT_EQ(fork_stmt->join_kind, TokenKind::kKwJoinAny);
}

// =============================================================================
// §9.2 -- Structured procedures (initial, always, final)
// =============================================================================
TEST(ParserSection9b, StructuredProcInitialAndAlways) {
  auto r = Parse(
      "module m;\n"
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
  auto r = Parse(
      "module m;\n"
      "  final $display(\"done\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kFinalBlock);
}

TEST(ParserSection9b, StructuredProcMultipleInitial) {
  auto r = Parse(
      "module m;\n"
      "  initial a = 0;\n"
      "  initial b = 1;\n"
      "  initial c = 2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock) count++;
  }
  EXPECT_EQ(count, 3);
}

// =============================================================================
// §9.2.2 -- always_comb procedure
// =============================================================================
TEST(ParserSection9b, AlwaysCombWithAssertion) {
  auto r = Parse(
      "module m;\n"
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
  auto r = Parse(
      "module m;\n"
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
  auto r = Parse(
      "module m;\n"
      "  always @(a iff enable == 1)\n"
      "    y <= a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_GE(item->sensitivity.size(), 1u);
  EXPECT_NE(item->sensitivity[0].iff_condition, nullptr);
}

TEST(ParserSection9b, ConditionalEventIffWithEdge) {
  auto r = Parse(
      "module m;\n"
      "  always @(posedge clk iff reset == 0)\n"
      "    q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_GE(item->sensitivity.size(), 1u);
  EXPECT_EQ(item->sensitivity[0].edge, Edge::kPosedge);
  EXPECT_NE(item->sensitivity[0].iff_condition, nullptr);
}

TEST(ParserSection9b, ConditionalEventIffMultipleEvents) {
  auto r = Parse(
      "module m;\n"
      "  always @(posedge clk iff en or negedge rst)\n"
      "    q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_GE(item->sensitivity.size(), 2u);
}

// =============================================================================
// §9.4.2.4 -- Sequence events
// =============================================================================
TEST(ParserSection9b, SequenceEventInEventControl) {
  auto r = Parse(
      "module m;\n"
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
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait (!enable) #10 a = b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
}

TEST(ParserSection9b, WaitStatementExpression) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait (done == 1) $display(\"done\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
  EXPECT_NE(stmt->condition, nullptr);
}

// =============================================================================
// §10.4.1 -- Blocking procedural assignments
// =============================================================================
TEST(ParserSection9b, BlockingAssignSimple) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    rega = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ParserSection9b, BlockingAssignBitSelect) {
  auto r = Parse(
      "module m;\n"
      "  initial rega[3] = 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kSelect);
}

TEST(ParserSection9b, BlockingAssignPartSelect) {
  auto r = Parse(
      "module m;\n"
      "  initial rega[3:5] = 7;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(ParserSection9b, BlockingAssignConcatLhs) {
  auto r = Parse(
      "module m;\n"
      "  initial {carry, acc} = rega + regb;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(stmt->lhs, nullptr);
  EXPECT_EQ(stmt->lhs->kind, ExprKind::kConcatenation);
}

TEST(ParserSection9b, BlockingAssignCompound) {
  auto r = Parse(
      "module m;\n"
      "  initial x += 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

// =============================================================================
// §10.4.2 -- Nonblocking procedural assignments
// =============================================================================
TEST(ParserSection9b, NonblockingAssignSimple) {
  auto r = Parse(
      "module m;\n"
      "  initial q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
}

TEST(ParserSection9b, NonblockingAssignWithDelay) {
  auto r = Parse(
      "module m;\n"
      "  initial q <= #5 d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  EXPECT_NE(stmt->delay, nullptr);
}

TEST(ParserSection9b, NonblockingAssignMultiple) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a <= b;\n"
      "    b <= a;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kNonblockingAssign);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kNonblockingAssign);
}

TEST(ParserSection9b, NonblockingAssignWithEventControl) {
  auto r = Parse(
      "module m;\n"
      "  initial a <= @(posedge clk) b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
}

// =============================================================================
// LRM section 9.2 -- Structured procedures overview
// Multiple initial/always procedures coexist within a module.
// =============================================================================
TEST(ParserSection9c, MultipleInitialProcedures) {
  auto r = Parse(
      "module m;\n"
      "  initial a = 0;\n"
      "  initial b = 1;\n"
      "  initial c = 2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock) ++count;
  }
  EXPECT_EQ(count, 3);
}

TEST(ParserSection9c, MixedProcedureTypes) {
  auto r = Parse(
      "module m;\n"
      "  initial a = 0;\n"
      "  always @(posedge clk) q <= d;\n"
      "  final $display(\"done\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kInitialBlock));
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAlwaysBlock));
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kFinalBlock));
}

// =============================================================================
// LRM section 9.2.2.2 -- always_comb procedure
// Combinational logic with begin/end block and multiple statements.
// =============================================================================
TEST(ParserSection9c, AlwaysCombBeginEnd) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, c, y;\n"
      "  always_comb begin\n"
      "    a = b & c;\n"
      "    y = a | b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysComb);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  EXPECT_GE(item->body->stmts.size(), 2u);
}

TEST(ParserSection9c, AlwaysCombWithIf) {
  auto r = Parse(
      "module m;\n"
      "  logic sel, a, b, y;\n"
      "  always_comb\n"
      "    if (sel) y = a;\n"
      "    else y = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysComb);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kIf);
}

TEST(ParserSection9c, AlwaysCombCaseStatement) {
  auto r = Parse(
      "module m;\n"
      "  logic [1:0] sel;\n"
      "  logic [3:0] y;\n"
      "  always_comb\n"
      "    case (sel)\n"
      "      2'b00: y = 4'h0;\n"
      "      2'b01: y = 4'h1;\n"
      "      default: y = 4'hf;\n"
      "    endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysComb);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kCase);
}

// =============================================================================
// LRM section 9.2.2.3 -- always_latch procedure
// Latched logic behavior modeled with always_latch.
// =============================================================================
TEST(ParserSection9c, AlwaysLatchWithBeginEnd) {
  auto r = Parse(
      "module m;\n"
      "  logic ck, d, q;\n"
      "  always_latch begin\n"
      "    if (ck) q <= d;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysLatch);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
}

}  // namespace
