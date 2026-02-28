// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

struct ParseResult9d {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult9d Parse(const std::string& src) {
  ParseResult9d result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static Stmt* FirstInitialBody(ParseResult9d& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock) return item->body;
  }
  return nullptr;
}

static Stmt* FirstInitialStmt(ParseResult9d& r) {
  auto* body = FirstInitialBody(r);
  if (body && body->kind == StmtKind::kBlock) {
    return body->stmts.empty() ? nullptr : body->stmts[0];
  }
  return body;
}

static ModuleItem* FirstAlwaysItem(ParseResult9d& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kAlwaysBlock ||
        item->kind == ModuleItemKind::kAlwaysCombBlock ||
        item->kind == ModuleItemKind::kAlwaysFFBlock ||
        item->kind == ModuleItemKind::kAlwaysLatchBlock) {
      return item;
    }
  }
  return nullptr;
}

namespace {

// =============================================================================
// LRM section 9.3.1 -- Sequential blocks
// Block-level variable declarations (block_item_declaration).
// =============================================================================
TEST(ParserSection9c, SequentialBlockWithLocalVarDecl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int x;\n"
      "    x = 5;\n"
      "    $display(\"%0d\", x);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  ASSERT_GE(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
}

TEST(ParserSection9c, SequentialBlockMultipleLocalVars) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int a;\n"
      "    int b;\n"
      "    a = 1;\n"
      "    b = a + 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 4u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kVarDecl);
}

TEST(ParserSection9c, SequentialBlockNamedWithDecls) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : my_block\n"
      "    integer count;\n"
      "    count = 0;\n"
      "  end : my_block\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  EXPECT_EQ(body->label, "my_block");
}

// =============================================================================
// LRM section 9.3.5 -- Statement labels (additional)
// Labels on while loops, case statements, and disabling labeled stmts.
// =============================================================================
TEST(ParserSection9c, StatementLabelOnWhile) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    spin: while (busy) @(posedge clk);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->label, "spin");
}

TEST(ParserSection9c, StatementLabelOnCase) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    decode: case (op)\n"
      "      0: a = 1;\n"
      "      1: a = 2;\n"
      "      default: a = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->label, "decode");
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
}

TEST(ParserSection9c, DisableLabeledBlock) {
  // LRM 9.6.2 example: block disables itself using its name.
  auto r = Parse(
      "module m;\n"
      "  initial begin : block_name\n"
      "    a = b;\n"
      "    disable block_name;\n"
      "    c = a;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->label, "block_name");
  ASSERT_GE(body->stmts.size(), 3u);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kDisable);
}

// =============================================================================
// LRM section 9.4 -- Procedural timing controls
// Zero-delay, chained delays, delay expressions.
// =============================================================================
TEST(ParserSection9c, ZeroDelayControl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    #0 a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDelay);
  EXPECT_NE(stmt->delay, nullptr);
}

TEST(ParserSection9c, ChainedDelayControls) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    #5 a = 0;\n"
      "    #10 a = 1;\n"
      "    #15 a = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 3u);
  for (size_t i = 0; i < 3; ++i) {
    EXPECT_EQ(body->stmts[i]->kind, StmtKind::kDelay);
  }
}

TEST(ParserSection9c, DelayWithExpression) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    #(a + b) c = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDelay);
  EXPECT_NE(stmt->delay, nullptr);
}

// =============================================================================
// LRM section 9.4.2 -- Event control
// Named event trigger and bare @identifier event control.
// =============================================================================
TEST(ParserSection9c, EventControlAtIdentifier) {
  // @clk shorthand for @(clk)
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @clk a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
}

TEST(ParserSection9c, EventControlMultipleOrExpressions) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(a or b or c) x = a + b + c;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_GE(stmt->events.size(), 3u);
}

TEST(ParserSection9c, EventControlMixedEdgesComma) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(posedge clk, negedge rst, a) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  ASSERT_GE(stmt->events.size(), 3u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kPosedge);
  EXPECT_EQ(stmt->events[1].edge, Edge::kNegedge);
  EXPECT_EQ(stmt->events[2].edge, Edge::kNone);
}

TEST(ParserSection9c, SequenceEventParenthesized) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s1;\n"
              "    @(posedge clk) a ##1 b;\n"
              "  endsequence\n"
              "  initial begin\n"
              "    @(s1) $display(\"matched\");\n"
              "  end\n"
              "endmodule\n"));
}

// =============================================================================
// LRM section 9.4.4 -- Level-sensitive sequence controls
// Wait on sequence.triggered to synchronize with sequence end point.
// =============================================================================
TEST(ParserSection9c, WaitSequenceTriggeredWithAction) {
  // After wait(seq.triggered), execute a procedural statement.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence req_ack;\n"
              "    @(posedge clk) req ##[1:5] ack;\n"
              "  endsequence\n"
              "  initial begin\n"
              "    wait(req_ack.triggered);\n"
              "    $display(\"handshake complete\");\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection9c, WaitTriggeredInLoop) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s;\n"
              "    @(posedge clk) a ##1 b;\n"
              "  endsequence\n"
              "  initial begin\n"
              "    forever begin\n"
              "      wait(s.triggered);\n"
              "      count = count + 1;\n"
              "      @(posedge clk);\n"
              "    end\n"
              "  end\n"
              "endmodule\n"));
}

// =============================================================================
// LRM section 9.6.2 -- Disable statement
// Disable named blocks and tasks from within and outside.
// =============================================================================
TEST(ParserSection9c, DisableBlockFromOutside) {
  // LRM 9.6.2 example 3: disable a named block from an always procedure.
  auto r = Parse(
      "module m;\n"
      "  initial begin : outer\n"
      "    forever begin\n"
      "      @(posedge clk) x = x + 1;\n"
      "    end\n"
      "  end\n"
      "  initial begin\n"
      "    #100;\n"
      "    disable outer;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  // The second initial block should contain a disable statement.
  auto* second_init = r.cu->modules[0]->items[1];
  ASSERT_NE(second_init, nullptr);
  ASSERT_NE(second_init->body, nullptr);
  ASSERT_GE(second_init->body->stmts.size(), 2u);
  EXPECT_EQ(second_init->body->stmts[1]->kind, StmtKind::kDisable);
}

TEST(ParserSection9c, DisableWithIfCondition) {
  // LRM 9.6.2 example 2: conditional disable as a forward goto.
  auto r = Parse(
      "module m;\n"
      "  initial begin : block_name\n"
      "    a = 1;\n"
      "    if (a == 0)\n"
      "      disable block_name;\n"
      "    b = 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->label, "block_name");
  ASSERT_GE(body->stmts.size(), 3u);
  // The if statement contains the disable.
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kIf);
}

TEST(ParserSection9c, DisableHierarchicalTaskName) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  task my_task;\n"
              "    begin\n"
              "      #100 x = 1;\n"
              "    end\n"
              "  endtask\n"
              "  initial begin\n"
              "    fork\n"
              "      my_task;\n"
              "    join_none\n"
              "    #50 disable my_task;\n"
              "  end\n"
              "endmodule\n"));
}

// =============================================================================
// LRM section 9.7 -- Fine-grain process control
// The process class: self(), status(), kill(), await(), suspend(), resume().
// =============================================================================
TEST(ParserSection9c, ProcessSelfAssignment) {
  // process p = process::self(); is valid usage.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    process p;\n"
              "    p = process::self();\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection9c, ProcessKillCall) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    process p;\n"
              "    p = process::self();\n"
              "    fork\n"
              "      begin\n"
              "        #100;\n"
              "      end\n"
              "    join_none\n"
              "    p.kill();\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection9c, ProcessStatusCheck) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    process p;\n"
              "    p = process::self();\n"
              "    if (p.status() != process::FINISHED)\n"
              "      $display(\"still running\");\n"
              "  end\n"
              "endmodule\n"));
}

// =============================================================================
// LRM section 9.2.2.4 -- always_ff procedure
// Sequential logic with reset and multiple sensitivity list items.
// =============================================================================
TEST(ParserSection9c, AlwaysFFWithReset) {
  // LRM example: always_ff @(posedge clock iff reset == 0 or posedge reset)
  auto r = Parse(
      "module m;\n"
      "  logic clock, reset;\n"
      "  logic [7:0] r1, r2;\n"
      "  always_ff @(posedge clock iff reset == 0 or posedge reset) begin\n"
      "    r1 <= reset ? 0 : r2 + 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysFF);
  ASSERT_EQ(item->sensitivity.size(), 2u);
  EXPECT_EQ(item->sensitivity[0].edge, Edge::kPosedge);
  EXPECT_NE(item->sensitivity[0].iff_condition, nullptr);
  EXPECT_EQ(item->sensitivity[1].edge, Edge::kPosedge);
  EXPECT_EQ(item->sensitivity[1].iff_condition, nullptr);
}

TEST(ParserSection9c, AlwaysFFSimplePosedge) {
  auto r = Parse(
      "module m;\n"
      "  logic clk;\n"
      "  logic [3:0] count;\n"
      "  always_ff @(posedge clk)\n"
      "    count <= count + 1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysFF);
  ASSERT_EQ(item->sensitivity.size(), 1u);
  EXPECT_EQ(item->sensitivity[0].edge, Edge::kPosedge);
}

// =============================================================================
// LRM section 9.3.1 -- Sequential blocks (additional)
// Nested blocks with names, and automatic variable lifetime in blocks.
// =============================================================================
TEST(ParserSection9c, NestedNamedSequentialBlocks) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : outer\n"
      "    begin : inner\n"
      "      a = 1;\n"
      "    end : inner\n"
      "  end : outer\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->label, "outer");
  ASSERT_GE(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kBlock);
  EXPECT_EQ(body->stmts[0]->label, "inner");
}

TEST(ParserSection9c, AutomaticVarDeclInBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    automatic int k = 5;\n"
      "    $display(\"%0d\", k);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_TRUE(body->stmts[0]->var_is_automatic);
}

// =============================================================================
// LRM section 9.4.2 -- Event control (additional edge cases)
// Null statement after event control, back-to-back event controls.
// =============================================================================
TEST(ParserSection9c, EventControlNullStatement) {
  // @(posedge clk); -- event control with null statement (just a semicolon)
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(posedge clk);\n"
      "    a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
}

TEST(ParserSection9c, BackToBackEventControls) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(posedge clk);\n"
      "    @(posedge clk);\n"
      "    a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 3u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kEventControl);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kEventControl);
}

// =============================================================================
// LRM section 9.4.2.3 -- Conditional event controls (iff)
// Additional iff guard tests for stmt-level and always_ff contexts.
// =============================================================================
TEST(ParserSection9c, IffGuardStmtLevelNoEdge) {
  // @(a iff enable == 1) - level-sensitive with iff qualifier
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(a iff enable == 1) y = a;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  ASSERT_EQ(stmt->events.size(), 1u);
  EXPECT_EQ(stmt->events[0].edge, Edge::kNone);
  EXPECT_NE(stmt->events[0].iff_condition, nullptr);
}

TEST(ParserSection9c, IffGuardAlwaysFF) {
  // always_ff with iff guard on the sensitivity.
  auto r = Parse(
      "module m;\n"
      "  logic clk, en;\n"
      "  logic [3:0] q, d;\n"
      "  always_ff @(posedge clk iff en) q <= d;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstAlwaysItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->always_kind, AlwaysKind::kAlwaysFF);
  ASSERT_EQ(item->sensitivity.size(), 1u);
  EXPECT_NE(item->sensitivity[0].iff_condition, nullptr);
}

// =============================================================================
// LRM section 9.2 -- Structured procedures (ParseOk smoke tests)
// Various procedure forms that should parse without errors.
// =============================================================================
TEST(ParserSection9c, InitialWithTaskCall) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  task my_task;\n"
              "    #10 a = 1;\n"
              "  endtask\n"
              "  initial begin\n"
              "    my_task;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection9c, AlwaysFFWithNegedge) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  always_ff @(negedge clk)\n"
              "    q <= d;\n"
              "endmodule\n"));
}

TEST(ParserSection9c, AlwaysCombWithFunctionCall) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  function logic [3:0] mux(input logic sel,\n"
              "                           input logic [3:0] a, b);\n"
              "    return sel ? a : b;\n"
              "  endfunction\n"
              "  logic sel;\n"
              "  logic [3:0] a, b, y;\n"
              "  always_comb y = mux(sel, a, b);\n"
              "endmodule\n"));
}

// =============================================================================
// LRM section 9.3.1 -- Sequential blocks (begin...end)
// Empty and minimal begin-end blocks.
// =============================================================================
TEST(ParserSection9, Sec9_3_1_EmptyBeginEnd) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  EXPECT_TRUE(body->stmts.empty());
}

TEST(ParserSection9, Sec9_3_1_NamedBeginEndMatchingLabel) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : seq_block\n"
      "    a = 1;\n"
      "  end : seq_block\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  EXPECT_EQ(body->label, "seq_block");
  EXPECT_EQ(body->stmts.size(), 1u);
}

TEST(ParserSection9, Sec9_3_1_NamedBeginEndNoEndLabel) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : blk_no_end\n"
      "    a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  EXPECT_EQ(body->label, "blk_no_end");
}

TEST(ParserSection9, Sec9_3_1_SingleStatementInBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = 42;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  ASSERT_EQ(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kBlockingAssign);
}

TEST(ParserSection9, Sec9_3_1_MultipleAssignmentsInBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "    b = 2;\n"
      "    c = 3;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->stmts.size(), 3u);
  for (size_t i = 0; i < 3; ++i) {
    EXPECT_EQ(body->stmts[i]->kind, StmtKind::kBlockingAssign);
  }
}

// =============================================================================
// LRM section 9.3.1 -- Variable declarations inside sequential blocks.
// =============================================================================
TEST(ParserSection9, Sec9_3_1_VarDeclAsFirstStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int temp;\n"
      "    temp = 99;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(body->stmts[0]->var_name, "temp");
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kBlockingAssign);
}

TEST(ParserSection9, Sec9_3_1_MultipleDifferentTypeVarDecls) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int x;\n"
      "    logic [7:0] y;\n"
      "    real z;\n"
      "    x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 4u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(body->stmts[2]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(body->stmts[3]->kind, StmtKind::kBlockingAssign);
}

TEST(ParserSection9, Sec9_3_1_VarDeclWithInitializer) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int count = 10;\n"
      "    $display(\"%0d\", count);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kVarDecl);
  EXPECT_EQ(body->stmts[0]->var_name, "count");
  EXPECT_NE(body->stmts[0]->var_init, nullptr);
}

// =============================================================================
// LRM section 9.3.1 -- Nested begin-end blocks.
// =============================================================================
TEST(ParserSection9, Sec9_3_1_NestedBeginEndTwoLevels) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a = 0;\n"
      "    begin\n"
      "      b = 1;\n"
      "      c = 2;\n"
      "    end\n"
      "    d = 3;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->stmts.size(), 3u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kBlock);
  EXPECT_EQ(body->stmts[1]->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[2]->kind, StmtKind::kBlockingAssign);
}

TEST(ParserSection9, Sec9_3_1_DeeplyNestedBeginEndThreeLevels) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    begin\n"
      "      begin\n"
      "        a = 1;\n"
      "      end\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->stmts.size(), 1u);
  auto* mid = body->stmts[0];
  EXPECT_EQ(mid->kind, StmtKind::kBlock);
  ASSERT_EQ(mid->stmts.size(), 1u);
  auto* inner = mid->stmts[0];
  EXPECT_EQ(inner->kind, StmtKind::kBlock);
  ASSERT_EQ(inner->stmts.size(), 1u);
  EXPECT_EQ(inner->stmts[0]->kind, StmtKind::kBlockingAssign);
}

TEST(ParserSection9, Sec9_3_1_NamedNestedBlocks) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : outer\n"
      "    begin : mid\n"
      "      begin : inner\n"
      "        x = 1;\n"
      "      end : inner\n"
      "    end : mid\n"
      "  end : outer\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->label, "outer");
  ASSERT_EQ(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->label, "mid");
  ASSERT_EQ(body->stmts[0]->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->stmts[0]->label, "inner");
}

// =============================================================================
// LRM section 9.3.1 -- Blocks with timing controls.
// =============================================================================
TEST(ParserSection9, Sec9_3_1_BlockWithDelayControl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    #5 a = 1;\n"
      "    #10 b = 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kDelay);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kDelay);
}

TEST(ParserSection9, Sec9_3_1_BlockWithEventControl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(posedge clk);\n"
      "    a = 1;\n"
      "    @(posedge clk);\n"
      "    b = 2;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->stmts.size(), 4u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kEventControl);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(body->stmts[2]->kind, StmtKind::kEventControl);
  EXPECT_EQ(body->stmts[3]->kind, StmtKind::kBlockingAssign);
}

// =============================================================================
// LRM section 9.3.1 -- Blocks with control flow statements.
// =============================================================================
TEST(ParserSection9, Sec9_3_1_BlockWithIfElse) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (sel)\n"
      "      a = 1;\n"
      "    else\n"
      "      a = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  EXPECT_NE(stmt->condition, nullptr);
  EXPECT_NE(stmt->then_branch, nullptr);
  EXPECT_NE(stmt->else_branch, nullptr);
}

TEST(ParserSection9, Sec9_3_1_BlockWithForLoop) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 8; i++)\n"
      "      data[i] = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_NE(stmt->for_cond, nullptr);
  EXPECT_NE(stmt->for_body, nullptr);
}

}  // namespace
