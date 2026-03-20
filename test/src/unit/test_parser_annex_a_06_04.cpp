#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(StatementSyntaxParsing, FunctionStatementOrNullWithNull) {
  auto r = Parse(
      "module m;\n"
      "  function void f();\n"
      "    ;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* func = FirstFunctionDecl(r);
  ASSERT_NE(func, nullptr);
  ASSERT_GE(func->func_body_stmts.size(), 1u);
  EXPECT_EQ(func->func_body_stmts[0]->kind, StmtKind::kNull);
}

TEST(StatementSyntaxParsing, FunctionStatementWithLabel) {
  auto r = Parse(
      "module m;\n"
      "  function void f();\n"
      "    step1: a = 1;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* func = FirstFunctionDecl(r);
  ASSERT_NE(func, nullptr);
  ASSERT_GE(func->func_body_stmts.size(), 1u);
  EXPECT_EQ(func->func_body_stmts[0]->label, "step1");
}

TEST(StatementSyntaxParsing, FunctionStatementWithAttribute) {
  auto r = Parse(
      "module m;\n"
      "  function void f();\n"
      "    (* inline *) a = 1;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* func = FirstFunctionDecl(r);
  ASSERT_NE(func, nullptr);
  ASSERT_GE(func->func_body_stmts.size(), 1u);
  EXPECT_FALSE(func->func_body_stmts[0]->attrs.empty());
  EXPECT_EQ(func->func_body_stmts[0]->attrs[0].name, "inline");
}

// --- Moved from test_parser_clause_12_03.cpp ---

TEST(StatementSyntaxParsing, NullStatementAsInitialBody) {
  auto r = Parse(
      "module m;\n"
      "  initial ;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItem(r.cu->modules[0]->items, ModuleItemKind::kInitialBlock);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kNull);
}

TEST(StatementSyntaxParsing, NullStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    ;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(body->kind, StmtKind::kBlock);
  ASSERT_GE(body->stmts.size(), 1u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kNull);
}

TEST(StatementSyntaxParsing, NullStatementWithAttribute) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    (* synthesis *) ;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 1u);
  auto* stmt = body->stmts[0];
  EXPECT_EQ(stmt->kind, StmtKind::kNull);
  EXPECT_FALSE(stmt->attrs.empty());
  EXPECT_EQ(stmt->attrs[0].name, "synthesis");
}

TEST(StatementSyntaxParsing, MultipleNullStatements) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    ;\n"
      "    ;\n"
      "    ;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = InitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 3u);
  EXPECT_EQ(body->stmts[0]->kind, StmtKind::kNull);
  EXPECT_EQ(body->stmts[1]->kind, StmtKind::kNull);
  EXPECT_EQ(body->stmts[2]->kind, StmtKind::kNull);
}

TEST(StatementSyntaxParsing, StatementWithAttribute) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    (* full_case *) a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_FALSE(stmt->attrs.empty());
  EXPECT_EQ(stmt->attrs[0].name, "full_case");
}

TEST(StatementSyntaxParsing, StatementWithLabelAndAttribute) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    lbl: (* mark *) a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->label, "lbl");
  EXPECT_FALSE(stmt->attrs.empty());
  EXPECT_EQ(stmt->attrs[0].name, "mark");
}

// --- Moved from test_parser_clause_09_03_05.cpp ---

TEST(StatementLabelParsing, StatementLabelOnBeginBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    name: begin\n"
      "      a = 1;\n"
      "    end: name\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  EXPECT_EQ(item->body->label, "name");
}
TEST(StatementLabelParsing, StatementLabelOnForkBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    name: fork\n"
      "      a = 1;\n"
      "    join: name\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->label, "name");
}

TEST(StatementLabelParsing, StatementLabelOnWhile) {
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

TEST(StatementLabelParsing, StatementLabelOnCase) {
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

TEST(StatementLabelParsing, SeqBlockWithStatementLabel) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    labelA: begin\n"
      "      a = 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlock);
  EXPECT_EQ(stmt->label, "labelA");
}

TEST(StatementLabelParsing, StatementLabelOnAssignment) {
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

TEST(StatementLabelParsing, StatementLabelOnIf) {
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

TEST(StatementLabelParsing, ForkWithStatementLabel) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    labelB: fork\n"
      "      a = 1;\n"
      "    join_none : labelB\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->label, "labelB");
}

TEST(StatementLabelParsing, StatementLabelOnForLoop) {
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

TEST(StatementSyntaxParsing, StatementWithLabel) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    my_label: a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
  EXPECT_EQ(stmt->label, "my_label");
}

TEST(StatementLabelParsing, StatementLabelOnVariableAssignment) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    assign_val: x = 42;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->label, "assign_val");
}

TEST(StatementLabelParsing, StatementLabelOnForever) {
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    inf: forever @(posedge clk) x = ~x;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForever);
}

TEST(StatementLabelParsing, LabelAndBlockNameErrors) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    my_label: begin : block_name\n"
      "      $display(\"hello\");\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(StatementLabelParsing, LabelStoredOnStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    lbl: $display(\"hello\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->body, nullptr);
  ASSERT_EQ(item->body->kind, StmtKind::kBlock);
  ASSERT_GE(item->body->stmts.size(), 1u);
  EXPECT_EQ(item->body->stmts[0]->label, "lbl");
}

// --- StmtItem dispatch tests (moved from various clause files) ---

TEST(StatementSyntaxParsing, BlockingAssignmentAsStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlockingAssign);
}

TEST(StatementSyntaxParsing, NonblockingAssignmentAsStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    x <= 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
}

TEST(StatementSyntaxParsing, ProceduralAssignAsStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assign x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssign);
}

TEST(StatementSyntaxParsing, ProceduralDeassignAsStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    deassign x;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDeassign);
}

TEST(StatementSyntaxParsing, ForceAsStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    force x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForce);
}

TEST(StatementSyntaxParsing, ReleaseAsStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    release x;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRelease);
}

TEST(StatementSyntaxParsing, CaseAsStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    case (x)\n"
      "      1: a = 1;\n"
      "      default: a = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
}

TEST(StatementSyntaxParsing, ConditionalAsStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (x) a = 1; else a = 0;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
}

TEST(StatementSyntaxParsing, DisableAsStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    disable my_block;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDisable);
}

TEST(StatementSyntaxParsing, BlockingTriggerAsStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    -> my_event;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventTrigger);
}

TEST(StatementSyntaxParsing, NonblockingTriggerAsStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    ->> my_event;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNbEventTrigger);
}

TEST(StatementSyntaxParsing, LoopAsStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i++) a = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
}

TEST(StatementSyntaxParsing, BreakAsStatement) {
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

TEST(StatementSyntaxParsing, ContinueAsStatement) {
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

TEST(StatementSyntaxParsing, ReturnAsStatement) {
  auto r = Parse(
      "module m;\n"
      "  function void f();\n"
      "    return;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* func = FirstFunctionDecl(r);
  ASSERT_NE(func, nullptr);
  ASSERT_GE(func->func_body_stmts.size(), 1u);
  EXPECT_EQ(func->func_body_stmts[0]->kind, StmtKind::kReturn);
}

TEST(StatementSyntaxParsing, DelayControlAsStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    #10 a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDelay);
}

TEST(StatementSyntaxParsing, EventControlAsStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    @(posedge clk) a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
}

TEST(StatementSyntaxParsing, WaitAsStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait (done) a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
}

TEST(StatementSyntaxParsing, RandcaseAsStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randcase\n"
      "      1: a = 1;\n"
      "      1: a = 2;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRandcase);
}

TEST(StatementSyntaxParsing, SeqBlockAsStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    begin\n"
      "      a = 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlock);
}

TEST(StatementSyntaxParsing, ParBlockAsStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      a = 1;\n"
      "    join\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
}

TEST(StatementSyntaxParsing, ImmediateAssertAsStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    assert (x == 1);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kAssertImmediate);
}

TEST(StatementSyntaxParsing, RandsequenceAsStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    randsequence(top)\n"
      "      top : a;\n"
      "      a : { x = 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRandsequence);
}

TEST(StatementSyntaxParsing, FunctionNullStatementWithAttribute) {
  auto r = Parse(
      "module m;\n"
      "  function void f();\n"
      "    (* synthesis *) ;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* func = FirstFunctionDecl(r);
  ASSERT_NE(func, nullptr);
  ASSERT_GE(func->func_body_stmts.size(), 1u);
  EXPECT_EQ(func->func_body_stmts[0]->kind, StmtKind::kNull);
  EXPECT_FALSE(func->func_body_stmts[0]->attrs.empty());
}

TEST(StatementLabelParsing, StatementLabelOnNullStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    marker: ;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNull);
  EXPECT_EQ(stmt->label, "marker");
}

TEST(StatementSyntaxParsing, InvalidTokenAsStatementErrors) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    endmodule\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
