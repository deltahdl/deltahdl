#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

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

}  // namespace
