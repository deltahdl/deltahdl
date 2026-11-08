#include <gtest/gtest.h>

#include <cstdint>

#include "common/diagnostic.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "lexer/token.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

TEST(StatementLabelParsing, FunctionStatementWithLabel) {
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

TEST(StatementLabelParsing, StatementLabelOnBlockingAssignment) {
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
  EXPECT_TRUE(ReportedError(
      r.diags, "cannot have both a statement label and a block name", 3,
      "9.3.5"));
}

TEST(StatementLabelParsing, StatementLabelOnTaskCall) {
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

TEST(StatementLabelParsing, StatementWithLabelAndAttribute) {
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

TEST(StatementLabelParsing, StatementLabelOnDoWhile) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    again: do a = ~a; while (busy);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDoWhile);
  EXPECT_EQ(stmt->label, "again");
}

TEST(StatementLabelParsing, StatementLabelOnRepeat) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    pulse: repeat (4) @(posedge clk);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kRepeat);
  EXPECT_EQ(stmt->label, "pulse");
}

TEST(StatementLabelParsing, StatementLabelOnForeach) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    scan: foreach (arr[i]) $display(arr[i]);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kForeach);
  EXPECT_EQ(stmt->label, "scan");
}

TEST(StatementLabelParsing, StatementLabelOnNonblockingAssignment) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    drive: q <= d;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kNonblockingAssign);
  EXPECT_EQ(stmt->label, "drive");
}

TEST(StatementLabelParsing, StatementLabelOnWait) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    hold: wait (ready) a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
  EXPECT_EQ(stmt->label, "hold");
}

TEST(StatementLabelParsing, StatementLabelOnDelayControl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    wait5: #5 a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDelay);
  EXPECT_EQ(stmt->label, "wait5");
}

TEST(StatementLabelParsing, StatementLabelOnEventControl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    sync: @(posedge clk) a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventControl);
  EXPECT_EQ(stmt->label, "sync");
}

TEST(StatementLabelParsing, StatementLabelOnEventTrigger) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fire: -> done;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kEventTrigger);
  EXPECT_EQ(stmt->label, "fire");
}

TEST(StatementLabelParsing, StatementLabelOnForLoopStoresLabel) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    loop: for (int i = 0; i < 10; i++) a = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFor);
  EXPECT_EQ(stmt->label, "loop");
}

TEST(StatementLabelParsing, StatementLabelOnForkWithJoinAny) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    race: fork\n"
      "      #10 a = 1;\n"
      "      #20 b = 2;\n"
      "    join_any : race\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->label, "race");
  EXPECT_EQ(stmt->join_kind, TokenKind::kKwJoinAny);
}

TEST(StatementLabelParsing, MismatchedEndLabelOnLabeledBeginIsError) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    blk: begin\n"
      "      a = 1;\n"
      "    end : wrong\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "end label 'wrong' does not match block name "
                            "'blk'",
                            5, "9.3.4"));
}

TEST(StatementLabelParsing, MismatchedEndLabelOnLabeledForkIsError) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fg: fork\n"
      "      a = 1;\n"
      "    join : wrong\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "end label 'wrong' does not match block name 'fg'", 5, "9.3.4"));
}

TEST(StatementLabelParsing, LabelAndBlockNameOnForkIsError) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    my_label: fork : block_name\n"
      "      a = 1;\n"
      "    join\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "cannot have both a statement label and a block name", 3,
      "9.3.5"));
}

TEST(StatementLabelParsing, PrefixLabelMatchesEndLabelOnBegin) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    name: begin\n"
      "      a = 1;\n"
      "    end : name\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = InitialBody(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kBlock);
  EXPECT_EQ(stmt->label, "name");
}

TEST(StatementLabelParsing, PrefixLabelMatchesJoinLabelOnFork) {
  auto r = Parse(
      "module m;\n"
      "  initial\n"
      "    name: fork\n"
      "      a = 1;\n"
      "    join : name\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kFork);
  EXPECT_EQ(stmt->label, "name");
}

TEST(StatementLabelParsing, LabelBeforeEndIsError) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "    tail: end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a statement label cannot appear before 'end', which does not",
      4, "9.3.5"));
}

TEST(StatementLabelParsing, LabelBeforeEndReportsExactlyOneError) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "    tail: end\n"
      "endmodule\n");
  uint32_t errors = 0;
  for (const auto& d : r.diags) {
    if (d.severity == DiagSeverity::kError) errors++;
  }
  EXPECT_EQ(errors, 1U);
}

TEST(StatementLabelParsing, LabelBeforeJoinIsError) {
  auto r = Parse(
      "module m;\n"
      "  initial fork\n"
      "    a = 1;\n"
      "    tail: join\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a statement label cannot appear before 'join', which does not",
      4, "9.3.5"));
}

TEST(StatementLabelParsing, LabelBeforeDeclarationIsError) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    lbl: int x;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a statement label cannot appear before a declaration", 3,
      "9.3.5"));
}

TEST(StatementLabelParsing,
     LabelBeforeDeclarationReportsAtTheLabelNotTheDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    lbl:\n"
      "    int x;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a statement label cannot appear before a declaration", 3,
      "9.3.5"));
}

TEST(StatementLabelParsing, LabelBeforeDeclarationLeavesTheDeclarationParsed) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    lbl: int x;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a statement label cannot appear before a declaration", 3,
      "9.3.5"));
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kVarDecl);
  EXPECT_EQ(stmt->var_name, "x");
}

TEST(StatementLabelParsing, LabelBeforeDeclarationInFunctionRejected) {
  auto r = Parse(
      "module m;\n"
      "  function void f();\n"
      "    lbl: int x;\n"
      "  endfunction\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a statement label cannot appear before a declaration", 3,
      "9.3.5"));
}

TEST(StatementLabelParsing, LabelBeforeDeclarationInTaskRejected) {
  auto r = Parse(
      "module m;\n"
      "  task t;\n"
      "    lbl: int x;\n"
      "  endtask\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a statement label cannot appear before a declaration", 3,
      "9.3.5"));
}

TEST(StatementLabelParsing, LabelBeforeJoinAnyIsError) {
  auto r = Parse(
      "module m;\n"
      "  initial fork\n"
      "    a = 1;\n"
      "    tail: join_any\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "a statement label cannot appear before "
                            "'join_any', which does not",
                            4, "9.3.5"));
}

TEST(StatementLabelParsing, LabelBeforeJoinNoneIsError) {
  auto r = Parse(
      "module m;\n"
      "  initial fork\n"
      "    a = 1;\n"
      "    tail: join_none\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "a statement label cannot appear before "
                            "'join_none', which does not",
                            4, "9.3.5"));
}

TEST(StatementLabelParsing, MultipleLabelsInSequence) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    step1: a = 1;\n"
      "    step2: b = 2;\n"
      "    step3: c = 3;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 3u);
  EXPECT_EQ(body->stmts[0]->label, "step1");
  EXPECT_EQ(body->stmts[1]->label, "step2");
  EXPECT_EQ(body->stmts[2]->label, "step3");
}

}  // namespace
