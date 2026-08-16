#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"

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
  // The report stands at the `begin` the label precedes, on line 3.
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
  // A label may precede a delay-control statement, a procedural statement
  // reached through a parse path distinct from the assignment forms.
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
  // A label may precede an event-control statement.
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
  // A label may precede an event-trigger statement.
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
  // §9.3.4 owns the rule that a name after end must match the block name, and
  // ParserStmtHelpers::MatchEndBlockLabel files the report under it; §9.3.5
  // contributes only the equivalence that makes `blk` the block name here.
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
  // §9.3.4 owns the matching-name rule the report is filed under, as above.
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
  // The report stands at the `fork` the label precedes, on line 3.
  EXPECT_TRUE(ReportedError(
      r.diags, "cannot have both a statement label and a block name", 3,
      "9.3.5"));
}

TEST(StatementLabelParsing, PrefixLabelMatchesEndLabelOnBegin) {
  // A label before begin is equivalent to a block name, so a matching name
  // may follow end without being treated as a label on an unnamed block.
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
  // The same equivalence holds for fork ... join with a matching name.
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
  // §9.3.5: "A label cannot appear before the end, join, join_any, or
  // join_none, as these keywords do not form a statement." The report names the
  // keyword, so each of the four sources below fixes a different message. It
  // stands at the label on line 4, not at the keyword.
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
  // The rejection leaves the `end` unconsumed, so the block closes on it and
  // the module closes on `endmodule`. Parser::ParsePrimaryExpr used to consume
  // that `end` as a failed expression, after which the module reported a second
  // time; a count is what states the cascade is gone.
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
  // The same §9.3.5 sentence covers the three fork terminators.
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
  // §9.3.5: "A label can be specified before any procedural statement (any
  // non-declaration statement that can appear inside a begin-end block)." A
  // data declaration is not one, so a label before it is rejected. This message
  // differs from the keyword one above and from the "cannot have both a
  // statement label and a block name" report the same subclause already
  // carries, which is what keeps the three §9.3.5 rules apart.
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
  // The label and the declaration stand on separate lines, so the asserted line
  // can fail. ReportedError compares the line and not the column, and
  // StatementLabelParsing.LabelBeforeDeclarationIsError puts both on line 3,
  // where a report about the declaration would satisfy it just as well.
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
  // The label is dropped and what followed it is then read as the declaration
  // it is, so the block holds `int x` rather than the expression statement the
  // label used to turn it into.
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    lbl: int x;\n"
      "  end\n"
      "endmodule\n");
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kVarDecl);
  EXPECT_EQ(stmt->var_name, "x");
}

TEST(StatementLabelParsing, LabelBeforeDeclarationInFunctionRejected) {
  // A function body admits declarations as a begin-end block does, so §9.3.5
  // reaches it through the same rejection. Parser::ParseFuncBody has its own
  // statement loop, separate from the one in Parser::ParseBlockStmt.
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
  // A task body has a third such loop, in Parser::ParseTaskDecl.
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
  // join_any is the second fork terminator the sentence enumerates.
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
  // join_none is the third and last.
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
