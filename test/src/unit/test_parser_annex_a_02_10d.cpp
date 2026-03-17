#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// --- sequence_declaration ---

TEST(AssertionDeclParsing, AssertionItemDecl_SequenceDecl) {
  auto r = Parse(
      "module m;\n"
      "  sequence s_handshake;\n"
      "    req ##[1:3] ack;\n"
      "  endsequence\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "s_handshake");
}

TEST(AssertionDeclParsing, SequenceDecl_WithEndLabel) {
  auto r = Parse(
      "module m;\n"
      "  sequence s_req;\n"
      "    req ##[1:3] ack;\n"
      "  endsequence : s_req\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "s_req");
}

TEST(AssertionDeclParsing, SequenceDecl_WithPortList) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(a, b);\n"
              "    a ##1 b;\n"
              "  endsequence\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, SequenceDecl_SourceLoc) {
  auto r = Parse(
      "module m;\n"
      "  sequence my_seq;\n"
      "    a;\n"
      "  endsequence\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->loc.IsValid());
}

TEST(AssertionParsing, SequenceDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  sequence s_req;\n"
      "    req ##1 ack;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kSequenceDecl) {
      found = true;
      EXPECT_EQ(item->name, "s_req");
    }
  }
  EXPECT_TRUE(found);
}

TEST(AssertionParsing, SequenceWithFormalArgsDecl) {
  auto r = Parse(
      "module m;\n"
      "  sequence s_req_ack(req, ack);\n"
      "    req ##1 ack;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(AssertionParsing, MulticlockSequenceDecl) {
  auto r = Parse(
      "module m;\n"
      "  sequence s_multi;\n"
      "    @(posedge clk1) a ##1 @(posedge clk2) b;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// --- sequence_port_list / sequence_port_item ---

TEST(AssertionDeclParsing, SequencePortItem_DefaultValue) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(a, b = 1'b1);\n"
              "    a ##1 b;\n"
              "  endsequence\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, SequencePortItem_LocalInout) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(local inout int x);\n"
              "    x > 0;\n"
              "  endsequence\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, SequenceLvarPortDirection_Input) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(local input int x);\n"
              "    x;\n"
              "  endsequence\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, SequenceLvarPortDirection_Output) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(local output int x);\n"
              "    (1, x = a) ##1 (1, x = b);\n"
              "  endsequence\n"
              "endmodule\n"));
}

// --- sequence_formal_type ---

TEST(AssertionDeclParsing, SequenceFormalType_Sequence) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(sequence sub_seq);\n"
              "    sub_seq ##1 a;\n"
              "  endsequence\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, SequenceFormalType_Untyped) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(untyped x);\n"
              "    x ##1 a;\n"
              "  endsequence\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, SequenceFormalType_DataType) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(int x);\n"
              "    x > 0;\n"
              "  endsequence\n"
              "endmodule\n"));
}

// --- sequence_list_of_arguments / sequence_actual_arg ---

TEST(AssertionDeclParsing, SequenceListOfArguments_Positional) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(a, b); a ##1 b; endsequence\n"
              "  assert property (@(posedge clk) s(x, y));\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, SequenceListOfArguments_Named) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(a, b); a ##1 b; endsequence\n"
              "  assert property (@(posedge clk) s(.a(x), .b(y)));\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, SequenceListOfArguments_Mixed) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(a, b, c); a ##1 b ##1 c; endsequence\n"
              "  assert property (@(posedge clk) s(x, .b(y), .c(z)));\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, SequenceActualArg_Dollar) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(a, b); a ##1 b; endsequence\n"
              "  assert property (@(posedge clk) s(x, $));\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, SequenceActualArg_EventExpr) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(a, b); a ##1 b; endsequence\n"
              "  assert property (@(posedge clk) s(posedge x, y));\n"
              "endmodule\n"));
}

// --- sequence_expr ---

TEST(AssertionDeclParsing, SequenceExpr_CycleDelay) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) ##2 a);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, SequenceExpr_Concatenation) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a ##1 b ##2 c);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, SequenceExpr_ClockingEvent) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a |-> @(negedge clk) b);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, SequenceExpr_ParenWithMatchItems) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    (a ##1 b, x = c) |-> d);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, SequenceExpr_And) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    (a ##1 b) and (c ##1 d));\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, SequenceExpr_Intersect) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    (a ##1 b) intersect (c ##1 d));\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, SequenceExpr_Or) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a or b);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, SequenceExpr_FirstMatch) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    first_match(a ##[1:5] b));\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, SequenceExpr_Throughout) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    en throughout (a ##1 b ##1 c));\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, SequenceExpr_Within) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    (a ##1 b) within (c ##[1:5] d));\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, SequenceExpr_ExprWithBooleanAbbrev) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a [*3]);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, SequenceExpr_SequenceInstanceWithAbbrev) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s; a ##1 b; endsequence\n"
              "  assert property (@(posedge clk) s [*3] |-> c);\n"
              "endmodule\n"));
}

TEST(AssertionParsing, SequenceDelayOperator) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) req ##1 gnt ##1 !req);\n"
              "endmodule\n"));
}

TEST(AssertionParsing, SequenceChainedConcatDelay) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req ##1 gnt ##1 !req);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(AssertionParsing, SequenceConcatFixedDelay) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req ##2 gnt);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(AssertionParsing, SequenceDelayRange) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req ##[4:32] gnt);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(AssertionParsing, SequenceWithRangeDelay) {
  auto r = Parse(
      "module m;\n"
      "  sequence s_handshake;\n"
      "    req ##[1:5] ack;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kSequenceDecl) {
      found = true;
      EXPECT_EQ(item->name, "s_handshake");
    }
  }
  EXPECT_TRUE(found);
}

TEST(AssertionParsing, SequenceThroughout) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (\n"
              "    @(posedge clk) !burst throughout (##2 trdy[*7]));\n"
              "endmodule\n"));
}

TEST(AssertionParsing, SequenceThroughoutBasic) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) !burst_mode throughout (##2 trdy[*7]));\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(AssertionParsing, SequenceThroughoutInSeqDecl) {
  auto r = Parse(
      "module m;\n"
      "  sequence burst_rule;\n"
      "    @(posedge clk)\n"
      "    (!burst_mode) throughout (##2 (trdy && irdy)[*7]);\n"
      "  endsequence\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* sq =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(sq, nullptr);
}

TEST(AssertionParsing, SequenceThroughoutWithImplication) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) req |-> en throughout (##2 ack[*3]));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// --- cycle_delay_range / cycle_delay_const_range_expression ---

TEST(AssertionDeclParsing, CycleDelayRange_Constant) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a ##1 b);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, CycleDelayRange_Range) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a ##[1:5] b);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, CycleDelayRange_OpenEndRange) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a ##[1:$] b);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, CycleDelayRange_Star) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) ##[*] a);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, CycleDelayRange_Plus) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) ##[+] a);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, CycleDelayRange_Zero) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a ##0 b);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, CycleDelayConstRange_FiniteRange) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a ##[2:5] b);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, CycleDelayConstRange_OpenEnd) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a ##[1:$] b);\n"
              "endmodule\n"));
}

// --- consecutive_repetition / nonconsecutive_repetition / goto_repetition ---

TEST(AssertionDeclParsing, ConsecutiveRepetition_Exact) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a [*3] |-> b);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, ConsecutiveRepetition_Range) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a [*1:3] |-> b);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, ConsecutiveRepetition_Star) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a [*] ##1 b);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, ConsecutiveRepetition_Plus) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a [+] ##1 b);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, NonconsecutiveRepetition) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a [=3] |-> b);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, NonconsecutiveRepetition_Range) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a [=1:3] |-> b);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, GotoRepetition_Exact) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a [->2] |-> b);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, GotoRepetition_Range) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a [->1:3] |-> b);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, ConstOrRangeExpr_Constant) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a [*5]);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, ConstOrRangeExpr_Range) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a [*2:8]);\n"
              "endmodule\n"));
}

TEST(AssertionParsing, SequenceConsecutiveRepetition) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a[*3] |-> b);\n"
              "endmodule\n"));
}

TEST(AssertionParsing, SequenceGotoRepetition) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) req |-> ack[->1]);\n"
              "endmodule\n"));
}

TEST(AssertionParsing, SequenceConsecutiveRepetitionChecksAst) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a[*3] |-> b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(AssertionParsing, SequenceRepetitionRange) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a[*1:3] ##1 b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(AssertionParsing, SequenceGotoRepetitionChecksAst) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req |-> ack[->1]);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

// --- sequence_match_item ---

TEST(AssertionDeclParsing, SequenceMatchItem_Assignment) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    (a ##1 b, x = c) |-> d);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, SequenceMatchItem_IncDec) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    (a ##1 b, x++) |-> c);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, SequenceMatchItem_SubroutineCall) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    (a ##1 b, $display(\"match\")) |-> c);\n"
              "endmodule\n"));
}

// --- assertion_variable_declaration ---

TEST(AssertionDeclParsing, AssertionVariableDecl_InProperty) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p;\n"
              "    int x;\n"
              "    (a, x = b) |-> (c == x);\n"
              "  endproperty\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, AssertionVariableDecl_InSequence) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s;\n"
              "    int x;\n"
              "    (a, x = b) ##1 (c == x);\n"
              "  endsequence\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, AssertionVariableDecl_MultipleVars) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p;\n"
              "    int x;\n"
              "    logic [7:0] y;\n"
              "    (a, x = b) |-> (c == x);\n"
              "  endproperty\n"
              "endmodule\n"));
}

// --- sequence_method_call ---

TEST(AssertionDeclParsing, SequenceMethodCall_Triggered) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s; a ##1 b; endsequence\n"
              "  assert property (@(posedge clk) s.triggered |-> c);\n"
              "endmodule\n"));
}

TEST(AssertionDeclParsing, SequenceMethodCall_Matched) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s; a ##1 b; endsequence\n"
              "  assert property (@(posedge clk) s.matched |-> c);\n"
              "endmodule\n"));
}

TEST(AssertionParsing, SequenceTriggeredMethod) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s1;\n"
              "    @(posedge clk) a ##1 b;\n"
              "  endsequence\n"
              "  sequence s2;\n"
              "    @(posedge clk) c ##1 s1.triggered ##1 d;\n"
              "  endsequence\n"
              "endmodule\n"));
}

TEST(AssertionParsing, SequenceMatchedMethod) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence e1;\n"
              "    @(posedge clk1) a ##1 b;\n"
              "  endsequence\n"
              "  sequence e2;\n"
              "    @(posedge clk2) c ##1 e1.matched ##1 d;\n"
              "  endsequence\n"
              "endmodule\n"));
}

TEST(AssertionParsing, SequenceTriggeredMethodChained) {
  auto r = Parse(
      "module m;\n"
      "  sequence e1;\n"
      "    @(posedge clk) a ##1 b ##1 c;\n"
      "  endsequence\n"
      "  sequence rule;\n"
      "    @(posedge clk) reset ##1 inst ##1 e1.triggered ##1 done;\n"
      "  endsequence\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(AssertionParsing, SequenceMatchedMethodWithReset) {
  auto r = Parse(
      "module m;\n"
      "  sequence e1;\n"
      "    @(posedge clk1) a ##1 b;\n"
      "  endsequence\n"
      "  sequence e2;\n"
      "    @(posedge clk2) reset ##1 e1.matched ##1 done;\n"
      "  endsequence\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

}  // namespace
