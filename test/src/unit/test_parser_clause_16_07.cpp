#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA210, SequenceExpr_CycleDelay) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) ##2 a);\n"
              "endmodule\n"));
}

TEST(ParserA210, SequenceExpr_Concatenation) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a ##1 b ##2 c);\n"
              "endmodule\n"));
}

TEST(ParserA210, SequenceExpr_ClockingEvent) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a |-> @(negedge clk) b);\n"
              "endmodule\n"));
}

TEST(ParserA210, CycleDelayRange_Constant) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a ##1 b);\n"
              "endmodule\n"));
}

TEST(ParserA210, CycleDelayRange_Range) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a ##[1:5] b);\n"
              "endmodule\n"));
}

TEST(ParserA210, CycleDelayRange_OpenEndRange) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a ##[1:$] b);\n"
              "endmodule\n"));
}

TEST(ParserA210, CycleDelayRange_Star) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) ##[*] a);\n"
              "endmodule\n"));
}

TEST(ParserA210, CycleDelayRange_Plus) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) ##[+] a);\n"
              "endmodule\n"));
}

TEST(ParserA210, CycleDelayRange_Zero) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a ##0 b);\n"
              "endmodule\n"));
}

TEST(ParserA210, CycleDelayConstRange_FiniteRange) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a ##[2:5] b);\n"
              "endmodule\n"));
}

TEST(ParserA210, CycleDelayConstRange_OpenEnd) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a ##[1:$] b);\n"
              "endmodule\n"));
}

TEST(ParserA210, SequenceListOfArguments_Mixed) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(a, b, c); a ##1 b ##1 c; endsequence\n"
              "  assert property (@(posedge clk) s(x, .b(y), .c(z)));\n"
              "endmodule\n"));
}

TEST(ParserA210, SequenceExpr_ParenWithMatchItems) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    (a ##1 b, x = c) |-> d);\n"
              "endmodule\n"));
}

TEST(ParserSection16, Sec16_5_1_SequenceDelayOperator) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) req ##1 gnt ##1 !req);\n"
              "endmodule\n"));
}

TEST(ParserSection16, SequenceConcatDelay1) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req ##1 gnt ##1 !req);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection16, SequenceConcatDelay2) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req ##2 gnt);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection16, SequenceDelayRange) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req ##[4:32] gnt);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

bool HasItemKind(ParseResult& r, ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return true;
  }
  return false;
}

TEST(ParserAnnexF, AnnexFSequenceConcatDelay) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a ##2 b ##3 c);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

TEST(ParserAnnexF, AnnexFRangedRepetition) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a ##[1:5] b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

TEST(ParserAnnexF, AnnexFChainedConcat) {
  auto r = Parse(
      "module m;\n"
      "  sequence s_chain;\n"
      "    @(posedge clk) a ##1 b ##1 c ##1 d ##1 e;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kSequenceDecl));
}

TEST(ParserAnnexF, AnnexFUnboundedDelayRange) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req |-> ##[0:$] ack);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

TEST(ParserSection16, SequenceWithRangeDelay) {
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

}
