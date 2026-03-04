#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA210, SequenceExpr_ExprWithBooleanAbbrev) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a [*3]);\n"
              "endmodule\n"));
}

TEST(ParserA210, ConsecutiveRepetition_Exact) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a [*3] |-> b);\n"
              "endmodule\n"));
}

TEST(ParserA210, ConsecutiveRepetition_Range) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a [*1:3] |-> b);\n"
              "endmodule\n"));
}

TEST(ParserA210, ConsecutiveRepetition_Star) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a [*] ##1 b);\n"
              "endmodule\n"));
}

TEST(ParserA210, ConsecutiveRepetition_Plus) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a [+] ##1 b);\n"
              "endmodule\n"));
}

TEST(ParserA210, NonconsecutiveRepetition) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a [=3] |-> b);\n"
              "endmodule\n"));
}

TEST(ParserA210, NonconsecutiveRepetition_Range) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a [=1:3] |-> b);\n"
              "endmodule\n"));
}

TEST(ParserA210, GotoRepetition_Exact) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a [->2] |-> b);\n"
              "endmodule\n"));
}

TEST(ParserA210, GotoRepetition_Range) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a [->1:3] |-> b);\n"
              "endmodule\n"));
}

TEST(ParserA210, ConstOrRangeExpr_Constant) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a [*5]);\n"
              "endmodule\n"));
}

TEST(ParserA210, ConstOrRangeExpr_Range) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a [*2:8]);\n"
              "endmodule\n"));
}

TEST(ParserA210, SequenceExpr_SequenceInstanceWithAbbrev) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s; a ##1 b; endsequence\n"
              "  assert property (@(posedge clk) s [*3] |-> c);\n"
              "endmodule\n"));
}

TEST(ParserSection16, Sec16_5_1_SequenceConsecutiveRepetition) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) a[*3] |-> b);\n"
              "endmodule\n"));
}

TEST(ParserSection16, Sec16_5_1_SequenceGotoRepetition) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) req |-> ack[->1]);\n"
              "endmodule\n"));
}

TEST(ParserSection16, SequenceConsecutiveRepetition) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a[*3] |-> b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection16, SequenceRepetitionRange) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a[*1:3] ##1 b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

TEST(ParserSection16, SequenceGotoRepetition) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req |-> ack[->1]);\n"
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

TEST(ParserAnnexF, AnnexFConsecutiveRepetition) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a[*3] |-> b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

TEST(ParserAnnexF, AnnexFGotoRepetition) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req |-> ack[->1]);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

TEST(ParserAnnexF, AnnexFNonconsecutiveRepetition) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req |-> ack[=2]);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

}
