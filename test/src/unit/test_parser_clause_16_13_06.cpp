#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA210, SequenceMethodCall_Triggered) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s; a ##1 b; endsequence\n"
              "  assert property (@(posedge clk) s.triggered |-> c);\n"
              "endmodule\n"));
}

TEST(ParserA210, SequenceMethodCall_Matched) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s; a ##1 b; endsequence\n"
              "  assert property (@(posedge clk) s.matched |-> c);\n"
              "endmodule\n"));
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

TEST(ParserSection16, Sec16_5_1_SequenceTriggeredMethod) {
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

TEST(ParserSection16, Sec16_5_1_SequenceMatchedMethod) {
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

TEST(ParserSection16, SequenceTriggeredMethod) {
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

TEST(ParserSection16, SequenceMatchedMethod) {
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
