#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

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

TEST(ParserSection9c, WaitSequenceTriggeredWithAction) {
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

}  // namespace
