#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA210, ExpectPropertyStatement) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  initial begin\n"
      "    expect (a |-> b) $display(\"pass\"); else $display(\"fail\");\n"
      "  end\n"
      "endmodule\n"));
}

TEST(ParserA210, ExpectPropertyStatement_NoActions) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    expect (req |-> ack);\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ParserSection16, ExpectStatement) {
  auto r = Parse(
      "module top();\n"
      "  logic clk, a, b;\n"
      "  initial begin\n"
      "    expect (@(posedge clk) a ##1 b);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->modules.size(), 1u);
}

}  // namespace
