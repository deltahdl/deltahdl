#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA210, SequenceMatchItem_Assignment) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    (a ##1 b, x = c) |-> d);\n"
              "endmodule\n"));
}

TEST(ParserA210, AssertionVariableDecl_InProperty) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p;\n"
              "    int x;\n"
              "    (a, x = b) |-> (c == x);\n"
              "  endproperty\n"
              "endmodule\n"));
}

TEST(ParserA210, AssertionVariableDecl_InSequence) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s;\n"
              "    int x;\n"
              "    (a, x = b) ##1 (c == x);\n"
              "  endsequence\n"
              "endmodule\n"));
}

TEST(ParserA210, SequenceMatchItem_IncDec) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    (a ##1 b, x++) |-> c);\n"
              "endmodule\n"));
}

TEST(ParserA210, AssertionVariableDecl_MultipleVars) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  property p;\n"
              "    int x;\n"
              "    logic [7:0] y;\n"
              "    (a, x = b) |-> (c == x);\n"
              "  endproperty\n"
              "endmodule\n"));
}

}  // namespace
