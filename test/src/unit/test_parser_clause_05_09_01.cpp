#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserClause05, Cl5_9_1_StringWithNewlineEscape) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial $display(\"line1\\nline2\");\n"
              "endmodule"));
}

TEST(ParserClause05, Cl5_9_1_StringWithTabEscape) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial $display(\"col1\\tcol2\");\n"
              "endmodule"));
}

TEST(ParserClause05, Cl5_9_1_StringWithQuoteEscape) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial $display(\"say \\\"hello\\\"\");\n"
              "endmodule"));
}

TEST(ParserClause05, Cl5_9_1_StringWithOctalEscape) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial $display(\"\\101\");\n"
              "endmodule"));
}

TEST(ParserClause05, Cl5_9_1_StringWithHexEscape) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial $display(\"\\x41\");\n"
              "endmodule"));
}

}  // namespace
