#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA211, BinsOrOptions_WithWithClause) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins b = {[0:15]} with (item > 5);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, WithCovergroupExpression) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins b = {[0:255]} with (item > 10);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverGroup_BinsWithCoverPointRef) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg;\n"
              "    coverpoint x {\n"
              "      bins b = {[0:15]} with (item < 10);\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

}
