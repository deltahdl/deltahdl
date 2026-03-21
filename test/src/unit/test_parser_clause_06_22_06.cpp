#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(MatchingNettypesParsing, UserDefinedNettypeSelfMatch) {
  auto r = Parse(
      "module m;\n"
      "  nettype logic [7:0] mynet_t;\n"
      "  mynet_t a;\n"
      "  mynet_t b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(MatchingNettypesParsing, NettypeAliasDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  nettype logic [7:0] base_t;\n"
      "  nettype base_t alias_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(MatchingNettypesParsing, NettypeAliasNetsAssignment) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  nettype logic [7:0] base_t;\n"
      "  nettype base_t alias_t;\n"
      "  base_t a;\n"
      "  alias_t b;\n"
      "  assign a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
