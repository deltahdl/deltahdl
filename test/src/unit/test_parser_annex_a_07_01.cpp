// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ParserA701, SpecparamWithRange) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam [31:0] tPD = 100;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ParserA701, SpecparamMultipleDecls) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam tRISE = 100, tFALL = 200;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
