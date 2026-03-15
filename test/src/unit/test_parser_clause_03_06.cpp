// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(DesignBuildingBlockParsing, CheckerWithPorts) {
  auto r = Parse(
      "checker chk(input logic clk, input logic rst);\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->checkers[0]->ports.size(), 2u);
}

TEST(DesignBuildingBlockParsing, CheckerWithMixedContent) {
  EXPECT_TRUE(
      ParseOk("checker chk(input logic clk, input logic a, input logic b);\n"
              "  logic internal;\n"
              "  always_comb internal = a & b;\n"
              "  assert property (@(posedge clk) a |-> b);\n"
              "  cover property (@(posedge clk) a && b);\n"
              "endchecker\n"));
}

}  // namespace
