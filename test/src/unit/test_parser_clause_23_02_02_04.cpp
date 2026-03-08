// §23.2.2.4

#include "fixture_parser.h"

using namespace delta;

namespace {

// ansi_port_declaration with default value
TEST(ModuleParamsA13, AnsiPortWithDefault) {
  auto r = Parse(
      "module m(\n"
      "  input logic clk,\n"
      "  input logic rst = 0\n"
      ");\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports.size(), 2u);
  EXPECT_NE(r.cu->modules[0]->ports[1].default_value, nullptr);
}

}  // namespace
