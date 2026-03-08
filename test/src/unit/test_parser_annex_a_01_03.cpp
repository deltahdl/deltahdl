// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

namespace {

// ansi_port_declaration with unpacked dimensions
TEST(ModuleParamsA13, AnsiPortUnpackedDim) {
  auto r = Parse(
      "module m(\n"
      "  input logic [7:0] data [4]\n"
      ");\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// interface port header
TEST(ModuleParamsA13, InterfacePortHeader) {
  auto r = Parse(
      "module m(bus_if.master bus);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
