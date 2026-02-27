// §23.10.1: defparam statement

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA23, ListOfDefparamAssignmentsThree) {
  auto r = Parse(
      "module top;\n"
      "  defparam u0.A = 1, u0.B = 2, u0.C = 3;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->defparam_assigns.size(), 3u);
}

}  // namespace
