// §6.20.1: Parameter declaration syntax

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ParserA23, ListOfSpecparamAssignmentsMultiple) {
  auto r = Parse(
      "module m;\n"
      "  specify specparam tRISE = 100, tFALL = 50, tHOLD = 10; endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
