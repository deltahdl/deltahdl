// §30.3: Specify block declaration

#include "fixture_parser.h"

using namespace delta;

namespace {

// --- list_of_specparam_assignments ---
// specparam_assignment { , specparam_assignment }
TEST(ParserA23, ListOfSpecparamAssignmentsSingle) {
  auto r = Parse(
      "module m;\n"
      "  specify specparam tRISE = 100; endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
