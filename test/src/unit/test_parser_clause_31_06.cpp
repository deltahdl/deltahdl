// §31.6: Notifiers: user-defined responses to timing violations

#include "fixture_parser.h"

using namespace delta;

namespace {

// =============================================================================
// A.7.5.2 notifier ::= variable_identifier
// =============================================================================
TEST(ParserA70502, NotifierVariable) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, posedge clk, 10, ntfr);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->notifier, "ntfr");
}

}  // namespace
