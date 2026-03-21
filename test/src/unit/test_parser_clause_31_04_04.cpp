#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(TimingCheckEventDefParsing, ControlledTimingCheckEventWidth) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $width(negedge rst, 20);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kNegedge);
  EXPECT_EQ(tc->ref_terminal.name, "rst");
}

}  // namespace
