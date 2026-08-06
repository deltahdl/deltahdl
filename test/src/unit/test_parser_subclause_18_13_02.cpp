#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

namespace {

// The §18.13.2 prototype lists maxval as the only required argument and minval
// as a defaulted optional argument, so a single-argument call is well-formed.
TEST_F(AnnexHParseTest, UrandomRangeSingleArgumentForm) {
  auto* unit = Parse(
      "module m;\n"
      "  int x;\n"
      "  initial begin\n"
      "    x = $urandom_range(7);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  EXPECT_FALSE(diag_.HasErrors());
}

// The §18.13.2 prototype accepts maxval followed by an explicit minval.
TEST_F(AnnexHParseTest, UrandomRangeTwoArgumentForm) {
  auto* unit = Parse(
      "module m;\n"
      "  int x;\n"
      "  initial begin\n"
      "    x = $urandom_range(7, 0);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  EXPECT_FALSE(diag_.HasErrors());
}

}  // namespace
