#include <gtest/gtest.h>

#include "fixture_program.h"

using namespace delta;

namespace {

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
