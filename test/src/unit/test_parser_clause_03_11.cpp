// Non-LRM tests

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(DesignBuildingBlockParsing, MultipleLevelsOfHierarchy) {
  EXPECT_TRUE(
      ParseOk("module leaf; endmodule\n"
              "module mid; leaf u0(); endmodule\n"
              "module top; mid u0(); endmodule\n"));
}

TEST(DesignBuildingBlockParsing, MultipleTopLevelModules) {
  auto r = Parse(
      "module top_a; endmodule\n"
      "module top_b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules.size(), 2u);
}

}  // namespace
