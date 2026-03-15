// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(DesignBuildingBlockParsing, MultipleModulesInOneCU) {
  auto r = Parse(
      "module a; endmodule\nmodule b; endmodule\n"
      "module c; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 3u);
  EXPECT_EQ(r.cu->modules[0]->name, "a");
  EXPECT_EQ(r.cu->modules[1]->name, "b");
  EXPECT_EQ(r.cu->modules[2]->name, "c");
}

TEST(DesignBuildingBlockParsing, MismatchedEndKeywordIsError) {
  EXPECT_FALSE(ParseOk("module m; endprogram"));
}

TEST(DesignBuildingBlockParsing, UnclosedModuleIsError) {
  EXPECT_FALSE(ParseOk("module m;"));
}

}  // namespace
