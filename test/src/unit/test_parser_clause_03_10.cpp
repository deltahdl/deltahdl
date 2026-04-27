#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(DesignBuildingBlockParsing, ConfigEnclosedByKeywords) {
  auto r = Parse(
      "module m; endmodule\n"
      "config cfg;\n"
      "  design m;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->name, "cfg");
}

TEST(DesignBuildingBlockParsing, ConfigWithDefaultRule) {
  EXPECT_TRUE(
      ParseOk("module m; endmodule\n"
              "config cfg;\n"
              "  design m;\n"
              "  default liblist work;\n"
              "endconfig\n"));
}

}  // namespace
