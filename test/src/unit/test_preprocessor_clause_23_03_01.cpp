// §23.3.1

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(TopLevelModules, MultipleModulesSurvivePreprocessing) {
  auto r = ParseWithPreprocessor(
      "module a; endmodule\n"
      "module b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules.size(), 2u);
}

TEST(TopLevelModules, DollarRootSurvivesPreprocessing) {
  EXPECT_TRUE(ParseWithPreprocessorOk(
      "module top;\n"
      "  logic x;\n"
      "  assign x = $root.top.x;\n"
      "endmodule\n"));
}

TEST(TopLevelModules, ConditionallyCompiledModulesAffectTopCandidates) {
  auto r = ParseWithPreprocessor(
      "`define INCLUDE_B\n"
      "module a; endmodule\n"
      "`ifdef INCLUDE_B\n"
      "module b; endmodule\n"
      "`endif\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules.size(), 2u);
}

TEST(TopLevelModules, UndefinedConditionalExcludesModule) {
  auto r = ParseWithPreprocessor(
      "module a; endmodule\n"
      "`ifdef NEVER_DEFINED\n"
      "module b; endmodule\n"
      "`endif\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "a");
}

}  // namespace
