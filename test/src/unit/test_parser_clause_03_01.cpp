#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserClause03, EmptySourceProducesValidCU) {
  auto r = Parse("");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules.empty());
  EXPECT_TRUE(r.cu->programs.empty());
  EXPECT_TRUE(r.cu->interfaces.empty());
  EXPECT_TRUE(r.cu->checkers.empty());
  EXPECT_TRUE(r.cu->packages.empty());
  EXPECT_TRUE(r.cu->udps.empty());
  EXPECT_TRUE(r.cu->configs.empty());
  EXPECT_TRUE(r.cu->classes.empty());
  EXPECT_TRUE(r.cu->cu_items.empty());
}

TEST(ParserClause03, MultipleModulesInOneCU) {
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

TEST(ParserClause03, MismatchedEndKeywordIsError) {
  EXPECT_FALSE(ParseOk("module m; endprogram"));
}

TEST(ParserClause03, UnclosedDesignElementIsError) {
  EXPECT_FALSE(ParseOk("module m;"));
}

}  // namespace
