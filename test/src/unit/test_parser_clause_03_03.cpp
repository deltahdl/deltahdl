// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(DesignBuildingBlockParsing, MismatchedEndKeywordIsError) {
  EXPECT_FALSE(ParseOk("module m; endprogram"));
}

TEST(DesignBuildingBlockParsing, UnclosedModuleIsError) {
  EXPECT_FALSE(ParseOk("module m;"));
}

}  // namespace
