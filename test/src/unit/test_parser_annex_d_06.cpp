#include <gtest/gtest.h>

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(OptionalListParserParsing, NoArgument) {
  auto r = Parse(
      "module m;\n"
      "  initial $list;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

TEST(OptionalListParserParsing, HierarchicalArgument) {
  auto r = Parse(
      "module m;\n"
      "  initial $list(m.blk);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
}

TEST(OptionalListParserParsing, MultiLevelHierarchicalArgument) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial $list(m.outer.inner);\n"
              "endmodule\n"));
}

TEST(OptionalListParserParsing, BareFormParsesWithoutError) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial $list;\n"
              "endmodule\n"));
}

}  // namespace
