#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserClause03, Cl3_10_ConfigEnclosedByKeywords) {
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

TEST(ParserClause03, Cl3_10_ConfigWithDesignCell) {
  auto r = Parse(
      "module top; endmodule\n"
      "config cfg;\n"
      "  design top;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(r.cu->configs[0]->design_cells.empty());
}

TEST(ParserClause03, Cl3_10_ConfigWithDefaultRule) {
  EXPECT_TRUE(
      ParseOk("module m; endmodule\n"
              "config cfg;\n"
              "  design m;\n"
              "  default liblist work;\n"
              "endconfig\n"));
}

TEST(ParserClause03, Cl3_10_LibraryDeclaration) {
  auto r = ParseLibrary("library work \"*.sv\";\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->libraries.size(), 1u);
  EXPECT_EQ(r.cu->libraries[0]->name, "work");
}

TEST(ParserClause03, Cl3_10_ConfigAndModuleCoexist) {
  auto r = Parse(
      "module a; endmodule\n"
      "module b; endmodule\n"
      "config cfg;\n"
      "  design a;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules.size(), 2u);
  EXPECT_EQ(r.cu->configs.size(), 1u);
}

}  // namespace
