#include "fixture_preprocessor.h"

namespace {

// §3.1 General — preprocessing of design element structures.

TEST(DesignElementPreprocessing, IfdefAroundModuleIncludesTaken) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define HAS_MODULE\n"
      "`ifdef HAS_MODULE\n"
      "module m; endmodule\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("module"), std::string::npos);
}

TEST(DesignElementPreprocessing, IfdefAroundModuleExcludesUntaken) {
  PreprocFixture f;
  auto result = Preprocess(
      "`ifdef UNDEFINED_MACRO\n"
      "module m; endmodule\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(result.find("module"), std::string::npos);
}

TEST(DesignElementPreprocessing, IfndefIncludesWhenUndefined) {
  PreprocFixture f;
  auto result = Preprocess(
      "`ifndef MISSING\n"
      "interface ifc; endinterface\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("interface"), std::string::npos);
}

TEST(DesignElementPreprocessing, IfdefElseSelectsAlternate) {
  PreprocFixture f;
  auto result = Preprocess(
      "`ifdef MISSING\n"
      "module a; endmodule\n"
      "`else\n"
      "module b; endmodule\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(result.find("module a"), std::string::npos);
  EXPECT_NE(result.find("module b"), std::string::npos);
}

TEST(DesignElementPreprocessing, MacroExpandsInsideModule) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define WIDTH 8\n"
      "module m;\n"
      "  logic [`WIDTH-1:0] data;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("8"), std::string::npos);
}

TEST(DesignElementPreprocessing, MacroExpandsToDesignElement) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define EMPTY_MOD(name) module name; endmodule\n"
      "`EMPTY_MOD(foo)\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("module"), std::string::npos);
  EXPECT_NE(result.find("foo"), std::string::npos);
}

TEST(DesignElementPreprocessing, MultipleDesignElementsWithConditional) {
  PreprocFixture f;
  auto result = Preprocess(
      "module always_present; endmodule\n"
      "`define INCLUDE_PKG\n"
      "`ifdef INCLUDE_PKG\n"
      "package pkg; endpackage\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("always_present"), std::string::npos);
  EXPECT_NE(result.find("package"), std::string::npos);
}

TEST(DesignElementPreprocessing, NestedIfdefAroundDesignElements) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define OUTER\n"
      "`define INNER\n"
      "`ifdef OUTER\n"
      "`ifdef INNER\n"
      "program p; endprogram\n"
      "`endif\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("program"), std::string::npos);
}

}  // namespace
