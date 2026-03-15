// Non-LRM tests

#include "fixture_preprocessor.h"

namespace {

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

TEST(DesignElementPreprocessing, ElsifChainSelectsCorrectDesignElement) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define USE_IFACE\n"
      "`ifdef USE_MODULE\n"
      "module m; endmodule\n"
      "`elsif USE_IFACE\n"
      "interface ifc; endinterface\n"
      "`else\n"
      "package p; endpackage\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(result.find("module"), std::string::npos);
  EXPECT_NE(result.find("interface"), std::string::npos);
  EXPECT_EQ(result.find("package"), std::string::npos);
}

TEST(DesignElementPreprocessing, UndefThenIfdefExcludesDesignElement) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define HAS_PKG\n"
      "`undef HAS_PKG\n"
      "`ifdef HAS_PKG\n"
      "package p; endpackage\n"
      "`endif\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(result.find("package"), std::string::npos);
}

TEST(DesignElementPreprocessing, EmptyIfdefBodyPreservesSubsequent) {
  PreprocFixture f;
  auto result = Preprocess(
      "`ifdef UNDEFINED_MACRO\n"
      "`endif\n"
      "module m; endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("module"), std::string::npos);
}

TEST(DesignElementPreprocessing, MultipleMacrosExpandInSameDesignElement) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define A 4\n"
      "`define B 8\n"
      "module m;\n"
      "  logic [`A-1:0] x;\n"
      "  logic [`B-1:0] y;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("4"), std::string::npos);
  EXPECT_NE(result.find("8"), std::string::npos);
}

}  // namespace
