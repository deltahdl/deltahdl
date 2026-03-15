// Non-LRM tests

#include "fixture_preprocessor.h"

namespace {

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
