#include "fixture_parser.h"
#include "fixture_preprocessor.h"

using namespace delta;

namespace {

TEST(HierarchicalNamePreprocessing, DotSeparatedPathSurvivesPreprocessing) {
  PreprocFixture f;
  auto out = Preprocess(
      "module m;\n"
      "  initial $display(top.sub.sig);\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("top.sub.sig"), std::string::npos);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(HierarchicalNamePreprocessing, EscapedIdentifierWhitespaceDotPreserved) {
  PreprocFixture f;
  auto out = Preprocess("\\esc .b", f);
  EXPECT_NE(out.find("\\esc"), std::string::npos);
  EXPECT_NE(out.find(" .b"), std::string::npos);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(HierarchicalNamePreprocessing, HierarchicalRefViaMacroExpansion) {
  auto r = ParseWithPreprocessor(
      "`define PATH top.sub.sig\n"
      "module m;\n"
      "  initial $display(`PATH);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(HierarchicalNamePreprocessing, RootPrefixSurvivesPreprocessing) {
  PreprocFixture f;
  auto out = Preprocess(
      "module m;\n"
      "  initial $display($root.top.sig);\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("$root.top.sig"), std::string::npos);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
