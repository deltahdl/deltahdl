#include "fixture_parser.h"
#include "fixture_preprocessor.h"

using namespace delta;

namespace {

// §23.6: "The period character shall be used to separate each of the names in
// the hierarchy."  Preprocessor must preserve a hierarchical_identifier's
// dot-separated text so downstream lexing still sees the path.
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

// §23.6: escaped identifiers in a hierarchical name reference "are followed
// by separators composed of white space and a period-character."  The
// preprocessor must keep the required whitespace between an escaped
// identifier and the trailing dot.
TEST(HierarchicalNamePreprocessing, EscapedIdentifierWhitespaceDotPreserved) {
  PreprocFixture f;
  auto out = Preprocess("\\esc .b", f);
  EXPECT_NE(out.find("\\esc"), std::string::npos);
  EXPECT_NE(out.find(" .b"), std::string::npos);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §23.6: A hierarchical name reference text remains intact through
// `define-driven macro expansion so subsequent parsing can resolve it.
TEST(HierarchicalNamePreprocessing, HierarchicalRefViaMacroExpansion) {
  auto r = ParseWithPreprocessor(
      "`define PATH top.sub.sig\n"
      "module m;\n"
      "  initial $display(`PATH);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §23.6: `$root` prefix on a hierarchical_identifier survives preprocessing.
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
