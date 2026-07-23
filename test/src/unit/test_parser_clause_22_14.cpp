#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(KeywordVersionParsing, BeginKeywordsMultipleModules) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`begin_keywords \"1800-2012\"\n"
                              "module m1;\n"
                              "endmodule\n"
                              "module m2;\n"
                              "endmodule\n"
                              "`end_keywords\n"));
}

// §22.14: under a version that does not reserve it, the word is an ordinary
// identifier — so it is usable in every position an identifier may occupy.
// Each position below is a distinct parser path, and each is paired with the
// negative: the same text under a version that does reserve the word.
TEST(KeywordVersionParsing, OldVersionIdentifierNamesANet) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`begin_keywords \"1364-2001\"\n"
                              "module t;\n"
                              "  wire logic;\n"
                              "endmodule\n"
                              "`end_keywords\n"));
}

TEST(KeywordVersionParsing, OldVersionIdentifierNamesADesignElement) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`begin_keywords \"1364-2001\"\n"
                              "module logic;\n"
                              "endmodule\n"
                              "`end_keywords\n"));

  EXPECT_FALSE(
      ParseWithPreprocessorOk("`begin_keywords \"1800-2005\"\n"
                              "module logic;\n"
                              "endmodule\n"
                              "`end_keywords\n"));
}

TEST(KeywordVersionParsing, OldVersionIdentifierNamesAParameter) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`begin_keywords \"1364-2001\"\n"
                              "module t;\n"
                              "  parameter logic = 4;\n"
                              "endmodule\n"
                              "`end_keywords\n"));

  EXPECT_FALSE(
      ParseWithPreprocessorOk("`begin_keywords \"1800-2005\"\n"
                              "module t;\n"
                              "  parameter logic = 4;\n"
                              "endmodule\n"
                              "`end_keywords\n"));
}

TEST(KeywordVersionParsing, OldVersionIdentifierNamesAPort) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`begin_keywords \"1364-2001\"\n"
                              "module t (input wire logic);\n"
                              "endmodule\n"
                              "`end_keywords\n"));
}

// §22.14 states its placement rule against the design elements of §3.2, and
// the region it opens governs whatever follows regardless of which kind those
// elements are. A package and an interface, in their real §3.2 syntax, both
// sit inside one 1800-2005 region — a version that reserves `package` and
// `interface` but not yet `until` and `global`, so those two words are still
// ordinary identifiers inside each element.
TEST(KeywordVersionParsing, RegionCoversNonModuleDesignElements) {
  const std::string src =
      "package pkg;\n"
      "  parameter until = 3;\n"
      "endpackage\n"
      "interface intf;\n"
      "  wire global;\n"
      "endinterface\n"
      "module t;\n"
      "endmodule\n";

  EXPECT_TRUE(ParseWithPreprocessorOk("`begin_keywords \"1800-2005\"\n" + src +
                                      "`end_keywords\n"));

  // The negative: 1800-2009 added both words to the reserved list, so the very
  // same package and interface no longer parse.
  EXPECT_FALSE(ParseWithPreprocessorOk("`begin_keywords \"1800-2009\"\n" + src +
                                       "`end_keywords\n"));
}

// The §3.2 restriction seen through the whole front end rather than only at
// the preprocessor: a directive placed inside a package fails the run.
TEST(KeywordVersionParsing, ErrorDirectiveInsideNonModuleDesignElement) {
  EXPECT_FALSE(
      ParseWithPreprocessorOk("package pkg;\n"
                              "`begin_keywords \"1364-2001\"\n"
                              "endpackage\n"
                              "`end_keywords\n"));
}

// The negative side of the same rule: the version_specifier says which
// identifiers are reserved, so under a version that does reserve `logic` the
// very same declaration is no longer a legal net name.
TEST(KeywordVersionParsing, ReservedWordCannotNameNetUnderSelectedVersion) {
  EXPECT_FALSE(
      ParseWithPreprocessorOk("`begin_keywords \"1800-2005\"\n"
                              "module t;\n"
                              "  wire logic;\n"
                              "endmodule\n"
                              "`end_keywords\n"));
}

// §22.14: with no `begin_keywords in effect the implementation's default
// reserved word list applies. This implementation defaults to 1800-2023, which
// reserves `logic`, so the declaration that 1364-2001 accepts is rejected when
// no directive selects a version at all.
TEST(KeywordVersionParsing, DefaultKeywordSetAppliesWithNoDirective) {
  EXPECT_FALSE(
      ParseWithPreprocessorOk("module t;\n"
                              "  wire logic;\n"
                              "endmodule\n"));
}

// §22.14: the region a `begin_keywords opens runs only until the matching
// `end_keywords. The first module sits inside a 1364-2001 region and may use
// `logic` as a net name; the second sits after the closing directive, where
// the default list is back in force and rejects it.
TEST(KeywordVersionParsing, RegionEndsAtMatchingEndKeywords) {
  EXPECT_FALSE(
      ParseWithPreprocessorOk("`begin_keywords \"1364-2001\"\n"
                              "module inside;\n"
                              "  wire logic;\n"
                              "endmodule\n"
                              "`end_keywords\n"
                              "module outside;\n"
                              "  wire logic;\n"
                              "endmodule\n"));
}

// §22.14: nested pairs are stacked, and closing one returns to the specifier
// that was in effect before it. The inner 1364-2001 region lets `logic` name a
// net; once it closes, the enclosing 1800-2012 region reserves the word again.
TEST(KeywordVersionParsing, NestedRegionRestoresEnclosingVersion) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`begin_keywords \"1800-2012\"\n"
                              "`begin_keywords \"1364-2001\"\n"
                              "module inner;\n"
                              "  wire logic;\n"
                              "endmodule\n"
                              "`end_keywords\n"
                              "module outer;\n"
                              "  logic w;\n"
                              "endmodule\n"
                              "`end_keywords\n"));

  EXPECT_FALSE(
      ParseWithPreprocessorOk("`begin_keywords \"1800-2012\"\n"
                              "`begin_keywords \"1364-2001\"\n"
                              "module inner;\n"
                              "  wire logic;\n"
                              "endmodule\n"
                              "`end_keywords\n"
                              "module outer;\n"
                              "  wire logic;\n"
                              "endmodule\n"
                              "`end_keywords\n"));
}

}  // namespace
