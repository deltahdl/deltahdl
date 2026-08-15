#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// The line each rejection below is reported at is counted in the
// preprocessor's output rather than in the source written here. Every
// `begin_keywords and `end_keywords leaves a blank line in that output on top
// of its own directive line (#3095), so each directive line above a source
// line pushes that line down by two.

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

  // §23.2.1 owns the report: the word stands where Parser::ParseModuleDecl
  // reads the module's own name.
  auto r = ParseWithPreprocessor(
      "`begin_keywords \"1800-2005\"\n"
      "module logic;\n"
      "endmodule\n"
      "`end_keywords\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got token", 3, "23.2.1"));
}

TEST(KeywordVersionParsing, OldVersionIdentifierNamesAParameter) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`begin_keywords \"1364-2001\"\n"
                              "module t;\n"
                              "  parameter logic = 4;\n"
                              "endmodule\n"
                              "`end_keywords\n"));

  // §6.20.1 owns the report. Once `logic` is a keyword it is read as the
  // parameter's data type, so Parser::ParseParamDecl is looking for the
  // parameter's name when it reaches the '='.
  auto r = ParseWithPreprocessor(
      "`begin_keywords \"1800-2005\"\n"
      "module t;\n"
      "  parameter logic = 4;\n"
      "endmodule\n"
      "`end_keywords\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got '='", 4, "6.20.1"));
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
  const std::string kSrc =
      "package pkg;\n"
      "  parameter until = 3;\n"
      "endpackage\n"
      "interface intf;\n"
      "  wire global;\n"
      "endinterface\n"
      "module t;\n"
      "endmodule\n";

  EXPECT_TRUE(ParseWithPreprocessorOk("`begin_keywords \"1800-2005\"\n" + kSrc +
                                      "`end_keywords\n"));

  // The negative: 1800-2009 added both words to the reserved list, so the very
  // same package and interface no longer parse. §6.20.1 owns the report on the
  // first of the two, where the reserved word stands in the parameter's name
  // slot.
  auto r = ParseWithPreprocessor("`begin_keywords \"1800-2009\"\n" + kSrc +
                                 "`end_keywords\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got token", 4, "6.20.1"));
}

// The §3.2 restriction seen through the whole front end rather than only at
// the preprocessor: a directive placed inside a package fails the run.
TEST(KeywordVersionParsing, ErrorDirectiveInsideNonModuleDesignElement) {
  // The preprocessor rejects this one and the parser never sees it, so the
  // report is Preprocessor::RejectInsideDesignElement's, and its location is
  // the directive's line in the source as written rather than in the output.
  auto r = ParseWithPreprocessor(
      "package pkg;\n"
      "`begin_keywords \"1364-2001\"\n"
      "endpackage\n"
      "`end_keywords\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "`begin_keywords illegal inside a design element", 2, "22.14"));
}

// The negative side of the same rule: the version_specifier says which
// identifiers are reserved, so under a version that does reserve `logic` the
// very same declaration is no longer a legal net name.
TEST(KeywordVersionParsing, ReservedWordCannotNameNetUnderSelectedVersion) {
  // §6.7 owns the report rather than §6.8: once `logic` is a keyword the
  // declaration reads as the net type `wire` carrying the data type `logic`,
  // and Parser::ParseVarDeclList files a net declaration's name under §6.7.
  // The name it is then looking for is the semicolon.
  auto r = ParseWithPreprocessor(
      "`begin_keywords \"1800-2005\"\n"
      "module t;\n"
      "  wire logic;\n"
      "endmodule\n"
      "`end_keywords\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected identifier, got ';'", 4, "6.7"));
}

// §22.14: with no `begin_keywords in effect the implementation's default
// reserved word list applies. This implementation defaults to 1800-2023, which
// reserves `logic`, so the declaration that 1364-2001 accepts is rejected when
// no directive selects a version at all.
TEST(KeywordVersionParsing, DefaultKeywordSetAppliesWithNoDirective) {
  // No directive stands above the declaration, so the line it is reported at
  // is the line it is written on.
  auto r = ParseWithPreprocessor(
      "module t;\n"
      "  wire logic;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected identifier, got ';'", 2, "6.7"));
}

// §22.14: the region a `begin_keywords opens runs only until the matching
// `end_keywords. The first module sits inside a 1364-2001 region and may use
// `logic` as a net name; the second sits after the closing directive, where
// the default list is back in force and rejects it.
TEST(KeywordVersionParsing, RegionEndsAtMatchingEndKeywords) {
  // The second declaration is written on line 7 and reported on line 9: one
  // `begin_keywords and one `end_keywords stand above it, each of which costs
  // two output lines.
  auto r = ParseWithPreprocessor(
      "`begin_keywords \"1364-2001\"\n"
      "module inside;\n"
      "  wire logic;\n"
      "endmodule\n"
      "`end_keywords\n"
      "module outside;\n"
      "  wire logic;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected identifier, got ';'", 9, "6.7"));
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

  // The outer module's declaration is written on line 8 and reported on line
  // 11: three directives stand above it, each costing two output lines.
  auto r = ParseWithPreprocessor(
      "`begin_keywords \"1800-2012\"\n"
      "`begin_keywords \"1364-2001\"\n"
      "module inner;\n"
      "  wire logic;\n"
      "endmodule\n"
      "`end_keywords\n"
      "module outer;\n"
      "  wire logic;\n"
      "endmodule\n"
      "`end_keywords\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got ';'", 11, "6.7"));
}

}  // namespace
