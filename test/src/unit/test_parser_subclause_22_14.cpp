#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

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

  auto r = ParseWithPreprocessor(
      "`begin_keywords \"1800-2005\"\n"
      "module logic;\n"
      "endmodule\n"
      "`end_keywords\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got 'logic'", 2, "23.2.1"));
}

TEST(KeywordVersionParsing, OldVersionIdentifierNamesAParameter) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`begin_keywords \"1364-2001\"\n"
                              "module t;\n"
                              "  parameter logic = 4;\n"
                              "endmodule\n"
                              "`end_keywords\n"));

  auto r = ParseWithPreprocessor(
      "`begin_keywords \"1800-2005\"\n"
      "module t;\n"
      "  parameter logic = 4;\n"
      "endmodule\n"
      "`end_keywords\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got '='", 3, "6.20.1"));
}

TEST(KeywordVersionParsing, OldVersionIdentifierNamesAPort) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`begin_keywords \"1364-2001\"\n"
                              "module t (input wire logic);\n"
                              "endmodule\n"
                              "`end_keywords\n"));
}

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

  auto r = ParseWithPreprocessor("`begin_keywords \"1800-2009\"\n" + kSrc +
                                 "`end_keywords\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got 'until'", 3, "6.20.1"));
}

TEST(KeywordVersionParsing, ErrorDirectiveInsideNonModuleDesignElement) {
  auto r = ParseWithPreprocessor(
      "package pkg;\n"
      "`begin_keywords \"1364-2001\"\n"
      "endpackage\n"
      "`end_keywords\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "`begin_keywords illegal inside a design element", 2, "22.14"));
}

TEST(KeywordVersionParsing, ReservedWordCannotNameNetUnderSelectedVersion) {
  auto r = ParseWithPreprocessor(
      "`begin_keywords \"1800-2005\"\n"
      "module t;\n"
      "  wire logic;\n"
      "endmodule\n"
      "`end_keywords\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected identifier, got ';'", 3, "6.7"));
}

TEST(KeywordVersionParsing, DefaultKeywordSetAppliesWithNoDirective) {
  auto r = ParseWithPreprocessor(
      "module t;\n"
      "  wire logic;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected identifier, got ';'", 2, "6.7"));
}

TEST(KeywordVersionParsing, RegionEndsAtMatchingEndKeywords) {
  auto r = ParseWithPreprocessor(
      "`begin_keywords \"1364-2001\"\n"
      "module inside;\n"
      "  wire logic;\n"
      "endmodule\n"
      "`end_keywords\n"
      "module outside;\n"
      "  wire logic;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected identifier, got ';'", 7, "6.7"));
}

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
  EXPECT_TRUE(ReportedError(r.diags, "expected identifier, got ';'", 8, "6.7"));
}

}  // namespace
