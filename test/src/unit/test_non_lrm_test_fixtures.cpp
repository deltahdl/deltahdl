#include <gtest/gtest-spi.h>
#include <gtest/gtest.h>

#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "fixture_elaborator.h"
#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

bool Reported(const std::vector<Diagnostic>& diags, std::string_view message) {
  for (const auto& diag : diags) {
    if (diag.message == message) return true;
  }
  return false;
}

TEST(ElaboratorHarness, ASourceThatDoesNotParseFailsTheCaseThatWroteIt) {
  EXPECT_NONFATAL_FAILURE(ElabOk("module m;\n"
                                 "  wire before;\n"
                                 "endmodule\n"),
                          "did not parse");
}

TEST(ElaboratorHarness, ASourceTheElaboratorRejectsIsReportedAsRejected) {
  EXPECT_FALSE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "class C implements IC;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ElaboratorHarness, ASourceTheElaboratorAcceptsIsReportedAsAccepted) {
  EXPECT_TRUE(ElabOk("module m;\nendmodule\n"));
}

TEST(ElaboratorHarness, AnElaborationRejectionIsReadableByItsMessage) {
  ElabFixture f;

  EXPECT_FALSE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "class C implements IC;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(Reported(f.diag.Diagnostics(),
                       "class 'C' does not implement pure virtual method "
                       "'foo' from interface 'IC'"));
}

TEST(ElaboratorHarness, AnAcceptedElaborationLeavesTheEngineEmpty) {
  ElabFixture f;

  EXPECT_TRUE(ElabOk("module m;\nendmodule\n", f));
  EXPECT_TRUE(f.diag.Diagnostics().empty());
}

TEST(ParserHarness, AParseRejectionIsReadableByItsMessageAndPosition) {
  auto result = Parse(
      "module m;\n"
      "endmodule\n"
      "    %\n");

  EXPECT_TRUE(ReportedError(result.diags, "expected top-level declaration", 3,
                            "3.12.1"));
}

TEST(ParserHarness, AnAcceptedParseKeepsNoDiagnostic) {
  auto result = Parse("module m;\nendmodule\n");

  EXPECT_FALSE(result.has_errors);
  EXPECT_TRUE(result.diags.empty());
}

TEST(ParserHarness, ALibraryTextRejectionIsReadableByItsMessage) {
  auto result = ParseLibrary("module m;\nendmodule\n");

  EXPECT_TRUE(Reported(result.diags,
                       "expected library declaration, include statement, "
                       "config declaration, or ';'"));
}

TEST(ParserHarness, AnAcceptedLibraryTextKeepsNoDiagnostic) {
  auto result = ParseLibrary("library work \"work/*.sv\";\n");

  EXPECT_FALSE(result.has_errors);
  EXPECT_TRUE(result.diags.empty());
}

TEST(ParserHarness, ADiagnosticReportedBeforeTheParseSurvivesIt) {
  auto result = ParseWithPreprocessor(
      "module m;\n"
      "endmodule\n"
      "`end_keywords\n");

  EXPECT_TRUE(ReportedError(result.diags,
                            "`end_keywords without matching `begin_keywords", 3,
                            "22.14"));
}

TEST(ParserHarness, AnAcceptedPreprocessedSourceKeepsNoDiagnostic) {
  auto result = ParseWithPreprocessor(
      "`define WIDTH 4\n"
      "module m;\n"
      "  wire [`WIDTH-1:0] w;\n"
      "endmodule\n");

  EXPECT_FALSE(result.has_errors);
  EXPECT_TRUE(result.diags.empty());
}

TEST(ParserHarness, ParseOkTellsAnAcceptedSourceFromARejectedOne) {
  EXPECT_TRUE(ParseOk("module m;\nendmodule\n"));
  EXPECT_FALSE(ParseOk("module m;\nendmodule\n    %\n"));
}

TEST(ParserHarness, ParseWithPreprocessorOkTellsAnAcceptedSourceFromARejected) {
  EXPECT_TRUE(
      ParseWithPreprocessorOk("`define WIDTH 4\n"
                              "module m;\n"
                              "  wire [`WIDTH-1:0] w;\n"
                              "endmodule\n"));
  EXPECT_FALSE(
      ParseWithPreprocessorOk("module m;\n"
                              "endmodule\n"
                              "`end_keywords\n"));
}

}  // namespace
