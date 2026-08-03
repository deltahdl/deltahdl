#include <gtest/gtest-spi.h>
#include <gtest/gtest.h>

#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "fixture_elaborator.h"
#include "fixture_parser.h"

using namespace delta;

namespace {

// Whether any record a run kept carries this message. A run may report more
// than one thing, and a case naming the rule it is about is asking whether the
// rule was what failed, not which position in the record it landed at.
bool Reported(const std::vector<Diagnostic>& diags, std::string_view message) {
  for (const auto& diag : diags) {
    if (diag.message == message) return true;
  }
  return false;
}

// A shared harness answers a question, and a case trusts the answer to be
// about what it asked. Where the answer is that something is absent -- no
// module, no binding, no diagnostic -- a source that never parsed produces the
// same answer the rule under test does, and the case passes whether the rule
// is implemented, implemented backwards, or absent. That is the shape these
// three pin: the harness must tell a source it could not read from a source it
// read and rejected, and it must go on telling an accepted source from a
// rejected one, or the first claim would be satisfied by a harness that
// complains about everything.

TEST(ElaboratorHarness, ASourceThatDoesNotParseFailsTheCaseThatWroteIt) {
  // `before` is reserved by Table B.1, so this declares no net and the module
  // does not parse. The keyword scan over test/src/ reads design elements and
  // deliberately leaves nets alone, which makes a net the one shape of this
  // defect only the harness can catch -- and the reason the two are
  // complementary rather than one of them being redundant.
  EXPECT_NONFATAL_FAILURE(ElabOk("module m;\n"
                                 "  wire before;\n"
                                 "endmodule\n"),
                          "did not parse");
}

TEST(ElaboratorHarness, ASourceTheElaboratorRejectsIsReportedAsRejected) {
  // Parses, so the harness has no complaint of its own; §8.26 rejects it,
  // which is the answer the case asked for. Without this the claim above
  // would be met by a harness that failed every case handed to it.
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
  // The other half of the control: a harness that answered "rejected" to
  // everything would satisfy the case above and fail this one.
  EXPECT_TRUE(ElabOk("module m;\nendmodule\n"));
}

TEST(ElaboratorHarness, AnElaborationRejectionIsReadableByItsMessage) {
  // §8.26 obliges a class that implements an interface class to implement
  // every pure virtual method the interface declares, and this class
  // implements none of them. The two-argument form leaves the engine that
  // recorded the diagnostic with the caller, which is what lets a case name
  // the rule it is about instead of asserting that something went wrong.
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
  // A harness that reported something about every source would satisfy the
  // case above whatever §8.26 does.
  ElabFixture f;

  EXPECT_TRUE(ElabOk("module m;\nendmodule\n", f));
  EXPECT_TRUE(f.diag.Diagnostics().empty());
}

// The parser harness builds its engine, reads one boolean out of it and lets
// it go, so the record of what a run reported used to be destroyed before the
// case that asked for the run could see it. These cases pin the copy that
// keeps it: a rejection is read back by the message that caused it, and by the
// position the record carries where the harness reports one. Each is paired
// with a source the same call accepts, because a harness that recorded
// something for every source would satisfy the rejections on its own.

TEST(ParserHarness, AParseRejectionIsReadableByItsMessageAndPosition) {
  // The '%' follows four spaces on the third line, so a record that kept the
  // location a default-constructed record carries, or that swapped the line
  // for the column, reads differently from one that kept what was reported.
  auto result = Parse(
      "module m;\n"
      "endmodule\n"
      "    %\n");

  ASSERT_EQ(result.diags.size(), 1u);
  EXPECT_EQ(result.diags.front().message, "expected top-level declaration");
  EXPECT_EQ(result.diags.front().loc.line, 3u);
  EXPECT_EQ(result.diags.front().loc.column, 5u);
}

TEST(ParserHarness, AnAcceptedParseKeepsNoDiagnostic) {
  auto result = Parse("module m;\nendmodule\n");

  EXPECT_FALSE(result.has_errors);
  EXPECT_TRUE(result.diags.empty());
}

TEST(ParserHarness, ALibraryTextRejectionIsReadableByItsMessage) {
  // §33.3 gives library text library declarations, include statements and
  // configurations, and a module is none of the three.
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
  // §22.14 pairs `end_keywords with a `begin_keywords before it, and there is
  // none. The preprocessor reports that, and the source the parser then reads
  // is one it has no complaint of its own about, so the message reaches the
  // case only if the harness keeps what the whole run recorded.
  auto result = ParseWithPreprocessor(
      "module m;\n"
      "endmodule\n"
      "`end_keywords\n");

  ASSERT_FALSE(result.diags.empty());
  EXPECT_EQ(result.diags.front().message,
            "`end_keywords without matching `begin_keywords");
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
  // ParseOk answers out of the same run that keeps the diagnostics above, so
  // this is what holds the answer the 1,508 acceptance assertions read to what
  // it was before that run became the one they go through.
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
