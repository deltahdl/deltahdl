#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "fixture_protect_read.h"
#include "helpers_reported_error.h"
#include "helpers_text_lines.h"
#include "preprocessor/protect_envelope.h"

using namespace delta;

namespace {

TEST(ProtectBeginSyntax, TheWordAloneOpensAnEncryptionEnvelope) {
  ReadSource run("`pragma protect begin\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 1U);
}

TEST(ProtectBeginSyntax, TheEnvelopeItOpenedIsTheOneThatWasClosed) {
  ReadSource run(
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 0U);
  ASSERT_EQ(run.Closed().size(), 1U);
  EXPECT_EQ(run.Closed().front().mode, EnvelopeMode::kEncryption);
}

TEST(ProtectBeginSyntax, TheDirectiveCarryingTheWordContributesNoText) {
  ReadSource run(
      "module secret;\n"
      "`pragma protect begin\n"
      "endmodule\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(Holds(run.text, "pragma"));
  EXPECT_TRUE(Holds(run.text, "module secret;"));
  EXPECT_TRUE(Holds(run.text, "endmodule"));
}

TEST(ProtectBeginSyntax, TheWordLastAfterValuedExpressionsStillOpens) {
  ReadSource run(
      "`pragma protect author=\"Acme Corp\", "
      "data_method=\"x-caesar\", begin\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 1U);
}

TEST(ProtectBeginSyntax, TheWordFirstAheadOfAValuedExpressionStillOpens) {
  ReadSource run("`pragma protect begin, comment=\"the region below\"\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 1U);
}

TEST(ProtectBeginSyntax, TheWordAloneOnItsOwnDirectiveStillOpens) {
  ReadSource run(
      "`pragma protect author=\"Acme Corp\"\n"
      "`pragma protect begin\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 1U);
}

TEST(ProtectBeginSyntax, AMacroExpandingToTheWordOpensTheEnvelope) {
  ReadSource run(
      "`define OPEN begin\n"
      "`pragma protect `OPEN\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 1U);
}

TEST(ProtectBeginSyntax, ACommentAfterTheWordLeavesItStandingAlone) {
  ReadSource run("`pragma protect begin // the region starts here\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 1U);
}

TEST(ProtectBeginSyntax, TheEncryptingHalfTakesTheWordAloneAsItsDelimiter) {
  std::string written = EncryptedByTheAuthor(
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n");
  EXPECT_TRUE(Holds(written, "`pragma protect begin_protected\n"));
  EXPECT_TRUE(Holds(written, "`pragma protect data_block\n"));
  EXPECT_FALSE(Holds(written, "initial result = 42;"));
}

TEST(ProtectBeginSyntax, ARegionTheWordOpenedComesBackUnderTheAuthorsKey) {
  std::string written = EncryptedByTheAuthor(
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n");
  ReadSource run(written, kReadingExchangeKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, "initial result = 42;"));
  EXPECT_FALSE(Holds(run.text, "data_block"));
}

TEST(ProtectBeginSyntax, AStringWrittenAgainstTheWordIsReported) {
  ReadSource run("`pragma protect begin=\"now\"\n");
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma begin keyword is written on its own and takes no "
      "pragma_value",
      1, "34.5.1.1"));
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 0U);
}

TEST(ProtectBeginSyntax, AParenthesizedValueAgainstTheWordIsReported) {
  ReadSource run("`pragma protect begin=(enctype=\"raw\")\n");
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma begin keyword is written on its own and takes no "
      "pragma_value",
      1, "34.5.1.1"));
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 0U);
}

TEST(ProtectBeginSyntax, AWordWrittenProperlyAfterAReportedOneStillOpens) {
  ReadSource run(
      "`pragma protect begin=\"now\"\n"
      "`pragma protect begin\n");
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma begin keyword is written on its own and takes no "
      "pragma_value",
      1, "34.5.1.1"));
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 1U);
}

TEST(ProtectBeginSyntax, TheValuedWordDelimitsNothingForTheEncryptingHalf) {
  std::string src =
      "`pragma protect begin=\"now\"\n"
      "  initial result = 42;\n"
      "`pragma protect end\n";
  std::string written = EncryptedByTheAuthor(src);
  EXPECT_EQ(written, src);
  EXPECT_FALSE(Holds(written, "data_block"));
}

TEST(ProtectBeginSyntax, AParenthesizedValueDelimitsNothingWhenEncrypting) {
  std::string src =
      "`pragma protect begin=(enctype=\"raw\")\n"
      "  initial result = 42;\n"
      "`pragma protect end\n";
  EXPECT_EQ(EncryptedByTheAuthor(src), src);
}

TEST(ProtectBeginSyntax, ADirectiveWithNoWordAheadOfItsValueDelimitsNothing) {
  std::string src =
      "`pragma protect =\"now\"\n"
      "  initial result = 42;\n"
      "`pragma protect end\n";
  EXPECT_EQ(EncryptedByTheAuthor(src), src);
}

TEST(ProtectBeginSyntax, AValuedWordLeavesTheDesignUnprotectedEndToEnd) {
  std::string written = EncryptedByTheAuthor(
      "`pragma protect begin=\"now\"\n"
      "  initial result = 42;\n"
      "`pragma protect end\n");
  ReadSource run(written, kReadingExchangeKey);
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma begin keyword is written on its own and takes no "
      "pragma_value",
      LineHolding(written, "begin=\"now\""), "34.5.1.1"));
  EXPECT_TRUE(Holds(run.text, "initial result = 42;"));
}

TEST(ProtectBeginSyntax, TheLettersAsAnEscapedIdentifierAreNotTheWord) {
  ReadSource run("`pragma protect \\begin\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 0U);
}

TEST(ProtectBeginSyntax, TheWordInAnotherCaseIsNotTheWord) {
  ReadSource run("`pragma protect BEGIN\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 0U);
}

TEST(ProtectBeginSyntax, ALongerReservedNameSharingItsLettersIsNotTheWord) {
  ReadSource run("`pragma protect begin_protected\n");
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 0U);
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 1U);
}

TEST(ProtectBeginSyntax, TheWordWrittenAsAValueOpensNothing) {
  ReadSource run("`pragma protect author=begin\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 0U);
}

TEST(ProtectBeginSyntax, TheWordUnderAnotherPragmaNameOpensNothing) {
  ReadSource run("`pragma acme begin\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 0U);
}

TEST(ProtectBeginSyntax, TheWordAsThePragmaNameOpensNothing) {
  ReadSource run("`pragma begin\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 0U);
}

TEST(ProtectBeginSyntax, TheWordInsideAParenthesizedValueOpensNothing) {
  ReadSource run("`pragma protect encoding=(begin)\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 0U);
}

TEST(ProtectBeginSyntax, TheWordInsideAParenthesizedValueDelimitsNothing) {
  std::string src =
      "`pragma protect encoding=(begin)\n"
      "  initial result = 42;\n"
      "`pragma protect end\n";
  EXPECT_EQ(EncryptedByTheAuthor(src), src);
}

TEST(ProtectBeginSyntax, LongerNamesAroundTheWordDelimitNothingWhenEncrypting) {
  for (const char* opening :
       {"`pragma protect begin$now\n", "`pragma protect _begin\n",
        "`pragma protectx begin\n"}) {
    std::string src = opening;
    src.append("  initial result = 42;\n`pragma protect end\n");
    EXPECT_EQ(EncryptedByTheAuthor(src), src) << opening;
  }
}

TEST(ProtectBeginSyntax, TheBarePragmaNameInsideARegionChangesNothing) {
  std::string written = EncryptedByTheAuthor(
      "`pragma protect begin\n`pragma protect\n  initial result = 42;\n"
      "`pragma protect end\n`pragma protect");
  EXPECT_FALSE(Holds(written, "initial result = 42;")) << written;
  EXPECT_TRUE(Holds(written, "data_block")) << written;
  EXPECT_TRUE(written.ends_with("\n`pragma protect")) << written;
}

}  // namespace
