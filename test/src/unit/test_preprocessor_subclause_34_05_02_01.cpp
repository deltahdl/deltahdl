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

std::string RegionClosedWith(std::string_view closing) {
  std::string text = "`pragma protect begin\n";
  text.append("  initial result = 42;\n");
  text.append(closing);
  return text;
}

TEST(ProtectEndSyntax, TheWordAloneClosesTheEnvelopeThatWasOpen) {
  ReadSource run(RegionClosedWith("`pragma protect end\n"));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 0U);
  ASSERT_EQ(run.Closed().size(), 1U);
  EXPECT_EQ(run.Closed().front().mode, EnvelopeMode::kEncryption);
}

TEST(ProtectEndSyntax, TheDirectiveCarryingTheWordContributesNoText) {
  ReadSource run(
      "module secret;\n"
      "`pragma protect begin\n"
      "`pragma protect end\n"
      "endmodule\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(Holds(run.text, "pragma"));
  EXPECT_TRUE(Holds(run.text, "module secret;"));
  EXPECT_TRUE(Holds(run.text, "endmodule"));
}

TEST(ProtectEndSyntax, TheWordLastAfterValuedExpressionsStillCloses) {
  std::string closing =
      "`pragma protect author=\"Acme Corp\", data_method=\"x-caesar\", end\n";
  ReadSource run(RegionClosedWith(closing));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 0U);
}

TEST(ProtectEndSyntax, TheWordFirstAheadOfAValuedExpressionStillCloses) {
  std::string closing = "`pragma protect end, comment=\"above\"\n";
  ReadSource run(RegionClosedWith(closing));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 0U);
}

TEST(ProtectEndSyntax, TheWordAloneOnItsOwnDirectiveStillCloses) {
  std::string closing = "`pragma protect comment=\"sealed\"\n";
  closing.append("`pragma protect end\n");
  ReadSource run(RegionClosedWith(closing));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 0U);
}

TEST(ProtectEndSyntax, AMacroExpandingToTheWordClosesTheEnvelope) {
  std::string src = "`define CLOSE end\n";
  src.append(RegionClosedWith("`pragma protect `CLOSE\n"));
  ReadSource run(src);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 0U);
}

TEST(ProtectEndSyntax, ACommentAfterTheWordLeavesItStandingAlone) {
  std::string closing = "`pragma protect end // the region stops here\n";
  ReadSource run(RegionClosedWith(closing));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 0U);
}

TEST(ProtectEndSyntax, TheEncryptingHalfTakesTheWordAloneAsItsDelimiter) {
  std::string written =
      EncryptedByTheAuthor(RegionClosedWith("`pragma protect end\n"));
  EXPECT_TRUE(Holds(written, "`pragma protect end_protected\n"));
  EXPECT_TRUE(Holds(written, "`pragma protect data_block\n"));
  EXPECT_FALSE(Holds(written, "initial result = 42;"));
}

TEST(ProtectEndSyntax, TheTextAfterTheWordIsOutsideTheRegionItClosed) {
  std::string src = RegionClosedWith("`pragma protect end\n");
  src.append("  initial published = 7;\n");
  std::string written = EncryptedByTheAuthor(src);
  EXPECT_FALSE(Holds(written, "initial result = 42;"));
  EXPECT_TRUE(Holds(written, "initial published = 7;"));
}

TEST(ProtectEndSyntax, ARegionTheWordClosedComesBackUnderTheAuthorsKey) {
  std::string written =
      EncryptedByTheAuthor(RegionClosedWith("`pragma protect end\n"));
  ReadSource run(written, kReadingExchangeKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, "initial result = 42;"));
  EXPECT_FALSE(Holds(run.text, "data_block"));
}

TEST(ProtectEndSyntax, AStringWrittenAgainstTheWordIsReported) {
  std::string closing = "`pragma protect end=\"now\"\n";
  ReadSource run(RegionClosedWith(closing));
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma end keyword is written on its own and takes no "
      "pragma_value",
      3, "34.5.2.1"));
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 1U);
  EXPECT_TRUE(run.Closed().empty());
}

TEST(ProtectEndSyntax, AParenthesizedValueAgainstTheWordIsReported) {
  std::string closing = "`pragma protect end=(enctype=\"raw\")\n";
  ReadSource run(RegionClosedWith(closing));
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma end keyword is written on its own and takes no "
      "pragma_value",
      3, "34.5.2.1"));
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 1U);
}

TEST(ProtectEndSyntax, AWordWrittenProperlyAfterAReportedOneStillCloses) {
  std::string closing = "`pragma protect end=\"now\"\n";
  closing.append("`pragma protect end\n");
  ReadSource run(RegionClosedWith(closing));
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma end keyword is written on its own and takes no "
      "pragma_value",
      3, "34.5.2.1"));
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 0U);
  EXPECT_EQ(run.Closed().size(), 1U);
}

TEST(ProtectEndSyntax, TheValuedWordDelimitsNothingForTheEncryptingHalf) {
  std::string src = RegionClosedWith("`pragma protect end=\"now\"\n");
  std::string written = EncryptedByTheAuthor(src);
  EXPECT_EQ(written, src);
  EXPECT_FALSE(Holds(written, "data_block"));
}

TEST(ProtectEndSyntax, AParenthesizedValueDelimitsNothingWhenEncrypting) {
  std::string closing = "`pragma protect end=(enctype=\"raw\")\n";
  std::string src = RegionClosedWith(closing);
  EXPECT_EQ(EncryptedByTheAuthor(src), src);
}

TEST(ProtectEndSyntax, AValuedWordIsEncryptedAsTextOfTheRegionItLeftOpen) {
  std::string closing = "`pragma protect end=\"now\"\n";
  closing.append("`pragma protect end\n");
  std::string written = EncryptedByTheAuthor(RegionClosedWith(closing));
  EXPECT_TRUE(Holds(written, "`pragma protect data_block\n"));
  EXPECT_FALSE(Holds(written, "end=\"now\""));
}

TEST(ProtectEndSyntax, AValuedWordLeavesTheDesignUnprotectedEndToEnd) {
  std::string closing = "`pragma protect end=\"now\"\n";
  std::string written = EncryptedByTheAuthor(RegionClosedWith(closing));
  ReadSource run(written, kReadingExchangeKey);
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma end keyword is written on its own and takes no "
      "pragma_value",
      LineHolding(written, "end=\"now\""), "34.5.2.1"));
  EXPECT_TRUE(Holds(run.text, "initial result = 42;"));
}

TEST(ProtectEndSyntax, TheLettersAsAnEscapedIdentifierAreNotTheWord) {
  ReadSource run(RegionClosedWith("`pragma protect \\end\n"));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 1U);
}

TEST(ProtectEndSyntax, TheLettersAsAnEscapedIdentifierDelimitNothing) {
  std::string src = RegionClosedWith("`pragma protect \\end\n");
  std::string written = EncryptedByTheAuthor(src);
  EXPECT_EQ(written, src);
  EXPECT_FALSE(Holds(written, "end_protected"));
}

TEST(ProtectEndSyntax, TheWordInAnotherCaseIsNotTheWord) {
  ReadSource run(RegionClosedWith("`pragma protect END\n"));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 1U);
}

TEST(ProtectEndSyntax, TheWordInAnotherCaseDelimitsNothing) {
  std::string src = RegionClosedWith("`pragma protect END\n");
  EXPECT_EQ(EncryptedByTheAuthor(src), src);
}

TEST(ProtectEndSyntax, ALongerReservedNameSharingItsLettersIsNotTheWord) {
  ReadSource run(RegionClosedWith("`pragma protect end_protected\n"));
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 1U);
  EXPECT_TRUE(run.Closed().empty());
}

TEST(ProtectEndSyntax, ALongerReservedNameSharingItsLettersDelimitsNothing) {
  std::string src = RegionClosedWith("`pragma protect end_protected\n");
  EXPECT_EQ(EncryptedByTheAuthor(src), src);
}

TEST(ProtectEndSyntax, TheWordWrittenAsAValueClosesNothing) {
  ReadSource run(RegionClosedWith("`pragma protect comment=end\n"));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 1U);
}

TEST(ProtectEndSyntax, TheWordWrittenAsAValueDelimitsNothing) {
  std::string src = RegionClosedWith("`pragma protect comment=end\n");
  EXPECT_EQ(EncryptedByTheAuthor(src), src);
}

TEST(ProtectEndSyntax, TheWordUnderAnotherPragmaNameClosesNothing) {
  ReadSource run(RegionClosedWith("`pragma acme end\n"));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 1U);
}

TEST(ProtectEndSyntax, TheWordUnderAnotherPragmaNameDelimitsNothing) {
  std::string src = RegionClosedWith("`pragma acme end\n");
  EXPECT_EQ(EncryptedByTheAuthor(src), src);
}

TEST(ProtectEndSyntax, TheWordAsThePragmaNameClosesNothing) {
  ReadSource run(RegionClosedWith("`pragma end\n"));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 1U);
}

TEST(ProtectEndSyntax, TheWordInsideAParenthesizedValueClosesNothing) {
  ReadSource run(RegionClosedWith("`pragma protect encoding=(end)\n"));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 1U);
}

TEST(ProtectEndSyntax, TheWordInsideAParenthesizedValueDelimitsNothing) {
  std::string src = RegionClosedWith("`pragma protect encoding=(end)\n");
  EXPECT_EQ(EncryptedByTheAuthor(src), src);
}

}  // namespace
