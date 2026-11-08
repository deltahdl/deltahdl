#include <gtest/gtest.h>

#include <cstddef>
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
  std::string text = "`pragma protect begin_protected\n";
  text.append(closing);
  return text;
}

std::string Design() {
  std::string text = "`pragma protect begin\n";
  text.append("  initial result = 42;\n");
  text.append("`pragma protect end\n");
  return text;
}

std::string DesignUnderDeclaredEncoding() {
  std::string text = "`pragma protect begin\n";
  text.append("`pragma protect encoding=(enctype=\"base64\")\n");
  text.append("  initial result = 42;\n");
  text.append("`pragma protect end\n");
  return text;
}

std::string WithValuedClosingWord(const std::string& written) {
  constexpr std::string_view kClosing = "`pragma protect end_protected\n";
  constexpr std::string_view kValued = "`pragma protect end_protected=\"1\"\n";
  size_t at = written.find(kClosing);
  if (at == std::string::npos) return written;
  std::string valued(written);
  valued.replace(at, kClosing.size(), kValued);
  return valued;
}

constexpr std::string_view kStrayBlockDirective =
    "`pragma protect data_block\nnot a block at all\n";

std::string RegionAroundSealedModel(std::string_view closing) {
  std::string text = "`pragma protect begin\n";
  text.append("  initial result = 42;\n");
  text.append("`pragma protect begin_protected\n");
  text.append("`pragma protect author=\"Other Corp\"\n");
  text.append(closing);
  text.append("`pragma protect author=\"Acme Corp\"\n");
  text.append(kStrayBlockDirective);
  text.append("`pragma protect end\n");
  return text;
}

std::string RegionAroundNestedSealedModels() {
  std::string text = "`pragma protect begin\n";
  text.append("  initial result = 42;\n");
  text.append("`pragma protect begin_protected\n");
  text.append("`pragma protect begin_protected\n");
  text.append("`pragma protect end_protected\n");
  text.append("`pragma protect author=\"Other Corp\"\n");
  text.append("`pragma protect end_protected\n");
  text.append("`pragma protect author=\"Acme Corp\"\n");
  text.append("`pragma protect end\n");
  return text;
}

TEST(ProtectEndProtectedSyntax, TheWordAloneClosesTheEnvelopeThatWasOpen) {
  ReadSource run(RegionClosedWith("`pragma protect end_protected\n"));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
  ASSERT_EQ(run.Closed().size(), 1U);
  EXPECT_EQ(run.Closed().front().mode, EnvelopeMode::kDecryption);
}

TEST(ProtectEndProtectedSyntax, TheDirectiveCarryingTheWordContributesNoText) {
  ReadSource run(
      "module sealed;\n"
      "`pragma protect begin_protected\n"
      "`pragma protect end_protected\n"
      "endmodule\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(Holds(run.text, "pragma"));
  EXPECT_TRUE(Holds(run.text, "module sealed;"));
  EXPECT_TRUE(Holds(run.text, "endmodule"));
}

TEST(ProtectEndProtectedSyntax, TheWordLeavesTheOtherModesEnvelopeOpen) {
  ReadSource run(
      "`pragma protect begin\n"
      "`pragma protect begin_protected\n"
      "`pragma protect end_protected\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 1U);
}

TEST(ProtectEndProtectedSyntax, TheWordLastAfterValuedExpressionsStillCloses) {
  std::string closing =
      "`pragma protect author=\"Acme Corp\", data_method=\"x-caesar\", "
      "end_protected\n";
  ReadSource run(RegionClosedWith(closing));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
}

TEST(ProtectEndProtectedSyntax,
     TheWordFirstAheadOfAValuedExpressionStillCloses) {
  ReadSource run(
      RegionClosedWith("`pragma protect end_protected, comment=\"done\"\n"));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
}

TEST(ProtectEndProtectedSyntax, TheWordAloneOnItsOwnDirectiveStillCloses) {
  std::string closing = "`pragma protect comment=\"sealed\"\n";
  closing.append("`pragma protect end_protected\n");
  ReadSource run(RegionClosedWith(closing));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
}

TEST(ProtectEndProtectedSyntax, AMacroExpandingToTheWordClosesTheEnvelope) {
  std::string src = "`define CLOSE end_protected\n";
  src.append(RegionClosedWith("`pragma protect `CLOSE\n"));
  ReadSource run(src);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
}

TEST(ProtectEndProtectedSyntax, ACommentAfterTheWordLeavesItStandingAlone) {
  ReadSource run(RegionClosedWith(
      "`pragma protect end_protected // sealed model ends here\n"));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
}

TEST(ProtectEndProtectedSyntax, TheWordClosesOneOfTwoNestedEnvelopes) {
  ReadSource run(
      "`pragma protect begin_protected\n"
      "`pragma protect begin_protected\n"
      "`pragma protect end_protected\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 1U);
  EXPECT_EQ(run.Closed().size(), 1U);
}

TEST(ProtectEndProtectedSyntax, TextAfterTheWordIsOutsideTheRegionItClosed) {
  std::string src = EncryptedByTheAuthor(Design());
  src.append(kStrayBlockDirective);
  ReadSource run(src, kReadingExchangeKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.Protected());
}

TEST(ProtectEndProtectedSyntax, ARegionTheWordClosesComesBackUnderTheKey) {
  ReadSource run(EncryptedByTheAuthor(Design()), kReadingExchangeKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, "initial result = 42;"));
  EXPECT_FALSE(Holds(run.text, "data_block"));
}

TEST(ProtectEndProtectedSyntax,
     ARegionUnderADeclaredEncodingComesBackThroughTheWord) {
  std::string written = EncryptedByTheAuthor(DesignUnderDeclaredEncoding());
  ASSERT_TRUE(Holds(written, "enctype=\"base64\""));
  ReadSource run(written, kReadingExchangeKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, "initial result = 42;"));
  EXPECT_FALSE(run.Protected());
}

TEST(ProtectEndProtectedSyntax, TheWordAloneEndsASealedModelForEncrypting) {
  std::string src = RegionAroundSealedModel("`pragma protect end_protected\n");
  EncryptionRun run(src);
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(),
                            "data_block is written where no previously",
                            LineHolding(src, "data_block"), "34.5.15"));
}

TEST(ProtectEndProtectedSyntax, TheDesignPastTheWordIsThisEncryptionsOwn) {
  std::string written = EncryptedByTheAuthor(
      RegionAroundSealedModel("`pragma protect end_protected\n"));
  EXPECT_TRUE(Holds(written, "author=\"Acme Corp\""));
  EXPECT_FALSE(Holds(written, "not a block at all"));
  EXPECT_FALSE(Holds(written, "initial result = 42;"));
}

TEST(ProtectEndProtectedSyntax,
     TheSealedModelsDescriptionStopsWhereTheWordStands) {
  std::string written = EncryptedByTheAuthor(
      RegionAroundSealedModel("`pragma protect end_protected\n"));
  EXPECT_FALSE(Holds(written, "author=\"Other Corp\""));
}

TEST(ProtectEndProtectedSyntax, TheWordLastAfterValuedExpressionsEndsTheModel) {
  std::string src = RegionAroundSealedModel(
      "`pragma protect encrypt_agent=\"other-tool\", end_protected\n");
  EncryptionRun run(src);
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(),
                            "data_block is written where no previously",
                            LineHolding(src, "data_block"), "34.5.15"));
}

TEST(ProtectEndProtectedSyntax,
     TheWordFirstAheadOfAValuedExpressionEndsTheModel) {
  std::string src = RegionAroundSealedModel(
      "`pragma protect end_protected, comment=\"done\"\n");
  EncryptionRun run(src);
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(),
                            "data_block is written where no previously",
                            LineHolding(src, "data_block"), "34.5.15"));
}

TEST(ProtectEndProtectedSyntax,
     ACommentAfterTheWordLeavesItStandingAloneWhenEncrypting) {
  std::string src = RegionAroundSealedModel(
      "`pragma protect end_protected // that model ends here\n");
  EncryptionRun run(src);
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(),
                            "data_block is written where no previously",
                            LineHolding(src, "data_block"), "34.5.15"));
}

TEST(ProtectEndProtectedSyntax, TheInnerWordEndsOnlyTheInnerSealedModel) {
  std::string written = EncryptedByTheAuthor(RegionAroundNestedSealedModels());
  EXPECT_FALSE(Holds(written, "author=\"Other Corp\""));
  EXPECT_TRUE(Holds(written, "author=\"Acme Corp\""));
}

TEST(ProtectEndProtectedSyntax, AStringWrittenAgainstTheWordIsReported) {
  ReadSource run(RegionClosedWith("`pragma protect end_protected=\"1\"\n"));
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma end_protected keyword is written on its own and takes "
      "no pragma_value",
      2, "34.5.4.1"));
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 1U);
  EXPECT_TRUE(run.Protected());
  EXPECT_TRUE(run.Closed().empty());
}

TEST(ProtectEndProtectedSyntax, AParenthesizedValueAgainstTheWordIsReported) {
  ReadSource run(
      RegionClosedWith("`pragma protect end_protected=(enctype=\"raw\")\n"));
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma end_protected keyword is written on its own and takes "
      "no pragma_value",
      2, "34.5.4.1"));
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 1U);
}

TEST(ProtectEndProtectedSyntax,
     TheValuedWordDescribesNothingAboutTheOpenEnvelope) {
  ReadSource run(RegionClosedWith("`pragma protect end_protected=\"1\"\n"));
  ASSERT_EQ(run.Open().size(), 1U);
  EXPECT_TRUE(run.Open().front().content_keywords.empty());
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(),
                            "protect pragma end_protected keyword is written "
                            "on its own and takes no pragma_value",
                            2, "34.5.4.1"));
}

TEST(ProtectEndProtectedSyntax, AWordWrittenProperlyAfterAReportedOneCloses) {
  std::string closing = "`pragma protect end_protected=\"1\"\n";
  closing.append("`pragma protect end_protected\n");
  ReadSource run(RegionClosedWith(closing));
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma end_protected keyword is written on its own and takes "
      "no pragma_value",
      2, "34.5.4.1"));
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
  EXPECT_EQ(run.Closed().size(), 1U);
}

TEST(ProtectEndProtectedSyntax, TextAfterAValuedWordIsStillReadAsProtected) {
  std::string src = WithValuedClosingWord(EncryptedByTheAuthor(Design()));
  src.append(kStrayBlockDirective);
  ReadSource run(src, kReadingExchangeKey);
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma end_protected keyword is written on its own and takes "
      "no pragma_value",
      LineHolding(src, "end_protected="), "34.5.4.1"));
  EXPECT_TRUE(run.Protected());
}

TEST(ProtectEndProtectedSyntax, TheValuedWordEndsNoSealedModelWhenEncrypting) {
  EncryptionRun run(
      RegionAroundSealedModel("`pragma protect end_protected=\"1\"\n"));
  EXPECT_EQ(run.diag.ErrorCount(), 0U);
}

TEST(ProtectEndProtectedSyntax,
     AParenthesizedValueEndsNoSealedModelWhenEncrypting) {
  EncryptionRun run(RegionAroundSealedModel(
      "`pragma protect end_protected=(enctype=\"raw\")\n"));
  EXPECT_EQ(run.diag.ErrorCount(), 0U);
}

TEST(ProtectEndProtectedSyntax, TheValuedWordLeavesTheDesignUnsealedEndToEnd) {
  std::string src =
      RegionAroundSealedModel("`pragma protect end_protected=\"1\"\n");
  std::string written = EncryptedByTheAuthor(src);
  EXPECT_EQ(written, src);
  EXPECT_TRUE(Holds(written, "initial result = 42;"));
}

TEST(ProtectEndProtectedSyntax, TheLettersAsAnEscapedIdentifierAreNotTheWord) {
  ReadSource run(RegionClosedWith("`pragma protect \\end_protected\n"));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 1U);
}

TEST(ProtectEndProtectedSyntax,
     TheLettersAsAnEscapedIdentifierEndNoSealedModel) {
  EncryptionRun run(
      RegionAroundSealedModel("`pragma protect \\end_protected\n"));
  EXPECT_EQ(run.diag.ErrorCount(), 0U);
}

TEST(ProtectEndProtectedSyntax, TheWordInAnotherCaseIsNotTheWord) {
  ReadSource run(RegionClosedWith("`pragma protect END_PROTECTED\n"));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 1U);
}

TEST(ProtectEndProtectedSyntax, TheWordInAnotherCaseEndsNoSealedModel) {
  EncryptionRun run(RegionAroundSealedModel("`pragma protect END_PROTECTED\n"));
  EXPECT_EQ(run.diag.ErrorCount(), 0U);
}

TEST(ProtectEndProtectedSyntax,
     AShorterReservedNameSharingItsLettersClosesTheOtherMode) {
  ReadSource run(
      "`pragma protect begin\n"
      "`pragma protect begin_protected\n"
      "`pragma protect end\n");
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 1U);
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 0U);
}

TEST(ProtectEndProtectedSyntax,
     AShorterReservedNameSharingItsLettersEndsNoSealedModel) {
  EncryptionRun run(RegionAroundSealedModel("`pragma protect end\n"));
  EXPECT_EQ(run.diag.ErrorCount(), 0U);
}

TEST(ProtectEndProtectedSyntax, ALongerNameStartingWithTheWordIsNotTheWord) {
  ReadSource run(RegionClosedWith("`pragma protect end_protected_v2\n"));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 1U);
}

TEST(ProtectEndProtectedSyntax,
     ALongerNameStartingWithTheWordEndsNoSealedModel) {
  EncryptionRun run(
      RegionAroundSealedModel("`pragma protect end_protected_v2\n"));
  EXPECT_EQ(run.diag.ErrorCount(), 0U);
}

TEST(ProtectEndProtectedSyntax, TheWordWrittenAsAValueClosesNothing) {
  ReadSource run(RegionClosedWith("`pragma protect comment=end_protected\n"));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 1U);
}

TEST(ProtectEndProtectedSyntax, TheWordWrittenAsAValueEndsNoSealedModel) {
  EncryptionRun run(
      RegionAroundSealedModel("`pragma protect comment=end_protected\n"));
  EXPECT_EQ(run.diag.ErrorCount(), 0U);
}

TEST(ProtectEndProtectedSyntax, TheWordUnderAnotherPragmaNameClosesNothing) {
  ReadSource run(RegionClosedWith("`pragma acme end_protected\n"));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 1U);
}

TEST(ProtectEndProtectedSyntax,
     TheWordUnderAnotherPragmaNameEndsNoSealedModel) {
  EncryptionRun run(RegionAroundSealedModel("`pragma acme end_protected\n"));
  EXPECT_EQ(run.diag.ErrorCount(), 0U);
}

TEST(ProtectEndProtectedSyntax, TheWordAsThePragmaNameClosesNothing) {
  ReadSource run(RegionClosedWith("`pragma end_protected\n"));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 1U);
}

TEST(ProtectEndProtectedSyntax, TheWordAsThePragmaNameEndsNoSealedModel) {
  EncryptionRun run(RegionAroundSealedModel("`pragma end_protected\n"));
  EXPECT_EQ(run.diag.ErrorCount(), 0U);
}

TEST(ProtectEndProtectedSyntax, TheWordInsideAParenthesizedValueClosesNothing) {
  ReadSource run(
      RegionClosedWith("`pragma protect encoding=(end_protected)\n"));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 1U);
}

TEST(ProtectEndProtectedSyntax,
     TheWordInsideAParenthesizedValueEndsNoSealedModel) {
  EncryptionRun run(
      RegionAroundSealedModel("`pragma protect encoding=(end_protected)\n"));
  EXPECT_EQ(run.diag.ErrorCount(), 0U);
}

}  // namespace
