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

std::string WithValuedOpeningWord(const std::string& written) {
  constexpr std::string_view kOpening = "`pragma protect begin_protected\n";
  constexpr std::string_view kValued =
      "`pragma protect begin_protected=\"1\"\n";
  size_t at = written.find(kOpening);
  if (at == std::string::npos) return written;
  std::string valued(written);
  valued.replace(at, kOpening.size(), kValued);
  return valued;
}

constexpr std::string_view kSealedBlockExpression =
    "`pragma protect data_block";

constexpr std::string_view kSealedBlockCharacters = "SEALEDMODELBLOCKMARKER";

std::string RegionAroundSealedModel(std::string_view opening) {
  std::string text = "`pragma protect begin\n";
  text.append("  initial result = 42;\n");
  text.append(opening);
  text.append("`pragma protect author=\"Other Corp\"\n");
  text.append(kSealedBlockExpression).append("\n");
  text.append(kSealedBlockCharacters).append("\n");
  text.append("`pragma protect end_protected\n");
  text.append("`pragma protect end\n");
  return text;
}

TEST(ProtectBeginProtectedSyntax, TheWordAloneOpensAnEnvelopeForDecryption) {
  ReadSource run("`pragma protect begin_protected\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 1U);
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 0U);
  EXPECT_TRUE(run.Protected());
}

TEST(ProtectBeginProtectedSyntax,
     TheDirectiveCarryingTheWordContributesNoText) {
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

TEST(ProtectBeginProtectedSyntax, TheEnvelopeTheWordOpenedIsWhatCloses) {
  ReadSource run(
      "`pragma protect begin_protected\n"
      "`pragma protect end_protected\n");
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
  ASSERT_EQ(run.Closed().size(), 1U);
  EXPECT_EQ(run.Closed().front().mode, EnvelopeMode::kDecryption);
}

TEST(ProtectBeginProtectedSyntax, TheWordLastAfterValuedExpressionsStillOpens) {
  ReadSource run(
      "`pragma protect author=\"Acme Corp\", data_method=\"x-caesar\", "
      "begin_protected\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 1U);
}

TEST(ProtectBeginProtectedSyntax,
     TheWordFirstAheadOfAValuedExpressionStillOpens) {
  ReadSource run("`pragma protect begin_protected, comment=\"sealed\"\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 1U);
}

TEST(ProtectBeginProtectedSyntax, TheWordAloneOnItsOwnDirectiveStillOpens) {
  ReadSource run(
      "`pragma protect author=\"Acme Corp\"\n"
      "`pragma protect begin_protected\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 1U);
}

TEST(ProtectBeginProtectedSyntax, AMacroExpandingToTheWordOpensTheEnvelope) {
  ReadSource run(
      "`define OPEN begin_protected\n"
      "`pragma protect `OPEN\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 1U);
}

TEST(ProtectBeginProtectedSyntax, ACommentAfterTheWordLeavesItStandingAlone) {
  ReadSource run("`pragma protect begin_protected // sealed model starts\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 1U);
}

TEST(ProtectBeginProtectedSyntax, TheWordOpensAnEnvelopeInsideOneAlreadyOpen) {
  ReadSource run(
      "`pragma protect begin_protected\n"
      "`pragma protect begin_protected\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 2U);
}

TEST(ProtectBeginProtectedSyntax, ARegionTheWordOpensComesBackUnderTheKey) {
  ReadSource run(EncryptedByTheAuthor(Design()), kReadingExchangeKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, "initial result = 42;"));
  EXPECT_FALSE(Holds(run.text, "data_block"));
}

TEST(ProtectBeginProtectedSyntax,
     ARegionUnderADeclaredEncodingComesBackThroughTheWord) {
  std::string written = EncryptedByTheAuthor(DesignUnderDeclaredEncoding());
  ASSERT_TRUE(Holds(written, "enctype=\"base64\""));
  ReadSource run(written, kReadingExchangeKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, "initial result = 42;"));
}

TEST(ProtectBeginProtectedSyntax, TheWordAloneMarksASealedModelForEncrypting) {
  EncryptionRun run(
      RegionAroundSealedModel("`pragma protect begin_protected\n"));
  EXPECT_EQ(run.diag.ErrorCount(), 0U);
}

TEST(ProtectBeginProtectedSyntax, TheSealedModelTheWordMarkedIsEncryptedWhole) {
  std::string written = EncryptedByTheAuthor(
      RegionAroundSealedModel("`pragma protect begin_protected\n"));
  EXPECT_TRUE(Holds(written, "`pragma protect data_block\n"));
  EXPECT_FALSE(Holds(written, kSealedBlockCharacters));
  EXPECT_FALSE(Holds(written, "initial result = 42;"));
}

TEST(ProtectBeginProtectedSyntax,
     TheSealedModelsDescriptionDoesNotReachTheEnvelopeBeingWritten) {
  std::string written = EncryptedByTheAuthor(
      RegionAroundSealedModel("`pragma protect begin_protected\n"));
  EXPECT_FALSE(Holds(written, "author=\"Other Corp\""));
}

TEST(ProtectBeginProtectedSyntax, AStringWrittenAgainstTheWordIsReported) {
  ReadSource run("`pragma protect begin_protected=\"1\"\n");
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma begin_protected keyword is written on its own and takes "
      "no pragma_value",
      1, "34.5.3.1"));
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
  EXPECT_FALSE(run.Protected());
}

TEST(ProtectBeginProtectedSyntax, AParenthesizedValueAgainstTheWordIsReported) {
  ReadSource run("`pragma protect begin_protected=(enctype=\"raw\")\n");
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma begin_protected keyword is written on its own and takes "
      "no pragma_value",
      1, "34.5.3.1"));
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
}

TEST(ProtectBeginProtectedSyntax, TheValuedWordDescribesNoEnvelopeEither) {
  ReadSource run("`pragma protect begin_protected=\"1\"\n");
  EXPECT_TRUE(run.Pending().empty());
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(),
                            "protect pragma begin_protected keyword is written "
                            "on its own and takes no pragma_value",
                            1, "34.5.3.1"));
}

TEST(ProtectBeginProtectedSyntax, AWordWrittenProperlyAfterAReportedOneOpens) {
  ReadSource run(
      "`pragma protect begin_protected=\"1\"\n"
      "`pragma protect begin_protected\n");
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma begin_protected keyword is written on its own and takes "
      "no pragma_value",
      1, "34.5.3.1"));
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 1U);
}

TEST(ProtectBeginProtectedSyntax, AValuedOpeningWordLeavesTheDesignSealed) {
  std::string written = WithValuedOpeningWord(EncryptedByTheAuthor(Design()));
  ReadSource run(written, kReadingExchangeKey);
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma begin_protected keyword is written on its own and takes "
      "no pragma_value",
      LineHolding(written, "begin_protected="), "34.5.3.1"));
  EXPECT_FALSE(Holds(run.text, "initial result = 42;"));
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
}

TEST(ProtectBeginProtectedSyntax,
     TheValuedWordMarksNoSealedModelWhenEncrypting) {
  std::string src =
      RegionAroundSealedModel("`pragma protect begin_protected=\"1\"\n");
  EncryptionRun run(src);
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(), "data_block is written where no previously",
      LineHolding(src, kSealedBlockExpression), "34.5.15"));
}

TEST(ProtectBeginProtectedSyntax,
     AParenthesizedValueMarksNoSealedModelWhenEncrypting) {
  std::string src = RegionAroundSealedModel(
      "`pragma protect begin_protected=(enctype=\"raw\")\n");
  EncryptionRun run(src);
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(), "data_block is written where no previously",
      LineHolding(src, kSealedBlockExpression), "34.5.15"));
}

TEST(ProtectBeginProtectedSyntax,
     TheValuedWordLetsTheOtherModelsAuthorOntoThisEnvelope) {
  std::string written = EncryptedByTheAuthor(
      RegionAroundSealedModel("`pragma protect begin_protected=\"1\"\n"));
  EXPECT_TRUE(Holds(written, "author=\"Other Corp\""));
}

TEST(ProtectBeginProtectedSyntax,
     TheLettersAsAnEscapedIdentifierAreNotTheWord) {
  ReadSource run("`pragma protect \\begin_protected\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
}

TEST(ProtectBeginProtectedSyntax,
     TheLettersAsAnEscapedIdentifierMarkNoSealedModel) {
  std::string src =
      RegionAroundSealedModel("`pragma protect \\begin_protected\n");
  EncryptionRun run(src);
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(), "data_block is written where no previously",
      LineHolding(src, kSealedBlockExpression), "34.5.15"));
}

TEST(ProtectBeginProtectedSyntax, TheWordInAnotherCaseIsNotTheWord) {
  ReadSource run("`pragma protect BEGIN_PROTECTED\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
}

TEST(ProtectBeginProtectedSyntax, TheWordInAnotherCaseMarksNoSealedModel) {
  std::string src =
      RegionAroundSealedModel("`pragma protect BEGIN_PROTECTED\n");
  EncryptionRun run(src);
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(), "data_block is written where no previously",
      LineHolding(src, kSealedBlockExpression), "34.5.15"));
}

TEST(ProtectBeginProtectedSyntax,
     AShorterReservedNameSharingItsLettersOpensTheOtherMode) {
  ReadSource run("`pragma protect begin\n");
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 1U);
}

TEST(ProtectBeginProtectedSyntax,
     AShorterReservedNameSharingItsLettersMarksNoSealedModel) {
  std::string src = RegionAroundSealedModel("`pragma protect begin\n");
  EncryptionRun run(src);
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(), "data_block is written where no previously",
      LineHolding(src, kSealedBlockExpression), "34.5.15"));
}

TEST(ProtectBeginProtectedSyntax, ALongerNameStartingWithTheWordIsNotTheWord) {
  ReadSource run("`pragma protect begin_protected_v2\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
}

TEST(ProtectBeginProtectedSyntax,
     ALongerNameStartingWithTheWordMarksNoSealedModel) {
  std::string src =
      RegionAroundSealedModel("`pragma protect begin_protected_v2\n");
  EncryptionRun run(src);
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(), "data_block is written where no previously",
      LineHolding(src, kSealedBlockExpression), "34.5.15"));
}

TEST(ProtectBeginProtectedSyntax, TheWordWrittenAsAValueOpensNothing) {
  ReadSource run("`pragma protect comment=begin_protected\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
}

TEST(ProtectBeginProtectedSyntax, TheWordWrittenAsAValueMarksNoSealedModel) {
  std::string src =
      RegionAroundSealedModel("`pragma protect comment=begin_protected\n");
  EncryptionRun run(src);
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(), "data_block is written where no previously",
      LineHolding(src, kSealedBlockExpression), "34.5.15"));
}

TEST(ProtectBeginProtectedSyntax, TheWordUnderAnotherPragmaNameOpensNothing) {
  ReadSource run("`pragma acme begin_protected\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
}

TEST(ProtectBeginProtectedSyntax,
     TheWordUnderAnotherPragmaNameMarksNoSealedModel) {
  std::string src = RegionAroundSealedModel("`pragma acme begin_protected\n");
  EncryptionRun run(src);
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(), "data_block is written where no previously",
      LineHolding(src, kSealedBlockExpression), "34.5.15"));
}

TEST(ProtectBeginProtectedSyntax, TheWordAsThePragmaNameOpensNothing) {
  ReadSource run("`pragma begin_protected\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
}

TEST(ProtectBeginProtectedSyntax, TheWordAsThePragmaNameMarksNoSealedModel) {
  std::string src = RegionAroundSealedModel("`pragma begin_protected\n");
  EncryptionRun run(src);
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(), "data_block is written where no previously",
      LineHolding(src, kSealedBlockExpression), "34.5.15"));
}

TEST(ProtectBeginProtectedSyntax,
     TheWordInsideAParenthesizedValueOpensNothing) {
  ReadSource run("`pragma protect encoding=(begin_protected)\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
}

TEST(ProtectBeginProtectedSyntax,
     TheWordInsideAParenthesizedValueMarksNoSealedModel) {
  std::string src =
      RegionAroundSealedModel("`pragma protect encoding=(begin_protected)\n");
  EncryptionRun run(src);
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(), "data_block is written where no previously",
      LineHolding(src, kSealedBlockExpression), "34.5.15"));
}

}  // namespace
