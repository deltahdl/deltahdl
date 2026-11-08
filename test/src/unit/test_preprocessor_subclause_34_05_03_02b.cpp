#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "fixture_protect_read.h"
#include "helpers_protect_sealed_model.h"
#include "helpers_reported_error.h"
#include "helpers_text_lines.h"

using namespace delta;

namespace {

constexpr std::string_view kCarriedBlockAnnouncement =
    "`pragma protect data_block\n";

std::string RegionUnderKey(std::string_view owner, std::string_view name,
                           std::string_view statement) {
  std::string text = "`pragma protect begin\n";
  text.append("`pragma protect data_keyowner=\"").append(owner).append("\"\n");
  text.append("`pragma protect data_keyname=\"").append(name).append("\"\n");
  text.append("  ").append(statement).append("\n");
  text.append("`pragma protect end\n");
  return text;
}

std::string RegionAroundAnUnclosedSealedModel() {
  std::string text = "`pragma protect begin\n";
  text.append("  ").append(kOuterStatement).append("\n");
  text.append("`pragma protect begin_protected\n");
  text.append(kCarriedBlockAnnouncement).append(kSealedBlockMarker);
  text.push_back('\n');
  text.append("`pragma protect end\n");
  return text;
}

std::string DesignUnderDeclaredEncoding() {
  std::string text = "`pragma protect begin\n";
  text.append("`pragma protect encoding=(enctype=\"base64\")\n");
  text.append("  ").append(kOuterStatement).append("\n");
  text.append("`pragma protect end\n");
  return text;
}

std::string OpeningDirective() { return "`pragma protect begin_protected\n"; }

std::string KeyNameDirective(std::string_view name) {
  std::string text = "`pragma protect data_keyname=\"";
  text.append(name).append("\"\n");
  return text;
}

TEST(ProtectBeginProtectedDescription,
     TheSealedModelsOpeningExpressionGoesIntoTheCurrentBlock) {
  std::string written = EncryptedUnderNames(NamedRegionAround(SealedModel()));
  EXPECT_EQ(TimesWritten(written, "begin_protected"), 1U);
  EXPECT_EQ(TimesWritten(written, "end_protected"), 1U);
}

TEST(ProtectBeginProtectedDescription,
     TheBlockIsWrittenUnderTheMethodTheEnvelopeStates) {
  std::string written = EncryptedUnderNames(NamedRegionAround(SealedModel()));
  EXPECT_TRUE(Holds(written, kCurrentMethod));
  EXPECT_FALSE(Holds(written, kSealerMethod));
}

TEST(ProtectBeginProtectedDescription,
     TheSealedModelsDelimitersComeBackOutOfTheBlock) {
  ReadSource run(EncryptedByTheAuthor(UnnamedRegionAround(
                     EncryptedByTheAuthor(Design(kInnerStatement)))),
                 ReadSource::KeyConfig(kReadingExchangeKey));
  EXPECT_EQ(run.Closed().size(), 2U);
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
}

TEST(ProtectBeginProtectedDescription,
     ARegionWithNoKeyLeavesTheSealedModelAsItStands) {
  KeylessEncryptionRun run(UnnamedRegionAround(SealedModel()));
  EXPECT_FALSE(Holds(run.text, kCurrentMethod));
  EXPECT_TRUE(Holds(run.text, kSealedBlockMarker));
  EXPECT_TRUE(Holds(run.text, kOuterStatement));
  EXPECT_TRUE(
      ReportedError(run.diag.Diagnostics(),
                    "protect pragma encryption envelope has no key to be "
                    "encrypted under, so it is written out unencrypted",
                    1, "34.3.1"));
}

TEST(ProtectBeginProtectedDescription,
     ASealedModelWithNoClosingExpressionLeavesNothingToEncrypt) {
  EncryptionRun run(RegionAroundAnUnclosedSealedModel());
  EXPECT_EQ(run.diag.ErrorCount(), 0U);
  EXPECT_FALSE(Holds(run.text, kCurrentMethod));
  EXPECT_TRUE(Holds(run.text, kOuterStatement));
  EXPECT_TRUE(Holds(run.text, kSealedBlockMarker));
}

TEST(ProtectBeginProtectedDescription,
     TheExpressionIsWhatBeginsTheRegionTheBlockBelongsTo) {
  ReadSource run(EncryptedByTheAuthor(Design(kOuterStatement)),
                 ReadSource::KeyConfig(kReadingExchangeKey));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, kOuterStatement));
}

TEST(ProtectBeginProtectedDescription,
     ABlockWithNoExpressionBeginningItsRegionIsNotOpened) {
  ReadSource run(Without(EncryptedByTheAuthor(Design(kOuterStatement)),
                         OpeningDirective()),
                 ReadSource::KeyConfig(kReadingExchangeKey));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(Holds(run.text, kOuterStatement));
}

TEST(ProtectBeginProtectedDescription,
     TheLineBelowAnAnnouncedKeyOutsideEveryRegionIsSourceText) {
  std::string src = "`pragma protect data_decrypt_key\n";
  src.append("  ").append(kOuterStatement).append("\n");
  ReadSource run(src, ReadSource::KeyConfig(kReadingExchangeKey));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, kOuterStatement));
}

TEST(ProtectBeginProtectedDescription,
     TheLineBelowAnAnnouncedKeyInsideTheRegionIsKeyMaterial) {
  std::string src = "`pragma protect begin_protected\n";
  src.append("`pragma protect data_decrypt_key\n");
  src.append("  ").append(kOuterStatement).append("\n");
  src.append("`pragma protect end_protected\n");
  ReadSource run(src, ReadSource::KeyConfig(kReadingExchangeKey));
  EXPECT_FALSE(Holds(run.text, kOuterStatement));
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma value is not written in the encoding in effect", 3,
      "34.5.9.2"));
}

TEST(ProtectBeginProtectedDescription,
     TheExpressionsInTheBlockSelectTheKeyThatOpensIt) {
  ReadSource run(
      EncryptedUnderNames(NamedRegionAround(SealedModelNamingItsOwnKeys())),
      ReadSource::KeysConfig(BothEntitiesKeys()));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, kOuterStatement));
}

TEST(ProtectBeginProtectedDescription,
     ABlockMissingTheExpressionThatNamesItsKeyDoesNotOpen) {
  std::string written =
      Without(EncryptedUnderNames(NamedRegionAround(SealedModel())),
              KeyNameDirective(kAuthorKeyName));
  ReadSource run(written, ReadSource::KeysConfig(BothEntitiesKeys()));
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma data block cannot be decrypted with the key supplied",
      LineHolding(written, kCarriedBlockAnnouncement) + 1, "34.3.2"));
  EXPECT_FALSE(Holds(run.text, kOuterStatement));
}

TEST(ProtectBeginProtectedDescription,
     EachBlockIsOpenedWithTheExpressionsItsOwnRegionCarries) {
  std::string src =
      RegionUnderKey(kAuthorEntity, kAuthorKeyName, "initial first = 1;");
  src.append(
      RegionUnderKey(kSealerEntity, kSealerKeyName, "initial second = 2;"));
  ReadSource run(EncryptedUnderNames(src),
                 ReadSource::KeysConfig(BothEntitiesKeys()));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, "initial first = 1;"));
  EXPECT_TRUE(Holds(run.text, "initial second = 2;"));
}

TEST(ProtectBeginProtectedDescription,
     ARegionDesignatingItsKeyByPublicKeyIsOpenedThroughThatDesignation) {
  std::string src = RegionDesignatingItsKeyByPublicKey(PublicKeyDesignation());
  ReadSource run(EncryptedUnderThePublicKey(src),
                 ReadSource::KeysConfig(KeysUnderThePublicKey()));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, kOuterStatement));
}

TEST(ProtectBeginProtectedDescription,
     TheCodingSchemeStatedInTheRegionIsWhatItsBlockIsReadUnder) {
  std::string written = EncryptedByTheAuthor(DesignUnderDeclaredEncoding());
  ASSERT_TRUE(Holds(written, "enctype=\"base64\""));
  ReadSource run(written, ReadSource::KeyConfig(kReadingExchangeKey));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, kOuterStatement));
}

}  // namespace
