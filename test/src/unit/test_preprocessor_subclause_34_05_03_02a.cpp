#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "fixture_protect_read.h"
#include "helpers_protect_sealed_model.h"
#include "helpers_reported_error.h"
#include "helpers_text_lines.h"

using namespace delta;

namespace {

constexpr std::string_view kNestedBlockMarker = "NESTEDMODELBLOCKMARKER";

constexpr std::string_view kModelBlockAnnouncement =
    "`pragma protect data_block\n";

std::string SealedModelHoldingAnother() {
  std::string text = "`pragma protect begin_protected\n";
  text.append("`pragma protect data_keyowner=\"").append(kSealerEntity);
  text.append("\"\n");
  text.append("`pragma protect begin_protected\n");
  text.append(kModelBlockAnnouncement).append(kNestedBlockMarker);
  text.push_back('\n');
  text.append("`pragma protect end_protected\n");
  text.append("`pragma protect data_keyname=\"").append(kSealerKeyName);
  text.append("\"\n");
  text.append(kModelBlockAnnouncement).append(kSealedBlockMarker);
  text.push_back('\n');
  text.append("`pragma protect end_protected\n");
  return text;
}

std::string SealedModelDeclaringAScheme() {
  std::string text = "`pragma protect begin_protected\n";
  text.append("`pragma protect encoding=(enctype=\"base64\")\n");
  text.append(kModelBlockAnnouncement).append(kSealedBlockMarker);
  text.push_back('\n');
  text.append("`pragma protect end_protected\n");
  return text;
}

std::string SealedModelHoldingAPublicKeyDesignation() {
  std::string text = "`pragma protect begin_protected\n";
  text.append(PublicKeyDesignation());
  text.append("`pragma protect end_protected\n");
  return text;
}

std::string NamedRegionNamingItsKeyAfter(std::string_view sealed) {
  std::string text = "`pragma protect begin\n";
  text.append("`pragma protect data_keyowner=\"").append(kAuthorEntity);
  text.append("\"\n");
  text.append("  ").append(kOuterStatement).append("\n");
  text.append(sealed);
  text.append("`pragma protect data_keyname=\"").append(kAuthorKeyName);
  text.append("\"\n");
  text.append("`pragma protect end\n");
  return text;
}

std::string RegionAnnouncingAKeyAheadOfASealedModel() {
  std::string text = "`pragma protect begin\n";
  text.append("`pragma protect data_keyowner=\"").append(kAuthorEntity);
  text.append("\"\n");
  text.append("`pragma protect encoding=(enctype=\"raw\")\n");
  text.append("`pragma protect data_public_key\n");
  text.append(SealedModel());
  text.append(kAuthorPublicKey).append("\n");
  text.append("  ").append(kOuterStatement).append("\n");
  text.append("`pragma protect end\n");
  return text;
}

std::string RegionAfterAStrayClosingExpression() {
  std::string text = "`pragma protect begin\n";
  text.append("`pragma protect end_protected\n");
  text.append("`pragma protect author=\"").append(kAuthorEntity).append("\"\n");
  text.append("  ").append(kOuterStatement).append("\n");
  text.append(SealedModel());
  text.append("`pragma protect end\n");
  return text;
}

TEST(ProtectBeginProtectedDescription,
     ASealedModelIsResealedAsPartOfTheLargerModel) {
  ReadSource run(EncryptedByTheAuthor(UnnamedRegionAround(
                     EncryptedByTheAuthor(Design(kInnerStatement)))),
                 ReadSource::KeyConfig(kReadingExchangeKey));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, kOuterStatement));
  EXPECT_TRUE(Holds(run.text, kInnerStatement));
}

TEST(ProtectBeginProtectedDescription,
     TheSealedModelsOwnDescriptionIsNotReadableInTheOutput) {
  std::string written = EncryptedUnderNames(NamedRegionAround(SealedModel()));
  EXPECT_FALSE(Holds(written, kSealedBlockMarker));
  EXPECT_FALSE(Holds(written, kSealerMethod));
  EXPECT_FALSE(Holds(written, kSealerEntity));
  EXPECT_FALSE(Holds(written, kOuterStatement));
}

TEST(ProtectBeginProtectedDescription,
     ASealedModelOutsideEveryRegionIsCarriedAcrossRatherThanRead) {
  std::string src = SealedModelNamingItsOwnKeys() + NamedRegionAround("");
  std::string written = EncryptedUnderNames(src);
  EXPECT_EQ(TimesWritten(written, "begin_protected"), 2U);
  EXPECT_EQ(TimesWritten(written, "data_keyname=\"design-2026\""), 1U);
  EXPECT_EQ(TimesWritten(written, "data_keyname=\"other-2019\""), 1U);
}

TEST(ProtectBeginProtectedDescription,
     ASealedModelOutsideEveryRegionSelectsNoKeyForTheRegionAfterIt) {
  std::string src = SealedModelNamingItsOwnKeys() + NamedRegionAround("");
  std::string written = EncryptedUnderNames(src);
  ReadSource run(written, ReadSource::KeyConfig(kSealerKey));
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma data block cannot be decrypted with the key supplied",
      LineHolding(written, kModelBlockAnnouncement) + 1, "34.3.2"));
  EXPECT_FALSE(Holds(run.text, kOuterStatement));
}

TEST(ProtectBeginProtectedDescription,
     TheSealedModelsAuthorDoesNotDisplaceTheCurrentOne) {
  std::string written = EncryptedUnderNames(NamedRegionAround(SealedModel()));
  EXPECT_TRUE(Holds(written, "author=\"Acme Corp\""));
  EXPECT_FALSE(Holds(written, "author=\"Other Corp\""));
}

TEST(ProtectBeginProtectedDescription,
     TheSealedModelsKeyNameDoesNotDisplaceTheCurrentOne) {
  std::string written = EncryptedUnderNames(NamedRegionAround(SealedModel()));
  EXPECT_TRUE(Holds(written, "data_keyname=\"design-2026\""));
  EXPECT_FALSE(Holds(written, kSealerKeyName));
}

TEST(ProtectBeginProtectedDescription,
     TheLargerModelIsEncryptedUnderTheKeyItsOwnNamesSelect) {
  ReadSource run(
      EncryptedUnderNames(NamedRegionAround(SealedModelNamingItsOwnKeys())),
      ReadSource::KeyConfig(kAuthorKey));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, kOuterStatement));
}

TEST(ProtectBeginProtectedDescription,
     TheSealedModelsNamesSelectNoKeyForTheLargerModel) {
  std::string written =
      EncryptedUnderNames(NamedRegionAround(SealedModelNamingItsOwnKeys()));
  ReadSource run(written, ReadSource::KeyConfig(kSealerKey));
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma data block cannot be decrypted with the key supplied",
      LineHolding(written, kModelBlockAnnouncement) + 1, "34.3.2"));
  EXPECT_FALSE(Holds(run.text, kOuterStatement));
}

TEST(ProtectBeginProtectedDescription,
     AModelRecoveredOutOfABlockIsReportedWhenNoKeyOpensIt) {
  std::string region = NamedRegionAround(SealedModel());
  ReadSource run(EncryptedUnderNames(region),
                 ReadSource::KeyConfig(kAuthorKey));
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "states an encryption algorithm this implementation does not provide",
      LineHolding(region, kSealedBlockMarker) - 2, "34.5.11.2"));
  EXPECT_TRUE(Holds(run.text, kOuterStatement));
}

TEST(ProtectBeginProtectedDescription,
     TheBlockInsideTheSealedModelIsNotTakenForOneOfThisEnvelopes) {
  EncryptionRun run(UnnamedRegionAround(SealedModel()));
  EXPECT_EQ(run.diag.ErrorCount(), 0U);
}

TEST(ProtectBeginProtectedDescription,
     AnAnnouncedKeyInsideTheSealedModelDesignatesNoKeyForTheRegion) {
  std::string src = RegionDesignatingItsKeyByPublicKey(
      SealedModelHoldingAPublicKeyDesignation());
  std::string written = EncryptedUnderThePublicKey(src);
  EXPECT_TRUE(Holds(written, kOuterStatement));
  EXPECT_FALSE(Holds(written, kCurrentMethod));
}

TEST(ProtectBeginProtectedDescription,
     TheSameAnnouncedKeyOutsideTheSealedModelDoesDesignateOne) {
  std::string src = RegionDesignatingItsKeyByPublicKey(PublicKeyDesignation());
  std::string written = EncryptedUnderThePublicKey(src);
  EXPECT_FALSE(Holds(written, kOuterStatement));
  EXPECT_TRUE(Holds(written, kCurrentMethod));
}

TEST(ProtectBeginProtectedDescription,
     TheReadingResumesWithItsOwnValuesWhereTheSealedModelEnds) {
  std::string written =
      EncryptedUnderNames(NamedRegionNamingItsKeyAfter(SealedModel()));
  EXPECT_TRUE(Holds(written, "data_keyname=\"design-2026\""));
  EXPECT_FALSE(Holds(written, kSealedBlockMarker));
}

TEST(ProtectBeginProtectedDescription,
     AFurtherSealedModelInsideOneDoesNotEndTheOuterBlockEarly) {
  std::string written =
      EncryptedUnderNames(NamedRegionAround(SealedModelHoldingAnother()));
  EXPECT_TRUE(Holds(written, "data_keyname=\"design-2026\""));
  EXPECT_FALSE(Holds(written, kSealerKeyName));
}

TEST(ProtectBeginProtectedDescription,
     NeitherBlockOfTheNestedSealedModelsIsReported) {
  EncryptionRun run(UnnamedRegionAround(SealedModelHoldingAnother()));
  EXPECT_EQ(run.diag.ErrorCount(), 0U);
  EXPECT_FALSE(Holds(run.text, kNestedBlockMarker));
}

TEST(ProtectBeginProtectedDescription,
     AnAnnouncementAheadOfASealedModelIsAnsweredByIt) {
  std::string written =
      EncryptedUnderThePublicKey(RegionAnnouncingAKeyAheadOfASealedModel());
  EXPECT_TRUE(Holds(written, kOuterStatement));
  EXPECT_FALSE(Holds(written, kCurrentMethod));
}

TEST(ProtectBeginProtectedDescription,
     TheSchemeStatedInsideTheSealedModelDoesNotDisplaceTheCurrentOne) {
  std::string written =
      EncryptedByTheAuthor(UnnamedRegionAround(SealedModelDeclaringAScheme()));
  EXPECT_TRUE(Holds(written, "enctype=\"x-deltahdl-block\""));
  EXPECT_FALSE(Holds(written, "base64"));
}

TEST(ProtectBeginProtectedDescription,
     AClosingExpressionWithNoModelOpenIsALineOfTheRegion) {
  std::string written =
      EncryptedByTheAuthor(RegionAfterAStrayClosingExpression());
  EXPECT_TRUE(Holds(written, "author=\"Acme Corp\""));
  EXPECT_FALSE(Holds(written, "author=\"Other Corp\""));
  EXPECT_FALSE(Holds(written, kSealedBlockMarker));
}

}  // namespace
