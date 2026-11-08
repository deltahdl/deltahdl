#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "fixture_protect_read.h"
#include "helpers_protect_keys.h"
#include "helpers_reported_error.h"
#include "helpers_text_lines.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

constexpr std::string_view kOtherReaderKey = "other-reader-key";

constexpr std::string_view kAuthorEntity = "Acme Corp";
constexpr std::string_view kAuthorKeyName = "design-2026";
constexpr std::string_view kAuthorKey = "acme-design-key";

constexpr std::string_view kSealerEntity = "Other Corp";
constexpr std::string_view kSealerKeyName = "other-2019";
constexpr std::string_view kSealerKey = "other-legacy-key";

constexpr std::string_view kOuterStatement = "initial result = 42;";

constexpr std::string_view kInnerStatement = "initial sealed = 7;";
constexpr std::string_view kAfterStatement = "initial after = 9;";

constexpr std::string_view kSealedBlockMarker = "SEALEDMODELBLOCKMARKER";

constexpr std::string_view kCurrentMethod = "x-deltahdl-stream";

constexpr std::string_view kSealerMethod = "x-legacy-cipher";

constexpr std::string_view kWordDirective = "`pragma protect end_protected\n";

constexpr std::string_view kValuedWordDirective =
    "`pragma protect end_protected=\"1\"\n";

constexpr std::string_view kAnnouncesTheBlock = "`pragma protect data_block\n";

ProtectKeyList BothEntitiesKeys() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kAuthorEntity, kAuthorKeyName, kAuthorKey));
  keys.Add(KeyOf(kSealerEntity, kSealerKeyName, kSealerKey));
  return keys;
}

std::string EncryptedUnderNames(const std::string& src) {
  return EncryptEnvelopes(src, {}, BothEntitiesKeys());
}

std::string SealedModel(std::string_view closing) {
  std::string text = "`pragma protect begin_protected\n";
  text.append("`pragma protect author=\"").append(kSealerEntity).append("\"\n");
  text.append("`pragma protect data_keyowner=\"").append(kSealerEntity);
  text.append("\"\n");
  text.append("`pragma protect data_keyname=\"").append(kSealerKeyName);
  text.append("\"\n");
  text.append(closing);
  return text;
}

std::string CurrentKeyNames() {
  std::string text = "`pragma protect data_keyowner=\"";
  text.append(kAuthorEntity).append("\"\n");
  text.append("`pragma protect data_keyname=\"").append(kAuthorKeyName);
  text.append("\"\n");
  return text;
}

std::string RegionNamingItsKeyPastTheWord(std::string_view closing) {
  std::string text = "`pragma protect begin\n";
  text.append("  ").append(kOuterStatement).append("\n");
  text.append(SealedModel(closing));
  text.append(CurrentKeyNames());
  text.append("`pragma protect end\n");
  return text;
}

std::string NextRegionNamingItsKeyPastTheWord(std::string_view closing) {
  std::string text = SealedModel(closing);
  text.append(CurrentKeyNames());
  text.append("`pragma protect begin\n");
  text.append("  ").append(kOuterStatement).append("\n");
  text.append("`pragma protect end\n");
  return text;
}

std::string RegionAroundNestedSealedModels() {
  std::string text = "`pragma protect begin\n";
  text.append("  ").append(kOuterStatement).append("\n");
  text.append("`pragma protect begin_protected\n");
  text.append("`pragma protect begin_protected\n");
  text.append("`pragma protect end_protected\n");
  text.append("`pragma protect data_keyname=\"").append(kSealerKeyName);
  text.append("\"\n");
  text.append("`pragma protect end_protected\n");
  text.append(CurrentKeyNames());
  text.append("`pragma protect end\n");
  return text;
}

std::string Design(std::string_view statement) {
  std::string text = "`pragma protect begin\n";
  text.append("  ").append(statement).append("\n");
  text.append("`pragma protect end\n");
  return text;
}

std::string RegionAroundAProducedModel(const std::string& sealed) {
  std::string text = "`pragma protect begin\n";
  text.append(sealed);
  text.append("  ").append(kAfterStatement).append("\n");
  text.append("`pragma protect end\n");
  return text;
}

std::string RegionOpeningWithAStrayWord() {
  std::string text = "`pragma protect begin\n";
  text.append(kWordDirective);
  text.append("`pragma protect author=\"").append(kAuthorEntity).append("\"\n");
  text.append("  ").append(kOuterStatement).append("\n");
  text.append("`pragma protect begin_protected\n");
  text.append("`pragma protect author=\"").append(kSealerEntity).append("\"\n");
  text.append("`pragma protect data_block\n").append(kSealedBlockMarker);
  text.push_back('\n');
  text.append(kWordDirective);
  text.append("`pragma protect end\n");
  return text;
}

std::string RegionNamingItsAuthorPastTheWord(std::string_view closing) {
  std::string text = "`pragma protect begin\n";
  text.append("  ").append(kOuterStatement).append("\n");
  text.append("`pragma protect begin_protected\n");
  text.append("`pragma protect author=\"").append(kSealerEntity).append("\"\n");
  text.append(closing);
  text.append("`pragma protect author=\"").append(kAuthorEntity).append("\"\n");
  text.append(kWordDirective);
  text.append("`pragma protect end\n");
  return text;
}

std::string RegionStatingASchemePastTheWord(std::string_view closing) {
  std::string text = "`pragma protect begin\n";
  text.append("  ").append(kOuterStatement).append("\n");
  text.append("`pragma protect begin_protected\n");
  text.append(closing);
  text.append("`pragma protect encoding=(enctype=\"base64\")\n");
  text.append(kWordDirective);
  text.append("`pragma protect end\n");
  return text;
}

std::string RegionAroundAModelNamingItsMethod(std::string_view closing) {
  std::string text = "`pragma protect begin\n";
  text.append("  ").append(kOuterStatement).append("\n");
  text.append("`pragma protect begin_protected\n");
  text.append("`pragma protect data_method=\"").append(kSealerMethod);
  text.append("\"\n");
  text.append(closing);
  text.append("`pragma protect end\n");
  return text;
}

std::string RegionUnderTheAuthorsKey() {
  std::string text = "`pragma protect begin\n";
  text.append(CurrentKeyNames());
  text.append("  ").append(kOuterStatement).append("\n");
  text.append("`pragma protect end\n");
  return text;
}

std::string EnvelopeAnnouncingNothing(std::string_view keyword) {
  std::string text = "`pragma protect begin_protected\n";
  text.append("`pragma protect ").append(keyword).append("\n");
  text.append("`pragma protect end_protected\n");
  return text;
}

std::string EnvelopeCarryingAnUnspentKey(std::string_view key) {
  std::string text = "`pragma protect begin_protected\n";
  text.append("`pragma protect encoding=(enctype=\"raw\")\n");
  text.append("`pragma protect data_decrypt_key\n");
  text.append(key).append("\n");
  text.append("`pragma protect end_protected\n");
  return text;
}

std::string KeyNameDirective(std::string_view name) {
  std::string text = "`pragma protect data_keyname=\"";
  text.append(name).append("\"\n");
  return text;
}

std::string WithLineMovedPastTheWord(const std::string& written,
                                     const std::string& line) {
  constexpr std::string_view kClosing = "`pragma protect end_protected\n";
  size_t at = written.find(line);
  if (at == std::string::npos) return written;
  std::string moved(written);
  moved.erase(at, line.size());
  size_t closing = moved.find(kClosing);
  if (closing == std::string::npos) return written;
  moved.insert(closing + kClosing.size(), line);
  return moved;
}

std::string WithTheWordAheadOfTheBlock(const std::string& written) {
  constexpr std::string_view kClosing = "`pragma protect end_protected\n";
  size_t at = written.find(kClosing);
  if (at == std::string::npos) return written;
  std::string moved(written);
  moved.erase(at, kClosing.size());
  size_t block = moved.find(kAnnouncesTheBlock);
  if (block == std::string::npos) return written;
  moved.insert(block, kClosing);
  return moved;
}

uint32_t TheBlocksLineIn(const std::string& written) {
  uint32_t announced = LineHolding(written, kAnnouncesTheBlock);
  return announced == 0 ? 0 : announced + 1;
}

TEST(ProtectEndProtectedDescription, AWordWithNoPreviousBlockEndsNothing) {
  std::string written = EncryptedByTheAuthor(RegionOpeningWithAStrayWord());
  EXPECT_TRUE(Holds(written, "author=\"Acme Corp\""));
  EXPECT_FALSE(Holds(written, "author=\"Other Corp\""));
  EXPECT_FALSE(Holds(written, kSealedBlockMarker));
}

TEST(ProtectEndProtectedDescription, AWordWithNoPreviousRegionClosesNothing) {
  std::string src(kWordDirective);
  src.append(EncryptedByTheAuthor(Design(kOuterStatement)));
  ReadSource run(src, ReadSource::KeyConfig(kReadingExchangeKey));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.Closed().size(), 1U);
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
  EXPECT_TRUE(Holds(run.text, kOuterStatement));
}

TEST(ProtectEndProtectedDescription,
     TheNamesWrittenPastTheWordDescribeTheEnvelope) {
  std::string written =
      EncryptedUnderNames(RegionNamingItsKeyPastTheWord(kWordDirective));
  EXPECT_TRUE(Holds(written, "data_keyname=\"design-2026\""));
  EXPECT_FALSE(Holds(written, kSealerKeyName));
}

TEST(ProtectEndProtectedDescription,
     TheEnvelopeIsUnderTheKeyTheNamesPastTheWordSelect) {
  std::string written =
      EncryptedUnderNames(RegionNamingItsKeyPastTheWord(kWordDirective));
  ASSERT_FALSE(Holds(written, kOuterStatement));
  ReadSource run(written, ReadSource::KeyConfig(kAuthorKey));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, kOuterStatement));
}

TEST(ProtectEndProtectedDescription, TheSealedModelsNamesSelectNoKeyForIt) {
  std::string written =
      EncryptedUnderNames(RegionNamingItsKeyPastTheWord(kWordDirective));
  ReadSource run(written, ReadSource::KeyConfig(kSealerKey));
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma data block cannot be decrypted with the key supplied",
      TheBlocksLineIn(written), "34.3.2"));
  EXPECT_FALSE(Holds(run.text, kOuterStatement));
  EXPECT_EQ(run.Closed().size(), 1U);
}

TEST(ProtectEndProtectedDescription,
     AWordCompletingNoBlockLeavesTheNamesUngathered) {
  std::string written =
      EncryptedUnderNames(RegionNamingItsKeyPastTheWord(kValuedWordDirective));
  EXPECT_FALSE(Holds(written, kCurrentMethod));
  EXPECT_TRUE(Holds(written, kOuterStatement));
}

TEST(ProtectEndProtectedDescription,
     TheNamesPastTheWordAreGatheredForTheNextEnvelope) {
  std::string written =
      EncryptedUnderNames(NextRegionNamingItsKeyPastTheWord(kWordDirective));
  ASSERT_FALSE(Holds(written, kOuterStatement));
  ReadSource run(written, ReadSource::KeyConfig(kAuthorKey));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, kOuterStatement));
}

TEST(ProtectEndProtectedDescription,
     NamesPastAWordCompletingNoBlockReachNoLaterEnvelope) {
  std::string src = NextRegionNamingItsKeyPastTheWord(kValuedWordDirective);
  std::string written = EncryptedUnderNames(src);
  EXPECT_EQ(written, src);
  EXPECT_FALSE(Holds(written, kCurrentMethod));
}

TEST(ProtectEndProtectedDescription,
     TheAuthorNamedPastTheWordIsTheEnvelopesOwn) {
  std::string written =
      EncryptedByTheAuthor(RegionNamingItsAuthorPastTheWord(kWordDirective));
  EXPECT_TRUE(Holds(written, "author=\"Acme Corp\""));
  EXPECT_FALSE(Holds(written, "author=\"Other Corp\""));
}

TEST(ProtectEndProtectedDescription, AnAuthorInsideTheUnendedBlockNamesNobody) {
  std::string written = EncryptedByTheAuthor(
      RegionNamingItsAuthorPastTheWord(kValuedWordDirective));
  EXPECT_TRUE(Holds(written, kCurrentMethod));
  EXPECT_FALSE(Holds(written, "author="));
}

TEST(ProtectEndProtectedDescription,
     ASchemeInsideTheUnendedBlockReachesNothing) {
  std::string written = EncryptedByTheAuthor(
      RegionStatingASchemePastTheWord(kValuedWordDirective));
  EXPECT_TRUE(Holds(written, "enctype=\"x-deltahdl-block\""));
  EXPECT_FALSE(Holds(written, "base64"));
}

TEST(ProtectEndProtectedDescription, TheWordOfTheSealedModelGoesIntoTheBlock) {
  std::string src = RegionNamingItsKeyPastTheWord(kWordDirective);
  ASSERT_EQ(TimesWritten(src, "end_protected"), 1U);
  std::string written = EncryptedUnderNames(src);
  EXPECT_EQ(TimesWritten(written, "end_protected"), 1U);
  EXPECT_TRUE(Holds(written, kCurrentMethod));
}

TEST(ProtectEndProtectedDescription, TheWordComesBackOutOfTheBlockAndEnds) {
  ReadSource run(
      EncryptedUnderNames(RegionNamingItsKeyPastTheWord(kWordDirective)),
      ReadSource::KeyConfig(kAuthorKey));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.Closed().size(), 2U);
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
}

TEST(ProtectEndProtectedDescription, TheWordOfEachNestedModelGoesIntoOneBlock) {
  std::string src = RegionAroundNestedSealedModels();
  ASSERT_EQ(TimesWritten(src, "end_protected"), 2U);
  std::string written = EncryptedUnderNames(src);
  EXPECT_EQ(TimesWritten(written, "end_protected"), 1U);
  EXPECT_TRUE(Holds(written, "data_keyname=\"design-2026\""));
  EXPECT_FALSE(Holds(written, kSealerKeyName));
}

TEST(ProtectEndProtectedDescription, ARegionWithNoKeyLeavesTheWordWhereItIs) {
  KeylessEncryptionRun run(RegionNamingItsKeyPastTheWord(kWordDirective));
  EXPECT_FALSE(Holds(run.text, kCurrentMethod));
  EXPECT_EQ(TimesWritten(run.text, "end_protected"), 1U);
  EXPECT_TRUE(Holds(run.text, kOuterStatement));
  EXPECT_TRUE(
      ReportedError(run.diag.Diagnostics(),
                    "protect pragma encryption envelope has no key to be "
                    "encrypted under, so it is written out unencrypted",
                    1, "34.3.1"));
}

TEST(ProtectEndProtectedDescription,
     TheModelsMethodGoesIntoTheBlockWithTheWord) {
  std::string written =
      EncryptedByTheAuthor(RegionAroundAModelNamingItsMethod(kWordDirective));
  EXPECT_TRUE(Holds(written, kCurrentMethod));
  EXPECT_FALSE(Holds(written, kSealerMethod));
  EXPECT_EQ(TimesWritten(written, "end_protected"), 1U);
}

TEST(ProtectEndProtectedDescription, ARegionWithNoKeyStatesNoMethodForTheWord) {
  KeylessEncryptionRun run(RegionAroundAModelNamingItsMethod(kWordDirective));
  EXPECT_FALSE(Holds(run.text, kCurrentMethod));
  EXPECT_TRUE(Holds(run.text, kSealerMethod));
  EXPECT_TRUE(
      ReportedError(run.diag.Diagnostics(),
                    "protect pragma encryption envelope has no key to be "
                    "encrypted under, so it is written out unencrypted",
                    1, "34.3.1"));
}

TEST(ProtectEndProtectedDescription, AProducedModelsOwnWordGoesIntoTheBlock) {
  std::string sealed = EncryptedByTheAuthor(Design(kInnerStatement));
  ASSERT_EQ(TimesWritten(sealed, "end_protected"), 1U);
  std::string written =
      EncryptedByTheAuthor(RegionAroundAProducedModel(sealed));
  EXPECT_EQ(TimesWritten(written, "end_protected"), 1U);
  EXPECT_FALSE(Holds(written, kAfterStatement));
}

TEST(ProtectEndProtectedDescription, AProducedModelsWordComesBackAndEndsIt) {
  std::string written = EncryptedByTheAuthor(RegionAroundAProducedModel(
      EncryptedByTheAuthor(Design(kInnerStatement))));
  ReadSource run(written, ReadSource::KeyConfig(kReadingExchangeKey));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, kInnerStatement));
  EXPECT_TRUE(Holds(run.text, kAfterStatement));
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
}

TEST(ProtectEndProtectedDescription, TheWordAnswersAKeyLeftAwaitingItsLine) {
  ReadSource run(EnvelopeAnnouncingNothing("data_decrypt_key"),
                 ReadSource::KeyConfig(kReadingExchangeKey));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
  EXPECT_EQ(run.Closed().size(), 1U);
}

TEST(ProtectEndProtectedDescription,
     TheWordAnswersADesignationLeftAwaitingItsLine) {
  ReadSource run(EnvelopeAnnouncingNothing("data_public_key"),
                 ReadSource::KeyConfig(kReadingExchangeKey));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
  EXPECT_EQ(run.Closed().size(), 1U);
}

TEST(ProtectEndProtectedDescription,
     TheWordAnswersAKeyBlockLeftAwaitingItsLine) {
  ReadSource run(EnvelopeAnnouncingNothing("key_block"),
                 ReadSource::KeyConfig(kReadingExchangeKey));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
  EXPECT_EQ(run.Closed().size(), 1U);
}

TEST(ProtectEndProtectedDescription, TheWordEndsTheRunItsOwnDirectiveOpened) {
  std::string src = "`pragma protect begin_protected\n";
  src.append("`pragma protect data_decrypt_key, end_protected\n");
  src.append("  ").append(kOuterStatement).append("\n");
  ReadSource run(src, ReadSource::KeyConfig(kReadingExchangeKey));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
  EXPECT_TRUE(Holds(run.text, kOuterStatement));
}

TEST(ProtectEndProtectedDescription,
     TheSchemeInTheRunIsWhatTheBlockIsReadUnder) {
  std::string written =
      EncryptedByTheAuthor(RegionStatingASchemePastTheWord(kWordDirective));
  ASSERT_TRUE(Holds(written, "enctype=\"base64\""));
  ReadSource run(written, ReadSource::KeyConfig(kReadingExchangeKey));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, kOuterStatement));
}

TEST(ProtectEndProtectedDescription, ABlockLeftPastTheWordBelongsToNoRun) {
  ReadSource run(
      WithTheWordAheadOfTheBlock(EncryptedByTheAuthor(Design(kOuterStatement))),
      ReadSource::KeyConfig(kReadingExchangeKey));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(Holds(run.text, kOuterStatement));
}

TEST(ProtectEndProtectedDescription, AKeyOneRunGatheredDoesNotOpenTheNext) {
  std::string src = EnvelopeCarryingAnUnspentKey(kOtherReaderKey);
  src.append(EncryptedByTheAuthor(RegionUnderTheAuthorsKey()));
  ReadSource run(src, ReadSource::KeyConfig(kReadingExchangeKey));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, kOuterStatement));
}

TEST(ProtectEndProtectedDescription, TheNextBlockIsNotOpenedByTheEarlierKey) {
  std::string src = EnvelopeCarryingAnUnspentKey(kReadingExchangeKey);
  src.append(EncryptedByTheAuthor(RegionUnderTheAuthorsKey()));
  ReadSource run(src, ReadSource::KeyConfig(kOtherReaderKey));
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma data block cannot be decrypted with the key supplied",
      TheBlocksLineIn(src), "34.3.2"));
  EXPECT_FALSE(Holds(run.text, kOuterStatement));
}

TEST(ProtectEndProtectedDescription, AnExpressionPastTheWordIsOutsideTheRun) {
  std::string written =
      WithLineMovedPastTheWord(EncryptedUnderNames(RegionUnderTheAuthorsKey()),
                               KeyNameDirective(kAuthorKeyName));
  ReadSource run(written, ReadSource::KeysConfig(BothEntitiesKeys()));
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma data block cannot be decrypted with the key supplied",
      TheBlocksLineIn(written), "34.3.2"));
  EXPECT_FALSE(Holds(run.text, kOuterStatement));
}

TEST(ProtectEndProtectedDescription, TheSameExpressionInsideTheRunOpensIt) {
  ReadSource run(EncryptedUnderNames(RegionUnderTheAuthorsKey()),
                 ReadSource::KeysConfig(BothEntitiesKeys()));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, kOuterStatement));
}

}  // namespace
