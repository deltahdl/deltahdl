#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_preprocessor.h"
#include "helpers_protect_keyword_value.h"
#include "helpers_protect_region.h"
#include "helpers_reported_error.h"
#include "helpers_text_lines.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_digest.h"
#include "preprocessor/protect_digest_block.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

constexpr std::string_view kProvider = "Meridian Aerospace";
constexpr std::string_view kProvidersKey = "meridian-2031";
constexpr std::string_view kDigestAlgorithm = "sha256";
constexpr std::string_view kKeyCipher = "rsa";

constexpr std::string_view kDigestMethodKeyword = "digest_method";
constexpr std::string_view kKeyMethodKeyword = "key_method";

constexpr std::string_view kSecondProvider = "Vantage Optics";

std::string Restores() { return "`pragma protect reset\n"; }

std::string ResetPragma() { return "`pragma reset protect\n"; }

constexpr std::string_view kResetExpression = "`pragma protect reset";

std::string Writes(std::string_view keyword, std::string_view value) {
  std::string written = "`pragma protect ";
  written.append(keyword).append("=\"").append(value).append("\"\n");
  return written;
}

std::string StatesFour() {
  std::string written = Writes(kDataKeyownerKeyword, kProvider);
  written.append(Writes(kDataKeynameKeyword, kProvidersKey));
  written.append(Writes(kDigestMethodKeyword, kDigestAlgorithm));
  written.append(Writes(kKeyMethodKeyword, kKeyCipher));
  return written;
}

bool AllFourAreBack(const ReadKeywordScope& scope) {
  return scope.ValueOf(kDataKeyownerKeyword).defaulted &&
         scope.ValueOf(kDataKeynameKeyword).defaulted &&
         scope.ValueOf(kDigestMethodKeyword).defaulted &&
         scope.ValueOf(kKeyMethodKeyword).defaulted;
}

TEST(ProtectResetDescription, EveryKeywordTheTextWroteStandsAtItsDefault) {
  EXPECT_TRUE(AllFourAreBack(ReadKeywordScope(StatesFour() + Restores())));
}

TEST(ProtectResetDescription, WithoutItThoseKeywordsAreStillStanding) {
  ReadKeywordScope scope(StatesFour());
  EXPECT_EQ(scope.ValueOf(kDataKeyownerKeyword).value, kProvider);
  EXPECT_EQ(scope.ValueOf(kKeyMethodKeyword).value, kKeyCipher);
}

TEST(ProtectResetDescription, ItRestoresWhatTheResetPragmaDirectiveRestores) {
  EXPECT_EQ(AllFourAreBack(ReadKeywordScope(StatesFour() + Restores())),
            AllFourAreBack(ReadKeywordScope(StatesFour() + ResetPragma())));
}

TEST(ProtectResetDescription, AKeywordWrittenAfterItIsInEffect) {
  ReadKeywordScope scope(StatesFour() + Restores() +
                         Writes(kDataKeyownerKeyword, kSecondProvider));
  EXPECT_EQ(scope.ValueOf(kDataKeyownerKeyword).value, kSecondProvider);
}

TEST(ProtectResetDescription, ADecryptionEnvelopeIsNeitherOpenedNorClosed) {
  ReadWithTheKeys reading(std::string(kBeginProtected) + Restores());
  EXPECT_EQ(reading.StillOpen(), 1U);
  EXPECT_EQ(reading.Closed(), 0U);
}

TEST(ProtectResetDescription, AnEnvelopeThisToolWroteDescribesNothingAfterIt) {
  ReadWithTheKeys reading(Encrypted(RegionWriting("")));
  EXPECT_TRUE(
      reading.reader.ProtectKeywords().ValueOf(kDataMethodKeyword).defaulted);
}

TEST(ProtectResetDescription, ARegionAfterItReachesNoNameWrittenBeforeIt) {
  std::string source = ReachesTheKey();
  source.append(Restores()).append(RegionAround(kSealedDesign));
  EXPECT_FALSE(Holds(Encrypted(source), kBlockOpening));
}

TEST(ProtectResetDescription, WithoutItThoseNamesReachTheRegion) {
  std::string source = ReachesTheKey();
  source.append(RegionAround(kSealedDesign));
  EXPECT_TRUE(Holds(Encrypted(source), kBlockOpening));
}

TEST(ProtectResetDescription, ARegionsOwnNamesGoBackWhenItResetsAfterThem) {
  std::string inside = ReachesTheKey();
  inside.append(Restores()).append(kSealedDesign);
  EXPECT_FALSE(Holds(Encrypted(RegionAround(inside)), kBlockOpening));
}

TEST(ProtectResetDescription, NamesWrittenAfterItInsideARegionReachTheKey) {
  std::string inside = Restores();
  inside.append(ReachesTheKey()).append(kSealedDesign);
  EXPECT_TRUE(Holds(Encrypted(RegionAround(inside)), kBlockOpening));
}

TEST(ProtectResetDescription, TheEnvelopeCarriesOnlyTheResetThatFollowsIt) {
  std::string inside = Restores();
  inside.append(ReachesTheKey()).append(kSealedDesign);
  EXPECT_EQ(TimesWritten(Encrypted(RegionAround(inside)), kResetExpression),
            1U);
}

TEST(ProtectResetDescription, TheRegionsOwnResetIsInTheBlockWithTheRest) {
  std::string inside = Restores();
  inside.append(ReachesTheKey()).append(kSealedDesign);
  EXPECT_TRUE(
      Holds(OpenedBlockOf(Encrypted(RegionAround(inside))), kResetExpression));
}

constexpr std::string_view kAnnouncingKeywords[] = {
    "key_public_key",  "key_block",         "data_decrypt_key",
    "data_public_key", "digest_public_key", "digest_decrypt_key",
    "data_block",
};

constexpr std::string_view kLineBeneath = "wire w;\n";

std::string AnnouncesThen(std::string_view keyword, std::string_view also) {
  std::string text = "`pragma protect begin_protected\n";
  text.append("`pragma protect ").append(keyword).append(also).append("\n");
  text.append(kLineBeneath);
  text.append("`pragma protect end_protected\n");
  return text;
}

constexpr std::string_view kHandedOverKey = "the-session-key-of-this-envelope";
constexpr std::string_view kBlockedDesign = "module handed_over_m; endmodule\n";

std::string HandsOverTheKey() {
  std::string text = "`pragma protect data_decrypt_key\n";
  text.append(EncodeProtectBlock(kHandedOverKey, DefaultProtectEncoding()));
  text.append("\n");
  return text;
}

std::string SealedUnderTheHandedOverKey(std::string_view between) {
  std::string text = "`pragma protect begin_protected\n";
  text.append(HandsOverTheKey()).append(between);
  text.append("`pragma protect data_block\n");
  text.append(EncryptProtectedRegion(kBlockedDesign, kHandedOverKey));
  text.append("\n`pragma protect end_protected\n");
  return text;
}

TEST(ProtectResetDescription, EveryAnnouncementAwaitingItsLineIsDropped) {
  for (std::string_view keyword : kAnnouncingKeywords) {
    PreprocFixture f;
    std::string read = Preprocess(AnnouncesThen(keyword, ", reset"), f);
    EXPECT_TRUE(Holds(read, kLineBeneath)) << keyword << " left: " << read;
  }
}

TEST(ProtectResetDescription, WithoutItEachAnnouncementTakesTheLineBeneathIt) {
  for (std::string_view keyword : kAnnouncingKeywords) {
    PreprocFixture f;
    std::string read = Preprocess(AnnouncesThen(keyword, ""), f);
    EXPECT_FALSE(Holds(read, kLineBeneath)) << keyword << " left: " << read;
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "protect pragma value is not written in the encoding in effect", 3,
        "34.5.9.2"))
        << keyword;
  }
}

TEST(ProtectResetDescription, TheSessionKeyTheTextHandedOverGoesBackToo) {
  PreprocFixture f;
  std::string read =
      Preprocess(SealedUnderTheHandedOverKey("`pragma protect reset\n"), f);
  EXPECT_FALSE(Holds(read, kBlockedDesign)) << read;
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "protect pragma data block cannot be decrypted with the key supplied", 6,
      "34.3.2"));
}

TEST(ProtectResetDescription, WithoutItThatSessionKeyOpensTheBlock) {
  PreprocFixture f;
  std::string read = Preprocess(SealedUnderTheHandedOverKey(""), f);
  EXPECT_TRUE(Holds(read, kBlockedDesign)) << read;
}

constexpr std::string_view kDigestSessionKey = "unseals-the-digest-of-this-one";
constexpr std::string_view kDataBlockKey = "opens-the-data-of-this-one";

constexpr std::string_view kVouchedDesign = "module vouched_m; endmodule\n";

std::string VouchedForUnderTheDigestKey(std::string_view between) {
  ProtectEncoding encoding = DefaultProtectEncoding();
  std::string text = "`pragma protect begin_protected\n";
  text.append("`pragma protect digest_decrypt_key\n");
  text.append(EncodeProtectBlock(kDigestSessionKey, encoding)).append("\n");
  text.append(between);
  text.append("`pragma protect data_block\n");
  text.append(EncryptProtectedRegion(kVouchedDesign, kDataBlockKey));
  text.append("\n");
  ProtectDigestBlockPolicy policy;
  policy.requested = true;
  policy.method = std::string(kDefaultDigestMethod);
  policy.key = std::string(kDigestSessionKey);
  text.append(ProtectDigestBlockDirectives(kVouchedDesign, policy, encoding));
  text.append("`pragma protect end_protected\n");
  return text;
}

struct ReadHoldingTheBlockKey {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp;
  std::string text;

  explicit ReadHoldingTheBlockKey(const std::string& src)
      : pp(mgr, diag, TheBlockKeyOnly()) {
    text = pp.Preprocess(mgr.AddFile("<test>", src));
  }

  static PreprocConfig TheBlockKeyOnly() {
    PreprocConfig config;
    config.protect_key = std::string(kDataBlockKey);
    return config;
  }

  ProtectDigestCheck DigestCheck() const { return pp.LastDigestBlockCheck(); }
};

TEST(ProtectResetDescription, TheDigestSessionKeyGoesBackToo) {
  ReadHoldingTheBlockKey run(
      VouchedForUnderTheDigestKey("`pragma protect reset\n"));
  EXPECT_NE(run.DigestCheck(), ProtectDigestCheck::kMatched);
}

TEST(ProtectResetDescription, WithoutItThatDigestKeyOpensTheDigest) {
  ReadHoldingTheBlockKey run(VouchedForUnderTheDigestKey(""));
  EXPECT_EQ(run.DigestCheck(), ProtectDigestCheck::kMatched);
}

TEST(ProtectResetDescription, TheResetPragmasTakeTheNamesAwayWhenEncrypting) {
  for (std::string_view reset :
       {"`pragma reset protect\n", "`pragma resetall\n"}) {
    std::string source = ReachesTheKey();
    source.append(reset).append(RegionAround(kSealedDesign));
    EXPECT_FALSE(Holds(Encrypted(source), kBlockOpening)) << reset;
  }
}

TEST(ProtectResetDescription, AResetPragmaNamingAnotherPragmaLeavesTheNames) {
  std::string source = ReachesTheKey();
  source.append("`pragma reset vendor_option\n")
      .append(RegionAround(kSealedDesign));
  EXPECT_TRUE(Holds(Encrypted(source), kBlockOpening));
}

TEST(ProtectResetDescription, AResetUndoesOnlyWhatItsDirectiveWroteAheadOfIt) {
  std::string names = "data_keyowner=\"";
  names.append(kKeyOwner).append("\", data_keyname=\"");
  names.append(kKeyName).append("\"");
  std::string after = "`pragma protect " + names + ", reset\n";
  EXPECT_FALSE(
      Holds(Encrypted(after + RegionAround(kSealedDesign)), kBlockOpening));
  std::string ahead = "`pragma protect reset, " + names + "\n";
  EXPECT_TRUE(
      Holds(Encrypted(ahead + RegionAround(kSealedDesign)), kBlockOpening));
}

TEST(ProtectResetDescription, AResetWrittenWithAValueResetsNothing) {
  std::string names = "data_keyowner=\"";
  names.append(kKeyOwner).append("\", data_keyname=\"");
  names.append(kKeyName).append("\"");
  std::string valued = "`pragma protect " + names + ", reset=\"all\"\n";
  EXPECT_TRUE(
      Holds(Encrypted(valued + RegionAround(kSealedDesign)), kBlockOpening));
}

}  // namespace
