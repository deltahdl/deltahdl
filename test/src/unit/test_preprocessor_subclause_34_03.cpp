#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

constexpr std::string_view kAuthorKey = "acme-exchange-key";
constexpr std::string_view kStrangerKey = "not-the-authors-key";

struct ReadWithKey {
  SourceManager mgr;
  DiagEngine diag{mgr};
  std::string text;

  ReadWithKey(const std::string& src, std::string_view key) {
    PreprocConfig config;
    config.protect_key = key;
    Preprocessor pp(mgr, diag, config);
    text = pp.Preprocess(mgr.AddFile("<test>", src));
  }
};

bool Holds(std::string_view text, std::string_view needle) {
  return text.find(needle) != std::string_view::npos;
}

std::string Encrypted(const std::string& src) {
  return EncryptEnvelopes(src, kAuthorKey);
}

constexpr std::string_view kBlockAnnouncement = "`pragma protect data_block\n";

std::vector<std::string> RecordedRegions(std::string_view text) {
  std::vector<std::string> regions;
  size_t pos = text.find(kBlockAnnouncement);
  while (pos != std::string_view::npos) {
    size_t start = pos + kBlockAnnouncement.size();
    size_t close = text.find('\n', start);
    regions.emplace_back(text.substr(start, close - start));
    pos = text.find(kBlockAnnouncement, close);
  }
  return regions;
}

uint32_t LineOfTheBlock(std::string_view written) {
  return LineHolding(written, kBlockAnnouncement) + 1;
}

std::string Recovered(const std::string& region, std::string_view key) {
  std::string cleartext;
  if (!DecryptProtectedRegion(region, key, &cleartext)) return "";
  return cleartext;
}

bool Recoverable(const std::string& region, std::string_view key) {
  std::string cleartext;
  return DecryptProtectedRegion(region, key, &cleartext);
}

std::string OneRegion(const std::string& src) {
  std::vector<std::string> regions = RecordedRegions(Encrypted(src));
  return regions.empty() ? "" : regions.front();
}

std::string DataBlockLine(const std::string& region) {
  return std::string(kBlockAnnouncement) + region + "\n";
}

std::string EnvelopeAround(const std::string& region,
                           const std::string& inner) {
  return "`pragma protect begin_protected\n" + DataBlockLine(region) + inner +
         "`pragma protect end_protected\n";
}

TEST(ProtectedEnvelopeProcessing, EncryptionEnvelopeBecomesDecryptionEnvelope) {
  std::string transformed = Encrypted(
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n");
  EXPECT_TRUE(Holds(transformed, "`pragma protect begin_protected\n"));
  EXPECT_TRUE(Holds(transformed, "`pragma protect end_protected\n"));
  EXPECT_FALSE(Holds(transformed, "`pragma protect begin\n"));
  EXPECT_FALSE(Holds(transformed, "`pragma protect end\n"));
}

TEST(ProtectedEnvelopeProcessing, EncryptedRegionTextIsNotInTheOutput) {
  std::string transformed = Encrypted(
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n");
  EXPECT_FALSE(Holds(transformed, "initial result = 42;"));
  ASSERT_EQ(RecordedRegions(transformed).size(), 1U);
  EXPECT_EQ(Recovered(RecordedRegions(transformed)[0], kAuthorKey),
            "  initial result = 42;\n");
}

TEST(ProtectedEnvelopeProcessing, TextWithNoEnvelopeIsReturnedUnchanged) {
  std::string src =
      "module m;\n"
      "  initial result = 1;\n"
      "endmodule\n";
  EXPECT_EQ(Encrypted(src), src);
  EXPECT_TRUE(RecordedRegions(Encrypted(src)).empty());
}

TEST(ProtectedEnvelopeProcessing, UnclosedRegionIsNotTransformed) {
  std::string transformed = Encrypted(
      "`pragma protect begin\n"
      "  initial result = 42;\n");
  EXPECT_TRUE(Holds(transformed, "initial result = 42;"));
  EXPECT_TRUE(RecordedRegions(transformed).empty());
}

TEST(ProtectedEnvelopeProcessing, DecryptionEnvelopeIsNotEncryptedAgain) {
  std::string src =
      "`pragma protect begin_protected\n"
      "  initial result = 42;\n"
      "`pragma protect end_protected\n";
  EXPECT_EQ(Encrypted(src), src);
}

TEST(ProtectedEnvelopeProcessing, EveryEncryptionEnvelopeIsTransformed) {
  std::string transformed = Encrypted(
      "`pragma protect begin\n"
      "  initial first = 1;\n"
      "`pragma protect end\n"
      "  initial between = 2;\n"
      "`pragma protect begin\n"
      "  initial second = 3;\n"
      "`pragma protect end\n");
  ASSERT_EQ(RecordedRegions(transformed).size(), 2U);
  EXPECT_EQ(Recovered(RecordedRegions(transformed)[0], kAuthorKey),
            "  initial first = 1;\n");
  EXPECT_EQ(Recovered(RecordedRegions(transformed)[1], kAuthorKey),
            "  initial second = 3;\n");
  EXPECT_TRUE(Holds(transformed, "initial between = 2;"));
}

TEST(ProtectedEnvelopeProcessing, AnEmptyRegionIsStillAnEnvelope) {
  std::vector<std::string> regions =
      RecordedRegions(Encrypted("`pragma protect begin\n"
                                "`pragma protect end\n"));
  ASSERT_EQ(regions.size(), 1U);
  EXPECT_FALSE(regions.front().empty());
  EXPECT_TRUE(Recoverable(regions.front(), kAuthorKey));
  EXPECT_EQ(Recovered(regions.front(), kAuthorKey), "");
}

TEST(ProtectedEnvelopeProcessing, AnEmptyRegionAddsNoTextAndTakesNone) {
  ReadWithKey run(Encrypted("module m;\n"
                            "`pragma protect begin\n"
                            "`pragma protect end\n"
                            "endmodule\n"),
                  kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, "module m;"));
  EXPECT_TRUE(Holds(run.text, "endmodule"));
  EXPECT_FALSE(Holds(run.text, "data_block"));
}

TEST(ProtectedEnvelopeProcessing, DelimiterBesideOtherExpressionsIsRecognized) {
  std::string transformed = Encrypted(
      "`pragma protect data_method=\"x-caesar\", key_keyname=\"rot13\", begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n");
  ASSERT_EQ(RecordedRegions(transformed).size(), 1U);
  EXPECT_EQ(Recovered(RecordedRegions(transformed)[0], kAuthorKey),
            "  initial result = 42;\n");
}

TEST(ProtectedEnvelopeProcessing, MacroInsideARegionIsNotExpanded) {
  std::string transformed = Encrypted(
      "`pragma protect begin\n"
      "`define WIDTH 8\n"
      "  logic [`WIDTH-1:0] bus;\n"
      "`pragma protect end\n");
  ASSERT_EQ(RecordedRegions(transformed).size(), 1U);
  EXPECT_EQ(Recovered(RecordedRegions(transformed)[0], kAuthorKey),
            "`define WIDTH 8\n  logic [`WIDTH-1:0] bus;\n");
}

TEST(ProtectedEnvelopeProcessing, IncludeInsideARegionIsNotResolved) {
  std::string transformed = Encrypted(
      "`pragma protect begin\n"
      "`include \"no_such_file_anywhere.svh\"\n"
      "`pragma protect end\n");
  ASSERT_EQ(RecordedRegions(transformed).size(), 1U);
  EXPECT_EQ(Recovered(RecordedRegions(transformed)[0], kAuthorKey),
            "`include \"no_such_file_anywhere.svh\"\n");
}

TEST(ProtectedEnvelopeProcessing, OtherPragmaInsideARegionIsNotActedOn) {
  std::string transformed = Encrypted(
      "`pragma protect begin\n"
      "`pragma acme_tool begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n");
  ASSERT_EQ(RecordedRegions(transformed).size(), 1U);
  EXPECT_EQ(Recovered(RecordedRegions(transformed)[0], kAuthorKey),
            "`pragma acme_tool begin\n  initial result = 42;\n");
}

TEST(ProtectedEnvelopeProcessing, RegionThatIsNotSystemVerilogRoundTrips) {
  std::string transformed = Encrypted(
      "`pragma protect begin\n"
      "!! this is not a design ((\n"
      "\"unterminated\n"
      "`pragma protect end\n");
  ASSERT_EQ(RecordedRegions(transformed).size(), 1U);
  EXPECT_EQ(Recovered(RecordedRegions(transformed)[0], kAuthorKey),
            "!! this is not a design ((\n\"unterminated\n");
}

TEST(ProtectedEnvelopeProcessing, TextOutsideAnEnvelopeIsCopiedNotInterpreted) {
  std::string transformed = Encrypted(
      "`define WIDTH 8\n"
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n"
      "  logic [`WIDTH-1:0] bus;\n");
  EXPECT_TRUE(Holds(transformed, "`define WIDTH 8\n"));
  EXPECT_TRUE(Holds(transformed, "  logic [`WIDTH-1:0] bus;\n"));
}

TEST(ProtectedEnvelopeProcessing, AWordInsideABlockCommentOpensNoRegion) {
  const std::string kSource =
      "/*\n"
      "`pragma protect begin\n"
      "*/\n"
      "module m; endmodule\n"
      "`pragma protect end\n";
  EXPECT_EQ(Encrypted(kSource), kSource);
}

TEST(ProtectedEnvelopeProcessing, AWordInsideABlockCommentClosesNoRegion) {
  std::string transformed = Encrypted(
      "`pragma protect begin\n"
      "/* `pragma protect end\n"
      "`pragma protect end */\n"
      "  initial result = 42;\n"
      "`pragma protect end\n");
  EXPECT_EQ(transformed.find("initial result = 42;"), std::string::npos)
      << transformed;
  EXPECT_NE(transformed.find("`pragma protect end_protected"),
            std::string::npos)
      << transformed;
}

TEST(ProtectedEnvelopeProcessing, DelimiterUnderAnotherPragmaNameDelimitsNone) {
  std::string src =
      "`pragma acme_tool begin\n"
      "  initial result = 42;\n"
      "`pragma acme_tool end\n";
  EXPECT_EQ(Encrypted(src), src);
  EXPECT_TRUE(RecordedRegions(Encrypted(src)).empty());
}

TEST(ProtectedEnvelopeProcessing, DecryptionPutsTheCleartextBack) {
  ReadWithKey run(Encrypted("`pragma protect begin\n"
                            "  initial result = 42;\n"
                            "`pragma protect end\n"),
                  kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, "initial result = 42;"));
  EXPECT_FALSE(Holds(run.text, "data_block"));
  EXPECT_FALSE(Holds(run.text, "pragma"));
}

TEST(ProtectedEnvelopeProcessing, DecryptionRecoversEveryLineOfTheRegion) {
  ReadWithKey run(Encrypted("`pragma protect begin\n"
                            "  initial first = 1;\n"
                            "  initial second = 2;\n"
                            "  initial third = 3;\n"
                            "`pragma protect end\n"),
                  kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  size_t first = run.text.find("initial first = 1;");
  size_t second = run.text.find("initial second = 2;");
  size_t third = run.text.find("initial third = 3;");
  EXPECT_NE(first, std::string::npos);
  EXPECT_LT(first, second);
  EXPECT_LT(second, third);
  EXPECT_NE(third, std::string::npos);
}

TEST(ProtectedEnvelopeProcessing, EveryDecryptionEnvelopeIsProcessed) {
  ReadWithKey run(Encrypted("`pragma protect begin\n"
                            "  initial first = 1;\n"
                            "`pragma protect end\n"
                            "`pragma protect begin\n"
                            "  initial second = 2;\n"
                            "`pragma protect end\n"),
                  kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, "initial first = 1;"));
  EXPECT_TRUE(Holds(run.text, "initial second = 2;"));
}

TEST(ProtectedEnvelopeProcessing, ANestedDecryptionEnvelopeIsProcessedToo) {
  std::string outer = OneRegion(
      "`pragma protect begin\n"
      "  initial outer_value = 1;\n"
      "`pragma protect end\n");
  std::string inner = OneRegion(
      "`pragma protect begin\n"
      "  initial inner_value = 2;\n"
      "`pragma protect end\n");
  ReadWithKey run(EnvelopeAround(outer, EnvelopeAround(inner, "")), kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, "initial outer_value = 1;"));
  EXPECT_TRUE(Holds(run.text, "initial inner_value = 2;"));
}

TEST(ProtectedEnvelopeProcessing, EveryRegionOfOneEnvelopeIsPutBack) {
  std::string first = OneRegion(
      "`pragma protect begin\n"
      "  initial first = 1;\n"
      "`pragma protect end\n");
  std::string second = OneRegion(
      "`pragma protect begin\n"
      "  initial second = 2;\n"
      "`pragma protect end\n");
  ReadWithKey run("`pragma protect begin_protected\n" + DataBlockLine(first) +
                      DataBlockLine(second) + "`pragma protect end_protected\n",
                  kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, "initial first = 1;"));
  EXPECT_TRUE(Holds(run.text, "initial second = 2;"));
  EXPECT_LT(run.text.find("initial first = 1;"),
            run.text.find("initial second = 2;"));
}

TEST(ProtectedEnvelopeProcessing, ABlockBesideAnotherExpressionIsPutBack) {
  std::string only = OneRegion(
      "`pragma protect begin\n"
      "  initial only_one = 7;\n"
      "`pragma protect end\n");
  ReadWithKey run(
      "`pragma protect begin_protected\n"
      "`pragma protect author=\"acme ip\", data_block\n" +
          only + "\n`pragma protect end_protected\n",
      kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, "initial only_one = 7;"));
  EXPECT_FALSE(Holds(run.text, only));
}

TEST(ProtectedEnvelopeProcessing, AKeyThatIsNotTheProperOneRecoversNothing) {
  std::string sealed = Encrypted(
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n");
  ReadWithKey run(sealed, kStrangerKey);
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma data block cannot be decrypted with the key supplied",
      LineOfTheBlock(sealed), "34.3.2"));
  EXPECT_FALSE(Holds(run.text, "initial result = 42;"));
}

TEST(ProtectedEnvelopeProcessing, NoKeySuppliedRecoversNothing) {
  std::string sealed = Encrypted(
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n");
  ReadWithKey run(sealed, "");
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma data block cannot be decrypted with the key supplied",
      LineOfTheBlock(sealed), "34.3.2"));
  EXPECT_FALSE(Holds(run.text, "initial result = 42;"));
}

TEST(ProtectedEnvelopeProcessing, AnEnvelopeRecordingNoRegionPassesQuietly) {
  ReadWithKey run(
      "`pragma protect begin_protected\n"
      "  initial result = 42;\n"
      "`pragma protect end_protected\n",
      kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, "initial result = 42;"));
}

TEST(ProtectedEnvelopeProcessing, ARegionOutsideAnEnvelopeIsNotRecovered) {
  std::string region = OneRegion(
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n");
  ReadWithKey run(DataBlockLine(region), kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(Holds(run.text, "initial result = 42;"));
  EXPECT_TRUE(Holds(run.text, region));
}

constexpr std::string_view kSealedBody = "  initial guarded = 7;\n";
constexpr std::string_view kSealingKey = "acme-exchange-key-of-the-year-2026";

TEST(ProtectedEnvelopeProcessing, AKeyMatchingTheBlocksLengthOpensNothing) {
  const size_t kBlockBytes = ProtectedRegionBlockSize(kSealedBody);
  ASSERT_GE(kSealingKey.size(), kBlockBytes);
  const std::string kImpostorKey =
      std::string(kSealingKey.substr(0, kBlockBytes)) + "-impostor";
  ASSERT_EQ(kImpostorKey.substr(0, kBlockBytes),
            std::string(kSealingKey.substr(0, kBlockBytes)));
  ASSERT_NE(kImpostorKey, std::string(kSealingKey));
  std::string bytes;
  ASSERT_TRUE(DecodeProtectBlock(
      EncryptProtectedRegion(kSealedBody, kSealingKey), kBlockEnctype, &bytes));
  std::string cleartext;
  EXPECT_FALSE(DecryptProtectedBlock(bytes, kImpostorKey, &cleartext));
}

TEST(ProtectedEnvelopeProcessing, KeysAlikeButForTheirLastCharacterSealApart) {
  const size_t kBlockBytes = ProtectedRegionBlockSize(kSealedBody);
  ASSERT_LT(kBlockBytes, kSealingKey.size());
  std::string sibling_key(kSealingKey);
  sibling_key.back() = static_cast<char>(sibling_key.back() + 1);
  ASSERT_EQ(sibling_key.substr(0, sibling_key.size() - 1),
            std::string(kSealingKey.substr(0, kSealingKey.size() - 1)));
  ASSERT_NE(sibling_key, std::string(kSealingKey));
  EXPECT_NE(EncryptProtectedRegion(kSealedBody, kSealingKey),
            EncryptProtectedRegion(kSealedBody, sibling_key));
}

TEST(ProtectedEnvelopeProcessing, TheKeyTheRegionWasSealedUnderOpensIt) {
  std::string region = EncryptProtectedRegion(kSealedBody, kSealingKey);
  std::string bytes;
  ASSERT_TRUE(DecodeProtectBlock(region, kBlockEnctype, &bytes));
  std::string cleartext;
  EXPECT_TRUE(DecryptProtectedBlock(bytes, kSealingKey, &cleartext));
  EXPECT_EQ(cleartext, kSealedBody);
  EXPECT_EQ(Recovered(region, kSealingKey), kSealedBody);
}

TEST(ProtectedEnvelopeProcessing, AValueOutsideTheAlphabetRecordsNoRegion) {
  EXPECT_FALSE(Recoverable("AAAA*AAA", kAuthorKey));
  ReadWithKey run(EnvelopeAround("AAAA*AAA", ""), kAuthorKey);
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma value is not written in the encoding in effect", 3,
      "34.5.9.2"));
}

TEST(ProtectedEnvelopeProcessing, AValueEndingMidGroupRecordsNoRegion) {
  EXPECT_FALSE(Recoverable("AAAAA", kAuthorKey));
  ReadWithKey run(EnvelopeAround("AAAAA", ""), kAuthorKey);
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma value is not written in the encoding in effect", 3,
      "34.5.9.2"));
}

TEST(ProtectedEnvelopeProcessing, AValueShorterThanAFingerprintRecordsNone) {
  EXPECT_FALSE(Recoverable("AAA", kAuthorKey));
  ReadWithKey run(EnvelopeAround("AAA", ""), kAuthorKey);
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma data block cannot be decrypted with the key supplied", 3,
      "34.3.2"));
}

}  // namespace
