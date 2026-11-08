#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>

#include "fixture_preprocessor.h"
#include "fixture_protect_encoding.h"
#include "helpers_reported_error.h"
#include "helpers_text_lines.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

TEST(ProtectEncodingEncryptionInput, TheSchemeARegionNamesWritesItsBlock) {
  std::string envelope = EnvelopeAround(NamesScheme(kBase64Enctype));
  ASSERT_TRUE(Holds(envelope, "enctype=\"base64\""));
  std::string block;
  ASSERT_TRUE(DecodeProtectBlock(EncodingDataBlockLinesOf(envelope),
                                 kBase64Enctype, &block));
  std::string recovered;
  EXPECT_TRUE(DecryptProtectedBlock(block, kEncodingExchangeKey, &recovered));
  EXPECT_TRUE(Holds(recovered, kEncodingSealedDesign));
}

TEST(ProtectEncodingEncryptionInput, TheBlockIsNotTheWritingOfAnotherScheme) {
  std::string envelope = EnvelopeAround(NamesScheme(kBase64Enctype));
  std::string block;
  ASSERT_TRUE(
      DecodeProtectBlock(EncodingDataBlockOf(envelope), kRawEnctype, &block));
  std::string recovered;
  EXPECT_FALSE(DecryptProtectedBlock(block, kEncodingExchangeKey, &recovered));
}

TEST(ProtectEncodingEncryptionInput, ASchemeNamedAheadOfARegionWritesItsBlock) {
  std::string source(NamesScheme(kBase64Enctype));
  source.append(RegionHolding(""));
  std::string envelope = EnvelopeOf(source);
  ASSERT_TRUE(Holds(envelope, "enctype=\"base64\""));
  std::string block;
  ASSERT_TRUE(DecodeProtectBlock(EncodingDataBlockLinesOf(envelope),
                                 kBase64Enctype, &block));
  std::string recovered;
  EXPECT_TRUE(DecryptProtectedBlock(block, kEncodingExchangeKey, &recovered));
  EXPECT_TRUE(Holds(recovered, kEncodingSealedDesign));
}

TEST(ProtectEncodingEncryptionInput, ACountWrittenInARegionReachesNoEnvelope) {
  std::string inside(
      StatesEncoding("(enctype=\"base64\", line_length=8, bytes=1)"));
  std::string envelope = EnvelopeAround(inside);
  size_t held = ProtectedRegionBlockSize(EncodingRegionBody(inside));
  EXPECT_TRUE(Holds(envelope, "enctype=\"base64\""));
  EXPECT_TRUE(Holds(envelope, TheCountOf(held)));
  EXPECT_FALSE(Holds(envelope, TheCountOf(1)));
}

TEST(ProtectEncodingEncryptionInput,
     ACountWrittenAheadOfARegionReachesNoEnvelope) {
  std::string source(StatesEncoding("(enctype=\"base64\", bytes=1)"));
  source.append(RegionHolding(""));
  std::string envelope = ProtectedPartOf(EnvelopeOf(source));
  ASSERT_FALSE(envelope.empty());
  EXPECT_TRUE(Holds(envelope, "enctype=\"base64\""));
  EXPECT_TRUE(Holds(
      envelope, TheCountOf(ProtectedRegionBlockSize(kEncodingSealedDesign))));
  EXPECT_FALSE(Holds(envelope, TheCountOf(1)));
}

TEST(ProtectEncodingEncryptionInput,
     TheSameCountIsActedOnWhenAnEnvelopeIsRead) {
  std::string list = "(enctype=\"";
  list.append(DefaultProtectEncoding().enctype).append("\", bytes=1)");
  PreprocFixture f;
  std::string src = EnvelopeReadUnder(StatesEncoding(list));
  std::string read = Preprocess(src, f, HoldingTheKey());
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "protect pragma value stands for a different number of bytes from the "
      "one the encoding in effect states",
      LineHolding(src, kEncodingBlockOpening) + 1, "34.5.9.2"));
  EXPECT_FALSE(Holds(read, "module sealed_m"));
}

TEST(ProtectEncodingTable, TheTableSetsFourIdentifiersAside) {
  auto rows = ProtectEncodingAlgorithms();
  ASSERT_EQ(rows.size(), 4U);
  EXPECT_EQ(rows[0].enctype, "uuencode");
  EXPECT_EQ(rows[1].enctype, "base64");
  EXPECT_EQ(rows[2].enctype, "quoted-printable");
  EXPECT_EQ(rows[3].enctype, "raw");
}

TEST(ProtectEncodingTable, EachRowNamesAnAlgorithmOfItsOwn) {
  auto rows = ProtectEncodingAlgorithms();
  ASSERT_EQ(rows.size(), 4U);
  for (size_t row = 0; row < rows.size(); ++row) {
    EXPECT_FALSE(rows[row].algorithm.empty());
    for (size_t other = row + 1; other < rows.size(); ++other) {
      EXPECT_NE(rows[row].algorithm, rows[other].algorithm);
    }
  }
}

TEST(ProtectEncodingTable, TheRequiredIdentifiersAreProvidedAndSoAreTheRest) {
  EXPECT_TRUE(IsRequiredProtectEncodingAlgorithm(kUuencodeEnctype));
  EXPECT_TRUE(IsRequiredProtectEncodingAlgorithm(kBase64Enctype));
  EXPECT_FALSE(IsRequiredProtectEncodingAlgorithm(kQuotedPrintableEnctype));
  EXPECT_FALSE(IsRequiredProtectEncodingAlgorithm(kRawEnctype));
  EXPECT_FALSE(IsRequiredProtectEncodingAlgorithm(kUnprovidedEnctype));
  EXPECT_TRUE(ProtectEncodingIsAvailable(kQuotedPrintableEnctype));
  EXPECT_TRUE(ProtectEncodingIsAvailable(kRawEnctype));
}

TEST(ProtectEncodingTable, TheToolsOwnIdentifierIsNoneOfTheTabulatedFour) {
  EXPECT_FALSE(IsProtectEncodingAlgorithm(kBlockEnctype));
  EXPECT_TRUE(ProtectEncodingIsAvailable(kBlockEnctype));
  EXPECT_FALSE(ProtectEncodingIsAvailable(kUnprovidedEnctype));
}

TEST(ProtectEncodingTable, TheRequiredBase64IdentifierReadsADesignation) {
  std::string sealed =
      SealedByDesignation(kBase64Enctype, kDesignationInBase64, kDesignatedKey);
  EXPECT_FALSE(Holds(sealed, kEncodingSealedDesign));
  EXPECT_TRUE(Holds(sealed, kKeyBlockLine));
}

TEST(ProtectEncodingTable, TheRequiredUuencodeIdentifierReadsADesignation) {
  std::string sealed = SealedByDesignation(
      kUuencodeEnctype, kDesignationInUuencode, kDesignatedKey);
  EXPECT_FALSE(Holds(sealed, kEncodingSealedDesign));
  EXPECT_TRUE(Holds(sealed, kKeyBlockLine));
}

TEST(ProtectEncodingTable,
     TheOptionalQuotedPrintableIdentifierReadsADesignation) {
  std::string sealed = SealedByDesignation(
      kQuotedPrintableEnctype, kDesignationInQuotedPrintable, kDesignatedKey);
  EXPECT_FALSE(Holds(sealed, kEncodingSealedDesign));
  EXPECT_TRUE(Holds(sealed, kKeyBlockLine));
}

TEST(ProtectEncodingTable, TheSameLineStandsForAnotherValueUnderRaw) {
  std::string as_written = SealedByDesignation(
      kRawEnctype, kDesignationInBase64, kDesignationInBase64);
  std::string as_base64 = SealedByDesignation(
      kBase64Enctype, kDesignationInBase64, kDesignationInBase64);
  EXPECT_FALSE(Holds(as_written, kEncodingSealedDesign));
  EXPECT_TRUE(Holds(as_base64, kEncodingSealedDesign));
}

TEST(ProtectEncodingTable, ARawDesignationMayHoldAnUnprintableCharacter) {
  std::string sealed = SealedByDesignation(kRawEnctype, kUnprintableDesignation,
                                           kUnprintableDesignation);
  EXPECT_FALSE(Holds(sealed, kEncodingSealedDesign));
  EXPECT_TRUE(Holds(sealed, kKeyBlockLine));
}

TEST(ProtectEncodingTable, AnIdentifierNothingProvidesReadsNoDesignation) {
  std::string untouched = SealedByDesignation(
      kUnprovidedEnctype, kDesignationInBase64, kDesignatedKey);
  EXPECT_TRUE(Holds(untouched, kEncodingSealedDesign));
  EXPECT_FALSE(Holds(untouched, kKeyBlockLine));
}

TEST(ProtectEncodingTable, AnIdentifierNothingProvidesWritesAndReadsNothing) {
  ProtectEncoding unprovided;
  unprovided.enctype = std::string(kUnprovidedEnctype);
  EXPECT_EQ(EncodeProtectBlock(kDesignatedKey, unprovided), "");
  std::string bytes = "untouched";
  EXPECT_FALSE(
      DecodeProtectBlock(kDesignationInBase64, kUnprovidedEnctype, &bytes));
  EXPECT_EQ(bytes, "untouched");
}

TEST(ProtectEncodingEncryptionOutput, EveryEnvelopeStatesItsOwnWriting) {
  std::string envelope = EnvelopeAround("");
  EXPECT_TRUE(Holds(envelope, kAnyEncoding));
  std::string named = "enctype=\"";
  named.append(DefaultProtectEncoding().enctype).append("\"");
  EXPECT_TRUE(Holds(envelope, named));
  PreprocFixture f;
  std::string read = Preprocess(envelope, f, HoldingTheKey());
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Holds(read, "module sealed_m"));
}

TEST(ProtectEncodingEncryptionOutput, TheCountIsOfTheDataAndNotOfTheWriting) {
  std::string envelope = EnvelopeAround("");
  EXPECT_TRUE(Holds(
      envelope, TheCountOf(ProtectedRegionBlockSize(kEncodingSealedDesign))));
  EXPECT_NE(ProtectedRegionBlockSize(kEncodingSealedDesign),
            kEncodingSealedDesign.size());
  EXPECT_NE(ProtectedRegionBlockSize(kEncodingSealedDesign),
            EncodingDataBlockOf(envelope).size());
}

TEST(ProtectEncodingEncryptionOutput, EachBlockOfAnEnvelopeStatesItsOwnCount) {
  std::string envelope = EnvelopeAround(kDigestBlockLine);
  size_t held = ProtectedRegionBlockSize(kEncodingSealedDesign);
  ASSERT_TRUE(Holds(envelope, kDigestBlockLine));
  EXPECT_EQ(TimesWritten(envelope, kAnyEncoding), 3U);
  EXPECT_EQ(TimesWritten(envelope, "bytes="), 2U);
  EXPECT_EQ(TimesWritten(envelope, TheCountOf(held)), 1U);
}

TEST(ProtectEncodingEncryptionOutput, EveryBlockIsWrittenUnderTheOneScheme) {
  std::string inside(kDigestBlockLine);
  inside.append(NamesScheme(kBase64Enctype));
  std::string envelope = EnvelopeAround(inside);
  EXPECT_EQ(TimesWritten(envelope, "enctype=\"base64\""), 3U);
  std::string digest;
  EXPECT_TRUE(DecodeProtectBlock(LineAfter(envelope, kDigestBlockLine),
                                 kBase64Enctype, &digest));
  EXPECT_FALSE(digest.empty());
}

TEST(ProtectEncodingEncryptionOutput, TheDataKeyDesignationIsRewrittenAsWell) {
  std::string envelope = EnvelopeOf(
      RegionDesignatingTheDataKey(kUuencodeEnctype, kDesignationInUuencode));
  std::string named = "enctype=\"";
  named.append(kBlockEnctype).append("\"");
  ASSERT_TRUE(Holds(envelope, named));
  std::string written = LineAfter(envelope, kDataPublicKeyLine);
  EXPECT_NE(written, kDesignationInUuencode);
  std::string key;
  ASSERT_TRUE(DecodeProtectBlock(written, kBlockEnctype, &key));
  EXPECT_EQ(key, kDesignatedKey);
  EXPECT_TRUE(Holds(envelope, TheCountOf(kDesignatedKey.size())));
}

TEST(ProtectEncodingEncryptionOutput, TheKeyDesignationIsRewrittenAsWell) {
  std::string envelope = SealedByDesignation(
      kUuencodeEnctype, kDesignationInUuencode, kDesignatedKey);
  ASSERT_FALSE(Holds(envelope, kEncodingSealedDesign));
  std::string written = LineAfter(envelope, kKeyPublicKeyLine);
  EXPECT_NE(written, kDesignationInUuencode);
  std::string key;
  ASSERT_TRUE(DecodeProtectBlock(written, kBlockEnctype, &key));
  EXPECT_EQ(key, kDesignatedKey);
}

TEST(ProtectEncodingEncryptionOutput, AKeyBlockAndTheKeyInItAreUnderTheScheme) {
  std::string envelope =
      SealedByDesignation(kBase64Enctype, kDesignationInBase64, kDesignatedKey);
  ASSERT_FALSE(Holds(envelope, kEncodingSealedDesign));
  ASSERT_TRUE(Holds(envelope, "enctype=\"base64\""));
  std::string block;
  ASSERT_TRUE(DecodeProtectBlock(BlockLinesAfter(envelope, kKeyBlockLine),
                                 kBase64Enctype, &block));
  std::string carried;
  ASSERT_TRUE(DecryptProtectedBlock(block, kProviderKey, &carried));
  std::string region_key;
  ASSERT_TRUE(DecodeProtectBlock(LineAfter(carried, kDataDecryptKeyLine),
                                 kBase64Enctype, &region_key));
  std::string design;
  EXPECT_TRUE(DecryptProtectedRegion(EncodingDataBlockLinesOf(envelope),
                                     region_key, &design, kBase64Enctype));
  EXPECT_TRUE(Holds(design, kEncodingSealedDesign));
}

TEST(ProtectEncodingEncryptionOutput, AnExpressionStandsAheadOfEveryField) {
  std::string envelope =
      SealedByDesignation(kBase64Enctype, kDesignationInBase64, kDesignatedKey);
  size_t expressions = TimesWritten(envelope, kAnyEncoding);
  size_t counts = TimesWritten(envelope, "bytes=");
  EXPECT_GE(counts, 3U);
  EXPECT_EQ(expressions, counts + 1);
}

TEST(ProtectEncodingEncryptionOutput, EachEnvelopeOfATextStatesItsWriting) {
  std::string text = EncryptEnvelopes(TwoRegions(), kEncodingExchangeKey);
  EXPECT_FALSE(Holds(text, kEncodingSealedDesign));
  EXPECT_FALSE(Holds(text, kSecondDesign));
  size_t first = text.find(kProtectedOpening);
  ASSERT_NE(first, std::string::npos);
  size_t second = text.find(kProtectedOpening, first + 1);
  ASSERT_NE(second, std::string::npos);
  EXPECT_TRUE(Holds(text.substr(first, second - first), kAnyEncoding));
  EXPECT_TRUE(Holds(text.substr(second), kAnyEncoding));
  PreprocFixture f;
  std::string read = Preprocess(text, f, HoldingTheKey());
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Holds(read, "module sealed_m"));
  EXPECT_TRUE(Holds(read, "module sealed_n"));
}

TEST(ProtectEncodingEncryptionOutput, TheBlockHoldsOnlyWhatASourceLineCarries) {
  std::string region = "`pragma protect begin\n";
  region.append(kAwkwardDesign).append("`pragma protect end\n");
  std::string block =
      EncodingDataBlockOf(EncryptEnvelopes(region, kEncodingExchangeKey));
  ASSERT_FALSE(block.empty());
  bool text_only = true;
  for (char c : block) {
    auto byte = static_cast<unsigned char>(c);
    if (byte < 0x21U || byte > 0x7EU || c == '"') text_only = false;
  }
  EXPECT_TRUE(text_only);
  std::string recovered;
  EXPECT_TRUE(DecryptProtectedRegion(block, kEncodingExchangeKey, &recovered));
  EXPECT_TRUE(Holds(recovered, kAwkwardDesign));
}

TEST(ProtectEncodingEncryptionOutput, AnEnvelopeStatesTheLengthItBrokeAt) {
  constexpr size_t kLengthAskedFor = 8;
  std::string list = "(enctype=\"base64\", line_length=";
  list.append(std::to_string(kLengthAskedFor)).append(")");
  std::string envelope = EnvelopeAround(StatesEncoding(list));
  ASSERT_TRUE(Holds(envelope, "enctype=\"base64\""));
  EXPECT_TRUE(Holds(envelope, "line_length=8"));
  EXPECT_LE(EncodingDataBlockOf(envelope).size(), kLengthAskedFor);
  EXPECT_GT(EncodingDataBlockLinesOf(envelope).size(), kLengthAskedFor);

  PreprocFixture f;
  std::string read = Preprocess(envelope, f, HoldingTheKey());
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Holds(read, kEncodingSealedDesign));
}

TEST(ProtectEncodingEncryptionOutput, TheStatedLengthBreaksTheDataBlockAlone) {
  std::string list = "(enctype=\"base64\", line_length=8)";
  std::string envelope =
      EnvelopeAround(StatesEncoding(list) + std::string(kDigestBlockLine));
  ASSERT_TRUE(Holds(envelope, "line_length=8"));
  EXPECT_TRUE(Holds(EncodingDataBlockLinesOf(envelope), "\n"));

  std::string digest = BlockLinesAfter(envelope, kDigestBlockLine);
  EXPECT_FALSE(digest.empty()) << envelope;
  EXPECT_FALSE(Holds(digest, "\n")) << envelope;
}

TEST(ProtectEncodingEncryptionOutput, TheStatedLengthBreaksTheWriting) {
  ProtectEncoding stated =
      ParseProtectEncoding("(enctype=\"base64\", line_length=8)");
  ASSERT_EQ(stated.line_length, 8U);
  std::string written = EncodeProtectBlock(kEncodingSealedDesign, stated);
  EXPECT_TRUE(Holds(written, "\n"));
  size_t at = 0;
  while (at < written.size()) {
    size_t breaks = written.find('\n', at);
    size_t ends = breaks == std::string::npos ? written.size() : breaks;
    EXPECT_LE(ends - at, 8U);
    at = ends + 1;
  }
  std::string recovered;
  EXPECT_TRUE(DecodeProtectBlock(written, kBase64Enctype, &recovered));
  EXPECT_EQ(recovered, kEncodingSealedDesign);
}

TEST(ProtectEncodingEncryptionOutput, ALengthTheWritingFitsInBreaksNothing) {
  ProtectEncoding stated =
      ParseProtectEncoding("(enctype=\"base64\", line_length=1000)");
  ASSERT_EQ(stated.line_length, 1000U);
  std::string written = EncodeProtectBlock(kEncodingSealedDesign, stated);
  EXPECT_FALSE(Holds(written, "\n"));
  EXPECT_FALSE(written.empty());
}

TEST(ProtectEncodingDecryptionInput, ACarriageReturnInABreakIsNotData) {
  std::string bytes;
  ASSERT_TRUE(
      DecodeProtectBlock("YWNtZSBw\r\ndWJsaWM=", kBase64Enctype, &bytes));
  EXPECT_EQ(bytes, kDesignatedKey);
}

TEST(ProtectEncodingDecryptionInput, ACarriageReturnInTheToolsSchemeIsNotData) {
  ProtectEncoding encoding;
  encoding.enctype = std::string(kBlockEnctype);
  std::string written = EncodeProtectBlock(kDesignatedKey, encoding);
  ASSERT_GT(written.size(), 4U);
  written.insert(4, "\r\n");
  std::string bytes;
  ASSERT_TRUE(DecodeProtectBlock(written, kBlockEnctype, &bytes));
  EXPECT_EQ(bytes, kDesignatedKey);
}

TEST(ProtectEncodingEncryptionOutput, TheIdentityTransformationBreaksNoLine) {
  ProtectEncoding stated =
      ParseProtectEncoding("(enctype=\"raw\", line_length=8)");
  ASSERT_EQ(stated.enctype, kRawEnctype);
  ASSERT_EQ(stated.line_length, 8U);
  ASSERT_GT(kEncodingSealedDesign.size(), stated.line_length);
  EXPECT_EQ(EncodeProtectBlock(kEncodingSealedDesign, stated),
            kEncodingSealedDesign);
}

TEST(ProtectEncodingDecryptionInput, TheStatedSchemeIsWhatOpensTheBlock) {
  std::string envelope = EnvelopeAround(NamesScheme(kBase64Enctype));
  PreprocFixture f;
  std::string read = Preprocess(envelope, f, HoldingTheKey());
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Holds(read, "module sealed_m"));
}

TEST(ProtectEncodingDecryptionInput, ABlockDeclaredWronglyDoesNotOpen) {
  PreprocFixture f;
  std::string src = EnvelopeReadUnder(NamesScheme(kRawEnctype));
  std::string read = Preprocess(src, f, HoldingTheKey());
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "protect pragma data block cannot be decrypted with the key supplied",
      LineHolding(src, kEncodingBlockOpening) + 1, "34.3.2"));
  EXPECT_FALSE(Holds(read, "module sealed_m"));
}

TEST(ProtectEncodingDecryptionInput, ABlockUnderAnUnprovidedSchemeIsNotRead) {
  std::string declared = NamesScheme(kUnprovidedEnctype);
  PreprocFixture f;
  std::string src = EnvelopeReadUnder(declared);
  std::string read = Preprocess(src, f, HoldingTheKey());
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "protect pragma encoding names an enctype this "
                            "implementation does not provide",
                            LineHolding(src, kEncodingBlockOpening) + 1,
                            "34.5.9.2"));
  EXPECT_FALSE(Holds(read, "module sealed_m"));
}

TEST(ProtectEncodingDecryptionInput, AFieldIsReadUnderTheExpressionAboveIt) {
  PreprocFixture f;
  std::string read = Preprocess(EnvelopeOpeningWith(NamesScheme(kRawEnctype)),
                                f, HoldingTheKey());
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Holds(read, "module sealed_m"));
}

TEST(ProtectEncodingDecryptionInput, ADigestBlockIsReadUnderTheSameScheme) {
  std::string inside(kDigestBlockLine);
  inside.append(NamesScheme(kBase64Enctype));
  std::string envelope = EnvelopeAround(inside);
  ASSERT_TRUE(Holds(envelope, kDigestBlockLine));
  PreprocFixture f;
  std::string read = Preprocess(envelope, f, HoldingTheKey());
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Holds(read, "module sealed_m"));
}

TEST(ProtectEncodingDecryptionInput, TheCountIsSpentOnTheBlockItStandsAheadOf) {
  std::string envelope = EnvelopeAround("");
  size_t block = envelope.find(kEncodingBlockOpening);
  ASSERT_NE(block, std::string::npos);
  size_t ends = envelope.find('\n', block + kEncodingBlockOpening.size());
  ASSERT_NE(ends, std::string::npos);
  std::string written(kDataPublicKeyLine);
  written.append(EncodeProtectBlock(kDesignatedKey, DefaultProtectEncoding()));
  written.append("\n");
  envelope.insert(ends + 1, written);

  PreprocFixture f;
  std::string read = Preprocess(envelope, f, HoldingTheKey());
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Holds(read, "module sealed_m"));
}

std::string IndentedRawBlockUnder(std::string_view bytes) {
  std::string src =
      "`pragma protect data_method=\"des-cbc\", begin_protected\n";
  src.append("`pragma protect encoding=(enctype=\"raw\", bytes=");
  src.append(bytes).append("), data_block\n");
  src.append("ab\n  cd\nef\n");
  src.append("`pragma protect end_protected\n");
  return src;
}

TEST(ProtectEncodingDecryptionInput, ARawBlockIsItsTextAsWritten) {
  PreprocFixture f;
  std::string src = IndentedRawBlockUnder("11");
  Preprocess(src, f, HoldingTheKey());
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "protect pragma data block cannot be decrypted with the key supplied", 3,
      "34.3.2"));
}

TEST(ProtectEncodingDecryptionInput, ARawBlockIsNotReadAtItsTrimmedCount) {
  PreprocFixture f;
  std::string src = IndentedRawBlockUnder("8");
  Preprocess(src, f, HoldingTheKey());
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "protect pragma value stands for a different "
                            "number of bytes from the one the encoding in "
                            "effect states",
                            3, "34.5.9.2"));
}

}  // namespace
