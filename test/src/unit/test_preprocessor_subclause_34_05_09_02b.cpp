#include <gtest/gtest.h>

#include <algorithm>
#include <cstddef>
#include <string>
#include <string_view>

#include "fixture_preprocessor.h"
#include "fixture_protect_encoding.h"
#include "helpers_text_lines.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

ProtectEncoding Stated(std::string_view enctype, size_t length) {
  std::string list = "(enctype=\"";
  list.append(enctype).append("\"");
  if (length != 0) list.append(", line_length=").append(std::to_string(length));
  list.append(")");
  ProtectEncoding stated = ParseProtectEncoding(list);
  EXPECT_EQ(stated.enctype, enctype);
  return stated;
}

size_t LongestLine(std::string_view text) {
  size_t longest = 0;
  size_t at = 0;
  while (at <= text.size()) {
    size_t breaks = text.find('\n', at);
    size_t ends = breaks == std::string_view::npos ? text.size() : breaks;
    longest = std::max(longest, ends - at);
    at = ends + 1;
  }
  return longest;
}

std::string EveryByteUpTo(size_t count) {
  std::string data;
  for (size_t b = 0; b < count; ++b) data.push_back(static_cast<char>(b));
  return data;
}

bool ReadsBackAs(std::string_view text, std::string_view enctype,
                 std::string_view data) {
  std::string bytes;
  return DecodeProtectBlock(text, enctype, &bytes) && bytes == data;
}

TEST(ProtectUuencodeWriting, TheWritingIsTheHistoricalAlgorithms) {
  std::string written =
      EncodeProtectBlock(kDesignatedKey, Stated(kUuencodeEnctype, 0));
  EXPECT_EQ(written, std::string(kDesignationInUuencode) + "\n`\n");
}

TEST(ProtectUuencodeWriting, WithNoLengthALineCarriesFortyFiveBytes) {
  std::string data = EveryByteUpTo(100);
  std::string written = EncodeProtectBlock(data, Stated(kUuencodeEnctype, 0));
  EXPECT_EQ(LongestLine(written), 61U) << written;
  EXPECT_TRUE(ReadsBackAs(written, kUuencodeEnctype, data));
}

TEST(ProtectUuencodeWriting, AStatedLengthBoundsEveryLine) {
  std::string data = EveryByteUpTo(100);
  std::string written = EncodeProtectBlock(data, Stated(kUuencodeEnctype, 9));
  EXPECT_EQ(LongestLine(written), 9U) << written;
  EXPECT_TRUE(ReadsBackAs(written, kUuencodeEnctype, data));
}

TEST(ProtectUuencodeWriting, ALengthShortOfOneGroupStillCarriesOne) {
  std::string data = EveryByteUpTo(10);
  std::string written = EncodeProtectBlock(data, Stated(kUuencodeEnctype, 3));
  EXPECT_EQ(LongestLine(written), 5U) << written;
  EXPECT_TRUE(ReadsBackAs(written, kUuencodeEnctype, data));
}

TEST(ProtectUuencodeReading, CarriageReturnsAndBlankLinesAreSteppedOver) {
  std::string text = "\n\r\n";
  text.append(kDesignationInUuencode).append("\r\n`\r\n");
  EXPECT_TRUE(ReadsBackAs(text, kUuencodeEnctype, kDesignatedKey));
}

TEST(ProtectUuencodeReading, ACharacterOutsideTheAlgorithmsRunIsRefused) {
  std::string bytes;
  EXPECT_FALSE(DecodeProtectBlock("a86-M", kUuencodeEnctype, &bytes));
  EXPECT_FALSE(DecodeProtectBlock("\t86-M", kUuencodeEnctype, &bytes));
  EXPECT_FALSE(DecodeProtectBlock("#8a-M", kUuencodeEnctype, &bytes));
  EXPECT_FALSE(DecodeProtectBlock("#8\t-M", kUuencodeEnctype, &bytes));
  EXPECT_TRUE(ReadsBackAs("#86-M", kUuencodeEnctype, "acm"));
}

TEST(ProtectUuencodeReading, ALineShortOfItsAnnouncedLengthIsRefused) {
  std::string bytes;
  EXPECT_FALSE(DecodeProtectBlock("#86", kUuencodeEnctype, &bytes));
}

TEST(ProtectQuotedPrintableWriting, TheWritingIsRfc2045s) {
  EXPECT_EQ(
      EncodeProtectBlock(kDesignatedKey, Stated(kQuotedPrintableEnctype, 0)),
      kDesignationInQuotedPrintable);
}

TEST(ProtectQuotedPrintableWriting, OnlyPrintablesOtherThanEqualsStandAlone) {
  EXPECT_EQ(EncodeProtectBlock(std::string_view(" !<=>~\x7f\xff", 8),
                               Stated(kQuotedPrintableEnctype, 0)),
            "=20!<=3D>~=7F=FF");
}

TEST(ProtectQuotedPrintableWriting, WithNoLengthALineRunsToSeventySix) {
  std::string data = EveryByteUpTo(256);
  std::string written =
      EncodeProtectBlock(data, Stated(kQuotedPrintableEnctype, 0));
  EXPECT_EQ(LongestLine(written), 76U) << written;
  EXPECT_TRUE(ReadsBackAs(written, kQuotedPrintableEnctype, data));
}

TEST(ProtectQuotedPrintableWriting, AStatedLengthBoundsEveryLine) {
  std::string data = EveryByteUpTo(256);
  std::string written =
      EncodeProtectBlock(data, Stated(kQuotedPrintableEnctype, 10));
  EXPECT_EQ(LongestLine(written), 10U) << written;
  EXPECT_TRUE(ReadsBackAs(written, kQuotedPrintableEnctype, data));
}

TEST(ProtectQuotedPrintableReading, WhatAReadingTakesBesidesItsOwnWriting) {
  EXPECT_TRUE(ReadsBackAs("acme=2a=2A", kQuotedPrintableEnctype, "acme**"));
  EXPECT_TRUE(ReadsBackAs("acme=\r\n=20public", kQuotedPrintableEnctype,
                          kDesignatedKey));
  EXPECT_TRUE(ReadsBackAs("acme\r\n=20pub\nlic", kQuotedPrintableEnctype,
                          kDesignatedKey));
}

TEST(ProtectQuotedPrintableReading, AnEscapeTheAlgorithmNeverWritesIsRefused) {
  std::string bytes;
  EXPECT_FALSE(DecodeProtectBlock("acme=", kQuotedPrintableEnctype, &bytes));
  EXPECT_FALSE(DecodeProtectBlock("acme=2", kQuotedPrintableEnctype, &bytes));
  EXPECT_FALSE(DecodeProtectBlock("acme=G0", kQuotedPrintableEnctype, &bytes));
  EXPECT_FALSE(DecodeProtectBlock("acme=0G", kQuotedPrintableEnctype, &bytes));
}

TEST(ProtectQuotedPrintableReading, BlanksEndingALineAreNotData) {
  EXPECT_TRUE(ReadsBackAs("ab=  \ncd", kQuotedPrintableEnctype, "abcd"));
  EXPECT_TRUE(ReadsBackAs("ab \t\ncd", kQuotedPrintableEnctype, "abcd"));
  EXPECT_TRUE(ReadsBackAs("ab=\t\r\ncd  ", kQuotedPrintableEnctype, "abcd"));
  EXPECT_TRUE(ReadsBackAs("a b=20\ncd", kQuotedPrintableEnctype, "a b cd"));
}

TEST(ProtectBase64Writing, WithNoLengthALineRunsToSeventySix) {
  std::string data = EveryByteUpTo(256);
  std::string written = EncodeProtectBlock(data, Stated(kBase64Enctype, 0));
  EXPECT_EQ(LongestLine(written), 76U) << written;
  EXPECT_TRUE(ReadsBackAs(written, kBase64Enctype, data));
}

TEST(ProtectBase64Writing, AStatedLengthBoundsEveryLine) {
  std::string data = EveryByteUpTo(256);
  std::string written = EncodeProtectBlock(data, Stated(kBase64Enctype, 10));
  EXPECT_EQ(LongestLine(written), 10U) << written;
  EXPECT_TRUE(ReadsBackAs(written, kBase64Enctype, data));
}

TEST(ProtectBase64Writing, AOneLineValueIsNeverBroken) {
  std::string data = EveryByteUpTo(256);
  for (std::string_view enctype : {kBase64Enctype, kBlockEnctype}) {
    std::string written = EncodeProtectValue(data, Stated(enctype, 10));
    EXPECT_EQ(written.find('\n'), std::string::npos) << enctype;
    EXPECT_TRUE(ReadsBackAs(written, enctype, data)) << enctype;
  }
  EXPECT_EQ(EncodeProtectValue("a\nb", Stated(kRawEnctype, 0)), "a\nb");
}

TEST(ProtectBase64Reading, CharactersOutsideTheAlphabetAreSteppedOver) {
  std::string data = EveryByteUpTo(40);
  std::string clean = EncodeProtectBlock(data, Stated(kBase64Enctype, 0));
  std::string padded = "  " + clean.substr(0, 21) + " \t\r\n\t" +
                       clean.substr(21, 11) + "*" + clean.substr(32) + "  ";
  EXPECT_TRUE(ReadsBackAs(padded, kBase64Enctype, data));
}

TEST(ProtectBase64Reading, AGroupEndingPartWayThroughAByteIsRefused) {
  std::string bytes;
  EXPECT_FALSE(DecodeProtectBlock("QUJD R", kBase64Enctype, &bytes));
  EXPECT_TRUE(ReadsBackAs("QUJD Rg==", kBase64Enctype, "ABCF"));
}

void ExpectTheDataBlockWrittenIn(std::string_view enctype) {
  std::string envelope = EnvelopeAround(NamesScheme(enctype));
  std::string stated = "`pragma protect encoding=(enctype=\"";
  stated.append(enctype).append("\"");
  EXPECT_TRUE(Holds(ProtectedPartOf(envelope), stated)) << envelope;
  std::string block;
  ASSERT_TRUE(
      DecodeProtectBlock(EncodingDataBlockLinesOf(envelope), enctype, &block));
  std::string recovered;
  EXPECT_TRUE(DecryptProtectedBlock(block, kEncodingExchangeKey, &recovered));
  EXPECT_TRUE(Holds(recovered, kEncodingSealedDesign));
}

TEST(ProtectBlockWriting, AUuencodeRequestWritesTheDataBlockInUuencode) {
  ExpectTheDataBlockWrittenIn(kUuencodeEnctype);
}

TEST(ProtectBlockWriting,
     AQuotedPrintableRequestWritesTheDataBlockInQuotedPrintable) {
  ExpectTheDataBlockWrittenIn(kQuotedPrintableEnctype);
}

TEST(ProtectBlockWriting, ARawRequestWritesTheDataBlockRaw) {
  ExpectTheDataBlockWrittenIn(kRawEnctype);
}

TEST(ProtectBlockWriting, AnEnvelopeWrittenInUuencodeIsReadBack) {
  std::string envelope = EnvelopeAround(NamesScheme(kUuencodeEnctype));
  PreprocFixture f;
  std::string read = Preprocess(envelope, f, HoldingTheKey());
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Holds(read, kEncodingSealedDesign));
}

TEST(ProtectBlockWriting, AKeyBlockWrittenInUuencodeIsReadBack) {
  std::string sealed = SealedByDesignation(
      kUuencodeEnctype, kDesignationInUuencode, kDesignatedKey);
  ASSERT_TRUE(Holds(sealed, kKeyBlockLine));
  ProtectKeyList keys;
  keys.Add({std::string(kKeyProvider), std::string(kDesignatedKey),
            std::string(kProviderKey)});
  PreprocConfig config;
  config.protect_keys = keys;
  PreprocFixture f;
  std::string read = Preprocess(sealed, f, config);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Holds(read, kEncodingSealedDesign));
}

}  // namespace
