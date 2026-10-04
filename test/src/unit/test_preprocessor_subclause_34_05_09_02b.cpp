// §34.5.9.2 Description, continued from
// test_preprocessor_subclause_34_05_09_02a for the two rows of Table 34-2 whose
// algorithms write lines: uuencode, the historical algorithm of IEEE Std
// 1003.1, and quoted-printable, IETF RFC 2045's other algorithm. The first file
// reads each of them on a designation no part of this tool wrote; this one
// writes each through EncodeProtectBlock, holds the writing to what the
// published algorithm produces, reads it back, and refuses the characters
// neither algorithm writes.
//
// Most of the writing is driven through EncodeProtectBlock, which holds it to
// the published algorithm alone. The cases at the end drive it through an
// envelope: the encrypting half writes its blocks under either of these two,
// or raw, where a text asks for it, and keeps the values §34.5.13.2 and its
// neighbours announce on the next line under a one-line scheme.
//
// A text written under either one runs to several lines by construction:
// uuencode ends every line after a set number of bytes and closes its output
// with a line carrying none, and quoted-printable breaks a line before the
// byte that would carry it past the length, with an equals sign standing for
// the break. §34.5.9.2's line_length is the most characters one such line may
// hold, so the same length is asked of both.
//
// All of it is preprocessor-stage: src/preprocessor/protect_encoding.cpp picks
// the algorithm by identifier and src/preprocessor/protect_encoding_codecs.cpp
// carries both.

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

// The descriptor a directive naming `enctype` with `length` against
// line_length reads as, taken from the spelling §34.5.9.1 writes rather than
// assembled by hand.
ProtectEncoding Stated(std::string_view enctype, size_t length) {
  std::string list = "(enctype=\"";
  list.append(enctype).append("\"");
  if (length != 0) list.append(", line_length=").append(std::to_string(length));
  list.append(")");
  ProtectEncoding stated = ParseProtectEncoding(list);
  EXPECT_EQ(stated.enctype, enctype);
  return stated;
}

// The longest line of `text`.
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

// Data holding every byte value from zero up, so that a writing is asked about
// bytes it writes as themselves, bytes it escapes, and more of them than one
// line carries.
std::string EveryByteUpTo(size_t count) {
  std::string data;
  for (size_t b = 0; b < count; ++b) data.push_back(static_cast<char>(b));
  return data;
}

// Whether `text` reads back under `enctype` as `data`.
bool ReadsBackAs(std::string_view text, std::string_view enctype,
                 std::string_view data) {
  std::string bytes;
  return DecodeProtectBlock(text, enctype, &bytes) && bytes == data;
}

// ---------------------------------------------------------------------------
// uuencode: a length character, the data six bits to a character, and a
// closing line carrying no data.
// ---------------------------------------------------------------------------

// The key the first file reads out of kDesignationInUuencode, written here.
// The line is that designation character for character, and a line of the
// grave accent alone follows it: the length character of a line carrying no
// data, which is how the algorithm says the data are complete.
TEST(ProtectUuencodeWriting, TheWritingIsTheHistoricalAlgorithms) {
  std::string written =
      EncodeProtectBlock(kDesignatedKey, Stated(kUuencodeEnctype, 0));
  EXPECT_EQ(written, std::string(kDesignationInUuencode) + "\n`\n");
}

// No length stated, so each line carries the forty-five bytes the algorithm
// puts on one: a length character and sixty characters of data.
TEST(ProtectUuencodeWriting, WithNoLengthALineCarriesFortyFiveBytes) {
  std::string data = EveryByteUpTo(100);
  std::string written = EncodeProtectBlock(data, Stated(kUuencodeEnctype, 0));
  EXPECT_EQ(LongestLine(written), 61U) << written;
  EXPECT_TRUE(ReadsBackAs(written, kUuencodeEnctype, data));
}

// A stated length puts as many whole groups of four characters on a line as
// fit behind its length character. Nine leaves room for two groups.
TEST(ProtectUuencodeWriting, AStatedLengthBoundsEveryLine) {
  std::string data = EveryByteUpTo(100);
  std::string written = EncodeProtectBlock(data, Stated(kUuencodeEnctype, 9));
  EXPECT_EQ(LongestLine(written), 9U) << written;
  EXPECT_TRUE(ReadsBackAs(written, kUuencodeEnctype, data));
}

// A length too short for a length character and one group still gets one
// group, a line of no data being the algorithm's mark that the data are over
// rather than a line data can be written on.
TEST(ProtectUuencodeWriting, ALengthShortOfOneGroupStillCarriesOne) {
  std::string data = EveryByteUpTo(10);
  std::string written = EncodeProtectBlock(data, Stated(kUuencodeEnctype, 3));
  EXPECT_EQ(LongestLine(written), 5U) << written;
  EXPECT_TRUE(ReadsBackAs(written, kUuencodeEnctype, data));
}

// A text written on a system that ends its lines with a carriage return as
// well, with blank lines ahead of the data, one of each ending: all are
// stepped over, and the designation reads as the one written with bare line
// feeds.
TEST(ProtectUuencodeReading, CarriageReturnsAndBlankLinesAreSteppedOver) {
  std::string text = "\n\r\n";
  text.append(kDesignationInUuencode).append("\r\n`\r\n");
  EXPECT_TRUE(ReadsBackAs(text, kUuencodeEnctype, kDesignatedKey));
}

// The characters the algorithm writes run from the space to the grave accent.
// A small letter lies above that run and a tab below it, so neither came out
// of the algorithm, whether it stands as a line's length or among its data.
TEST(ProtectUuencodeReading, ACharacterOutsideTheAlgorithmsRunIsRefused) {
  std::string bytes;
  EXPECT_FALSE(DecodeProtectBlock("a86-M", kUuencodeEnctype, &bytes));
  EXPECT_FALSE(DecodeProtectBlock("\t86-M", kUuencodeEnctype, &bytes));
  EXPECT_FALSE(DecodeProtectBlock("#8a-M", kUuencodeEnctype, &bytes));
  EXPECT_FALSE(DecodeProtectBlock("#8\t-M", kUuencodeEnctype, &bytes));
  EXPECT_TRUE(ReadsBackAs("#86-M", kUuencodeEnctype, "acm"));
}

// A line announcing more data than its characters carry. '#' announces three
// bytes, which take a group of four characters, and only two stand behind it.
TEST(ProtectUuencodeReading, ALineShortOfItsAnnouncedLengthIsRefused) {
  std::string bytes;
  EXPECT_FALSE(DecodeProtectBlock("#86", kUuencodeEnctype, &bytes));
}

// ---------------------------------------------------------------------------
// quoted-printable: printable bytes as themselves, the rest as an equals sign
// and two hex digits, and an equals sign ending a line to break it.
// ---------------------------------------------------------------------------

// The key the first file reads out of kDesignationInQuotedPrintable, written
// here. The space is escaped and the letters stand for themselves.
TEST(ProtectQuotedPrintableWriting, TheWritingIsRfc2045s) {
  EXPECT_EQ(
      EncodeProtectBlock(kDesignatedKey, Stated(kQuotedPrintableEnctype, 0)),
      kDesignationInQuotedPrintable);
}

// Which bytes stand for themselves: the printable run from '!' to '~' but for
// the equals sign the scheme takes for its escape. The space below that run,
// the equals sign inside it, and the bytes above it are escaped, the digits
// in capitals.
TEST(ProtectQuotedPrintableWriting, OnlyPrintablesOtherThanEqualsStandAlone) {
  EXPECT_EQ(EncodeProtectBlock(std::string_view(" !<=>~\x7f\xff", 8),
                               Stated(kQuotedPrintableEnctype, 0)),
            "=20!<=3D>~=7F=FF");
}

// No length stated, so a line runs to the seventy-six characters RFC 2045
// allows, broken with the equals sign that stands for no data.
TEST(ProtectQuotedPrintableWriting, WithNoLengthALineRunsToSeventySix) {
  std::string data = EveryByteUpTo(256);
  std::string written =
      EncodeProtectBlock(data, Stated(kQuotedPrintableEnctype, 0));
  EXPECT_EQ(LongestLine(written), 76U) << written;
  EXPECT_TRUE(ReadsBackAs(written, kQuotedPrintableEnctype, data));
}

// A stated length is the most characters a line holds, the equals sign that
// breaks it among them.
TEST(ProtectQuotedPrintableWriting, AStatedLengthBoundsEveryLine) {
  std::string data = EveryByteUpTo(256);
  std::string written =
      EncodeProtectBlock(data, Stated(kQuotedPrintableEnctype, 10));
  EXPECT_EQ(LongestLine(written), 10U) << written;
  EXPECT_TRUE(ReadsBackAs(written, kQuotedPrintableEnctype, data));
}

// RFC 2045 writes the digits in capitals and has a reading take either case,
// a break written with a carriage return ahead of its line feed, and a line
// ended without an equals sign; none of them is data.
TEST(ProtectQuotedPrintableReading, WhatAReadingTakesBesidesItsOwnWriting) {
  EXPECT_TRUE(ReadsBackAs("acme=2a=2A", kQuotedPrintableEnctype, "acme**"));
  EXPECT_TRUE(ReadsBackAs("acme=\r\n=20public", kQuotedPrintableEnctype,
                          kDesignatedKey));
  EXPECT_TRUE(ReadsBackAs("acme\r\n=20pub\nlic", kQuotedPrintableEnctype,
                          kDesignatedKey));
}

// An equals sign followed by neither a line break nor two hex digits: the
// text ends after it or after one digit, or a digit is not hex. None of these
// comes out of the algorithm.
TEST(ProtectQuotedPrintableReading, AnEscapeTheAlgorithmNeverWritesIsRefused) {
  std::string bytes;
  EXPECT_FALSE(DecodeProtectBlock("acme=", kQuotedPrintableEnctype, &bytes));
  EXPECT_FALSE(DecodeProtectBlock("acme=2", kQuotedPrintableEnctype, &bytes));
  EXPECT_FALSE(DecodeProtectBlock("acme=G0", kQuotedPrintableEnctype, &bytes));
  EXPECT_FALSE(DecodeProtectBlock("acme=0G", kQuotedPrintableEnctype, &bytes));
}

// §34.5.9.2 ENCRYPTION INPUT: the encoding expression a text states decides how
// the data_block, digest_block and key_block of the output are written, and
// Table 34-2 sets four identifiers aside for it. A scheme that breaks its
// output over several lines is honoured for the blocks, whose content runs to
// the next pragma directive, so the data block is written in the scheme asked
// for and reads back by that scheme's algorithm to the block the cipher
// produced. Each case fails on an encrypting tool that writes its own one-line
// scheme in place of the one requested.
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

// §34.5.9.2 DECRYPTION INPUT: a reader takes the scheme each block was written
// in from the expression standing ahead of it, so the envelope written in the
// scheme requested is read back to the design it sealed.
TEST(ProtectBlockWriting, AnEnvelopeWrittenInUuencodeIsReadBack) {
  std::string envelope = EnvelopeAround(NamesScheme(kUuencodeEnctype));
  PreprocFixture f;
  std::string read = Preprocess(envelope, f, HoldingTheKey());
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(Holds(read, kEncodingSealedDesign));
}

// A region whose keys travel in key blocks, its data_decrypt_key written inside
// a block's cleartext on the line beneath its keyword (§34.5.14). That value
// stays on its one line, under a one-line scheme §34.2's sequential reading
// puts in effect ahead of it, while the key block around it is written in the
// scheme requested; a reader holding the provider's key reads the block, then
// the key, then the data. The test fails on a writer that leaves the one-line
// value in a scheme that breaks it over several lines, or a key block in a
// scheme other than the one asked for.
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
