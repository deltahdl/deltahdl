// §34.5.9.2 Description, continued from
// test_preprocessor_subclause_34_05_09_02a for the two rows of Table 34-2 whose
// algorithms write lines: uuencode, the historical algorithm of IEEE Std
// 1003.1, and quoted-printable, IETF RFC 2045's other algorithm. The first file
// reads each of them on a designation no part of this tool wrote; this one
// writes each through EncodeProtectBlock, holds the writing to what the
// published algorithm produces, reads it back, and refuses the characters
// neither algorithm writes.
//
// The writing is driven through EncodeProtectBlock rather than through an
// envelope, because the encrypting half writes an envelope under neither of
// these two today: #4303 is the open question of how it honours a request for
// them, the values §34.5.13.2 and its neighbours announce on the next line
// being ones these two algorithms break across several.
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

#include "fixture_protect_encoding.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_keywords.h"

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

}  // namespace
