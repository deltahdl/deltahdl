#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

constexpr std::string_view kAuthorKey = "acme-exchange-key";

constexpr std::string_view kSealedDesign = "  initial result = 42;\n";

constexpr std::string_view kSealedStatement = "initial result = 42;";

constexpr std::string_view kPublishedDesign = "  int published = 7;\n";

constexpr std::string_view kClosingDirective = "`pragma protect end\n";

constexpr std::string_view kProducedClosing = "`pragma protect end_protected";

bool Holds(std::string_view text, std::string_view needle) {
  return text.find(needle) != std::string_view::npos;
}

size_t Occurrences(std::string_view text, std::string_view needle) {
  size_t count = 0;
  size_t pos = text.find(needle);
  while (pos != std::string_view::npos) {
    ++count;
    pos = text.find(needle, pos + needle.size());
  }
  return count;
}

std::string Encrypted(const std::string& src) {
  return EncryptEnvelopes(src, kAuthorKey);
}

std::string DataBlockOf(const std::string& written) {
  constexpr std::string_view kAnnounces = "`pragma protect data_block\n";
  size_t at = written.find(kAnnounces);
  if (at == std::string::npos) return {};
  size_t start = at + kAnnounces.size();
  size_t ends = written.find('\n', start);
  return ends == std::string::npos ? std::string()
                                   : written.substr(start, ends - start);
}

PreprocConfig ReadingKey(std::string_view key) {
  PreprocConfig config;
  config.protect_key = std::string(key);
  return config;
}

struct ReadSource {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp;
  std::string text;

  ReadSource(const std::string& src, std::string_view key)
      : pp(mgr, diag, ReadingKey(key)) {
    text = pp.Preprocess(mgr.AddFile("<test>", src));
  }
};

std::string RegionClosedWith(std::string_view body, std::string_view closing) {
  std::string text = "`pragma protect begin\n";
  text.append(body).append(closing);
  return text;
}

std::string Region(std::string_view body) {
  return RegionClosedWith(body, kClosingDirective);
}

TEST(ProtectEndEncryptionInput, TheExpressionIsWhereTheRegionStops) {
  std::string src = Region(kSealedDesign);
  src.append(kPublishedDesign);
  std::string written = Encrypted(src);
  EXPECT_FALSE(Holds(written, kSealedStatement));
  EXPECT_TRUE(Holds(written, "int published = 7;"));
}

TEST(ProtectEndEncryptionInput, MovingTheExpressionMovesWhatIsSealed) {
  std::string stops_early = Region(kSealedDesign);
  stops_early.append(kPublishedDesign);
  std::string both = std::string(kSealedDesign).append(kPublishedDesign);
  EXPECT_TRUE(Holds(Encrypted(stops_early), "int published = 7;"));
  EXPECT_FALSE(Holds(Encrypted(Region(both)), "int published = 7;"));
}

TEST(ProtectEndEncryptionInput, WhereItStopsDecidesWhatTheBlockRecords) {
  std::string both = std::string(kSealedDesign).append(kPublishedDesign);
  std::string stops_early = Encrypted(Region(kSealedDesign));
  std::string stops_late = Encrypted(Region(both));
  EXPECT_FALSE(DataBlockOf(stops_early).empty());
  EXPECT_NE(DataBlockOf(stops_early), DataBlockOf(stops_late));
}

TEST(ProtectEndEncryptionInput, TheBoundedRegionIsEncryptedRatherThanDropped) {
  std::string written = Encrypted(Region(kSealedDesign));
  EXPECT_FALSE(Holds(written, kSealedStatement));
  ReadSource read(written, kAuthorKey);
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_TRUE(Holds(read.text, kSealedStatement));
}

TEST(ProtectEndEncryptionInput, AListedExpressionStopsTheRegionToo) {
  std::string closing = "`pragma protect author=\"Acme Corp\", end\n";
  std::string src = RegionClosedWith(kSealedDesign, closing);
  src.append(kPublishedDesign);
  std::string written = Encrypted(src);
  EXPECT_FALSE(Holds(written, kSealedStatement));
  EXPECT_TRUE(Holds(written, "int published = 7;"));
}

TEST(ProtectEndEncryptionInput, TheExpressionAheadOfAValuedOneStopsItToo) {
  std::string closing = "`pragma protect end, comment=\"sealed above\"\n";
  std::string src = RegionClosedWith(kSealedDesign, closing);
  src.append(kPublishedDesign);
  std::string written = Encrypted(src);
  EXPECT_FALSE(Holds(written, kSealedStatement));
  EXPECT_TRUE(Holds(written, "int published = 7;"));
}

TEST(ProtectEndEncryptionInput, ACommentAfterTheWordLeavesTheDivisionInPlace) {
  std::string closing = "`pragma protect end // the region stops here\n";
  std::string src = RegionClosedWith(kSealedDesign, closing);
  src.append(kPublishedDesign);
  std::string written = Encrypted(src);
  EXPECT_FALSE(Holds(written, kSealedStatement));
  EXPECT_TRUE(Holds(written, "int published = 7;"));
}

TEST(ProtectEndEncryptionInput, EachExpressionStopsItsOwnRegion) {
  std::string src = Region("  initial first = 1;\n");
  src.append("  int between = 3;\n");
  src.append(Region("  initial second = 2;\n"));
  std::string written = Encrypted(src);
  EXPECT_FALSE(Holds(written, "initial first = 1;"));
  EXPECT_FALSE(Holds(written, "initial second = 2;"));
  EXPECT_TRUE(Holds(written, "int between = 3;"));
}

TEST(ProtectEndEncryptionInput, WithNoClosingExpressionNothingIsSealed) {
  std::string src = "`pragma protect begin\n";
  src.append(kSealedDesign);
  EXPECT_EQ(Encrypted(src), src);
}

TEST(ProtectEndEncryptionInput, TheExpressionWithNoRegionOpenStopsNothing) {
  std::string src(kSealedDesign);
  src.append(kClosingDirective);
  EXPECT_EQ(Encrypted(src), src);
}

TEST(ProtectEndEncryptionInput, TheWordInsideAProtectedBlockStopsNothing) {
  std::string body = "`pragma protect begin_protected\n";
  body.append(kClosingDirective);
  body.append("`pragma protect end_protected\n");
  body.append(kSealedDesign);
  std::string written = Encrypted(RegionClosedWith(body, kClosingDirective));
  EXPECT_FALSE(Holds(written, kSealedStatement));
  EXPECT_EQ(Occurrences(written, kProducedClosing), 1U);
}

TEST(ProtectEndEncryptionOutput, TheClosingExpressionIsReplaced) {
  std::string written = Encrypted(Region(kSealedDesign));
  EXPECT_TRUE(Holds(written, "`pragma protect end_protected\n"));
  EXPECT_FALSE(Holds(written, kClosingDirective));
}

TEST(ProtectEndEncryptionOutput, AnUnterminatedLastLineIsReplacedToo) {
  std::string written =
      Encrypted(RegionClosedWith(kSealedDesign, "`pragma protect end"));
  EXPECT_FALSE(Holds(written, kSealedStatement));
  EXPECT_TRUE(Holds(written, "`pragma protect end_protected\n"));
}

TEST(ProtectEndEncryptionOutput, ExpressionsAheadOfTheWordAreTheRegions) {
  std::string closing = "`pragma protect author=\"Acme Corp\", end\n";
  std::string written = Encrypted(RegionClosedWith(kSealedDesign, closing));
  EXPECT_TRUE(Holds(written, "`pragma protect end_protected\n")) << written;
  EXPECT_TRUE(Holds(written, "`pragma protect author=\"Acme Corp\"\n"))
      << written;
  EXPECT_LT(written.find("`pragma protect author="),
            written.find("`pragma protect data_block"))
      << written;
}

TEST(ProtectEndEncryptionOutput, ExpressionsAfterTheDelimiterAreCarried) {
  std::string closing = "`pragma protect end, comment=\"sealed above\"\n";
  std::string written = Encrypted(RegionClosedWith(kSealedDesign, closing));
  constexpr std::string_view kTransformed =
      "`pragma protect end_protected, comment=\"sealed above\"\n";
  EXPECT_TRUE(Holds(written, kTransformed));
}

TEST(ProtectEndEncryptionOutput, ACommentAfterTheDelimiterIsNotCarried) {
  std::string closing = "`pragma protect end // the region stops here\n";
  std::string written = Encrypted(RegionClosedWith(kSealedDesign, closing));
  EXPECT_TRUE(Holds(written, "`pragma protect end_protected\n"));
  EXPECT_FALSE(Holds(written, "the region stops here"));
}

TEST(ProtectEndEncryptionOutput, TheReplacementFollowsTheBlockItCloses) {
  std::string written = Encrypted(Region(kSealedDesign));
  size_t opening = written.find("`pragma protect begin_protected");
  size_t data_block = written.find("`pragma protect data_block\n");
  size_t closing = written.find(kProducedClosing);
  ASSERT_NE(opening, std::string::npos);
  ASSERT_NE(data_block, std::string::npos);
  ASSERT_NE(closing, std::string::npos);
  EXPECT_LT(opening, data_block);
  EXPECT_LT(data_block, closing);
}

TEST(ProtectEndEncryptionOutput, EachRegionsWordIsReplacedWhereItStood) {
  std::string src = Region("  initial first = 1;\n");
  src.append(Region("  initial second = 2;\n"));
  std::string written = Encrypted(src);
  EXPECT_EQ(Occurrences(written, kProducedClosing), 2U);
  EXPECT_FALSE(Holds(written, kClosingDirective));
}

TEST(ProtectEndEncryptionOutput, WithNoKeyTheExpressionStandsAsWritten) {
  std::string src = Region(kSealedDesign);
  EXPECT_EQ(EncryptEnvelopes(src, ""), src);
}

TEST(ProtectEndEncryptionOutput, TheUnreplacedWordSurvivesTheReadingItself) {
  std::string src = Region(kSealedDesign);
  SourceManager mgr;
  DiagEngine diag(mgr);
  EXPECT_EQ(EncryptEnvelopes(src, "", ProtectKeyList(), &diag,
                             mgr.AddFile("<test>", src)),
            src);
}

TEST(ProtectEndEncryptionOutput, AWordInsideAProtectedBlockIsSealedInstead) {
  std::string body = "`pragma protect begin_protected\n";
  body.append(kClosingDirective);
  body.append("`pragma protect end_protected\n");
  body.append(kSealedDesign);
  std::string written = Encrypted(RegionClosedWith(body, kClosingDirective));
  EXPECT_FALSE(Holds(written, kClosingDirective));
  EXPECT_EQ(Occurrences(written, kProducedClosing), 1U);
}

TEST(ProtectEndDecryptionInput, TheExpressionDecryptsNothing) {
  ReadSource run(Region(kSealedDesign), kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, kSealedStatement));
}

TEST(ProtectEndDecryptionInput, AnEnvelopeAfterItYieldsTheSameDesign) {
  std::string written = Encrypted(Region(kSealedDesign));
  ReadSource plain(written, kAuthorKey);
  ReadSource preceded(std::string(kClosingDirective) + written, kAuthorKey);
  EXPECT_FALSE(preceded.diag.HasErrors());
  EXPECT_TRUE(Holds(plain.text, kSealedStatement));
  EXPECT_TRUE(Holds(preceded.text, kSealedStatement));
}

TEST(ProtectEndDecryptionInput, TheExpressionInsideAnEnvelopeChangesNothing) {
  std::string written = Encrypted(Region(kSealedDesign));
  size_t first_line = written.find('\n');
  ASSERT_NE(first_line, std::string::npos);
  std::string spliced = written.substr(0, first_line + 1);
  spliced.append(kClosingDirective);
  spliced.append(written.substr(first_line + 1));
  ReadSource run(spliced, kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, kSealedStatement));
}

}  // namespace
