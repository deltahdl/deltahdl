// §34.5.2.2 Description, for the protect pragma keyword that closes an
// encryption envelope. The syntax block above it settles how the expression is
// spelled; this one settles what an encrypting tool does when it reads one, and
// it settles it under the three headings the subclause writes its rules under.
//
// ENCRYPTION INPUT. The expression is written in the input cleartext to say
// where the region that is to be encrypted stops. Its counterpart said where a
// region starts, so this one is what fixes the other end of the same interval:
// the text ahead of it, back to the opening expression that answers it, is what
// a tool seals, and the text from it on is text the tool carries across. Moving
// the word one line moves that line from one fate to the other, which is the
// whole of what the rule claims and the one thing a single position cannot
// show.
//
// ENCRYPTION OUTPUT. The expression is replaced by §34.5.4's. It is the word
// that is replaced rather than the directive carrying it, so the expressions
// written beside it went on describing the envelope standing in the region's
// place, and the replacement lands where a region ended rather than wherever
// the word happens to be written -- a word that closed no region is left as the
// author wrote it.
//
// DECRYPTION INPUT: none. The expression asks for nothing on that side, so a
// text carrying one is decrypted exactly as the same text without it would be.
//
// All of it is preprocessor-stage. src/preprocessor/protect_processing.cpp
// reads a source text for the line each region stops at and writes the envelope
// that stands where the region was, over the word held in
// src/preprocessor/protect_envelope.cpp, and
// src/preprocessor/protect_envelope_output.cpp settles where in that envelope
// the produced closing directive is written. The regions here are delimited
// with the real directive syntax of §22.5.1 -- §34.5.1's opening expression is
// what gives this one something to close, and §34.5.4's closing expression is
// both what replaces it and what ends a previously generated block -- and every
// input is driven through those halves and through the preprocessor that reads
// what they produced, rather than handed to the envelope state directly.

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

// The key an author hands the encrypting half, and hands back to whatever reads
// what that half produced. Without one the transformation replaces nothing, and
// a test could not tell a region that was never sealed from a key that was
// never supplied.
constexpr std::string_view kAuthorKey = "acme-exchange-key";

// The design most regions below enclose. Nothing of it survives the writing of
// an encrypted block, so finding these characters in a tool's output is finding
// a region that was not sealed.
constexpr std::string_view kSealedDesign = "  initial result = 42;\n";

// The same design's own text, without the whitespace that positioned it. A
// preprocessed text keeps what a line said rather than how it was laid out, so
// this is what a search of the text reaching the step after the preprocessor
// looks for.
constexpr std::string_view kSealedStatement = "initial result = 42;";

// The design written after a region, which the word closing that region is what
// leaves in the clear.
constexpr std::string_view kPublishedDesign = "  int published = 7;\n";

// The directive that closes an encryption envelope, written as its whole
// expression list. The trailing newline is part of what is searched for: the
// word §34.5.4.1 defines begins with these same characters, so a search without
// it would find that word too and could not tell the two apart.
constexpr std::string_view kClosingDirective = "`pragma protect end\n";

// The directive §34.5.4.1 defines, which is what a closed region's own closing
// directive comes back as.
constexpr std::string_view kProducedClosing = "`pragma protect end_protected";

bool Holds(std::string_view text, std::string_view needle) {
  return text.find(needle) != std::string_view::npos;
}

// How many times `needle` is written in `text`.
size_t Occurrences(std::string_view text, std::string_view needle) {
  size_t count = 0;
  size_t pos = text.find(needle);
  while (pos != std::string_view::npos) {
    ++count;
    pos = text.find(needle, pos + needle.size());
  }
  return count;
}

// Envelope encryption over a source text under the author's key.
std::string Encrypted(const std::string& src) {
  return EncryptEnvelopes(src, kAuthorKey);
}

// The characters a written envelope records its region on. §34.5.15 carries
// them as a quoted pragma_value, so the block is what stands between the
// quotes, and two regions the closing expression bounded differently leave two
// different runs of them.
std::string DataBlockOf(const std::string& written) {
  constexpr std::string_view kOpening = "`pragma protect data_block=\"";
  size_t at = written.find(kOpening);
  if (at == std::string::npos) return {};
  size_t start = at + kOpening.size();
  size_t quoted = written.find('"', start);
  return quoted == std::string::npos ? std::string()
                                     : written.substr(start, quoted - start);
}

// What a user supplies for reading protected regions back. A test reading a
// produced envelope needs the key it was formed under, or the region would stay
// sealed and its absence from the output would say nothing.
PreprocConfig ReadingKey(std::string_view key) {
  PreprocConfig config;
  config.protect_key = std::string(key);
  return config;
}

// A source text read through the whole preprocessor, with what the reading left
// behind kept beside it.
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

// One encryption envelope: §34.5.1's opening expression, then `body`, then
// `closing` -- which the tests below vary, that being the expression this
// subclause defines.
std::string RegionClosedWith(std::string_view body, std::string_view closing) {
  std::string text = "`pragma protect begin\n";
  text.append(body).append(closing);
  return text;
}

// The same region, closed by the expression written as its whole directive.
std::string Region(std::string_view body) {
  return RegionClosedWith(body, kClosingDirective);
}

// ---------------------------------------------------------------------------
// ENCRYPTION INPUT: where the region that is to be encrypted stops.
// ---------------------------------------------------------------------------

// The rule at its plainest, read from both sides of the point the expression
// marks. The design written ahead of the word is text an encrypting tool seals
// and the design written after it is text that tool carries across, so the one
// line between them is what decided the fate of each.
TEST(ProtectEndEncryptionInput, TheExpressionIsWhereTheRegionStops) {
  std::string src = Region(kSealedDesign);
  src.append(kPublishedDesign);
  std::string written = Encrypted(src);
  EXPECT_FALSE(Holds(written, kSealedStatement));
  EXPECT_TRUE(Holds(written, "int published = 7;"));
}

// The same claim put where no single position of the word can answer it: one
// design, with the word written at two different points of it. The line
// between the two positions is inside the region in the first text and outside
// it in the second, so a reading that had sealed a fixed interval -- the whole
// text, or everything to its end -- would return the same partition twice.
TEST(ProtectEndEncryptionInput, MovingTheExpressionMovesWhatIsSealed) {
  std::string stops_early = Region(kSealedDesign);
  stops_early.append(kPublishedDesign);
  std::string both = std::string(kSealedDesign).append(kPublishedDesign);
  EXPECT_TRUE(Holds(Encrypted(stops_early), "int published = 7;"));
  EXPECT_FALSE(Holds(Encrypted(Region(both)), "int published = 7;"));
}

// And what the line that changed sides became. A block records the region the
// expression bounded, so the two texts above leave two different blocks; equal
// blocks would say the extra line went nowhere in either reading.
TEST(ProtectEndEncryptionInput, WhereItStopsDecidesWhatTheBlockRecords) {
  std::string both = std::string(kSealedDesign).append(kPublishedDesign);
  std::string stops_early = Encrypted(Region(kSealedDesign));
  std::string stops_late = Encrypted(Region(both));
  EXPECT_FALSE(DataBlockOf(stops_early).empty());
  EXPECT_NE(DataBlockOf(stops_early), DataBlockOf(stops_late));
}

// The region the expression bounded is a region that is to be encrypted rather
// than one merely dropped. Reading the produced envelope back under the key it
// was formed under returns the design, so the characters missing from the
// output went into the block the word closed.
TEST(ProtectEndEncryptionInput, TheBoundedRegionIsEncryptedRatherThanDropped) {
  std::string written = Encrypted(Region(kSealedDesign));
  EXPECT_FALSE(Holds(written, kSealedStatement));
  ReadSource read(written, kAuthorKey);
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_TRUE(Holds(read.text, kSealedStatement));
}

// The other syntactic position §22.5.1 allows the expression: last in a list
// whose earlier expressions describe the envelope. The list is one run of
// expressions however it is spread over directives, so the region stops where
// the word stands rather than where its directive does, and the design written
// on the line after it stays in the clear.
TEST(ProtectEndEncryptionInput, AListedExpressionStopsTheRegionToo) {
  std::string closing = "`pragma protect author=\"Acme Corp\", end\n";
  std::string src = RegionClosedWith(kSealedDesign, closing);
  src.append(kPublishedDesign);
  std::string written = Encrypted(src);
  EXPECT_FALSE(Holds(written, kSealedStatement));
  EXPECT_TRUE(Holds(written, "int published = 7;"));
}

// The remaining order over such a list. A comma ends the expression before it,
// so a valued keyword written after the word describes neither the word nor the
// region's stopping, and the word standing ahead of it stops the region as it
// does standing alone.
TEST(ProtectEndEncryptionInput, TheExpressionAheadOfAValuedOneStopsItToo) {
  std::string closing = "`pragma protect end, comment=\"sealed above\"\n";
  std::string src = RegionClosedWith(kSealedDesign, closing);
  src.append(kPublishedDesign);
  std::string written = Encrypted(src);
  EXPECT_FALSE(Holds(written, kSealedStatement));
  EXPECT_TRUE(Holds(written, "int published = 7;"));
}

// The last position the word can be written in on its line: with a comment
// after it. A comment is not a pragma expression, so the word ahead of one is
// the word standing alone and the region stops on that line like any other.
//
// What is asked here is the division rather than the produced directive. The
// other heading's case for this spelling asks what became of the comment, and
// an envelope appearing in its output says the region closed somewhere; it does
// not say the region closed here. So this one writes design on both sides of
// the word and reads off which side each landed on.
TEST(ProtectEndEncryptionInput, ACommentAfterTheWordLeavesTheDivisionInPlace) {
  std::string closing = "`pragma protect end // the region stops here\n";
  std::string src = RegionClosedWith(kSealedDesign, closing);
  src.append(kPublishedDesign);
  std::string written = Encrypted(src);
  EXPECT_FALSE(Holds(written, kSealedStatement));
  EXPECT_TRUE(Holds(written, "int published = 7;"));
}

// Each expression stops a region of its own rather than one of them ending
// whatever encryption a text has open anywhere. A text carrying a single region
// cannot tell those two readings apart, which is why this one carries two with
// cleartext between them.
TEST(ProtectEndEncryptionInput, EachExpressionStopsItsOwnRegion) {
  std::string src = Region("  initial first = 1;\n");
  src.append("  int between = 3;\n");
  src.append(Region("  initial second = 2;\n"));
  std::string written = Encrypted(src);
  EXPECT_FALSE(Holds(written, "initial first = 1;"));
  EXPECT_FALSE(Holds(written, "initial second = 2;"));
  EXPECT_TRUE(Holds(written, "int between = 3;"));
}

// The closest input the rule has to turn away: the same design with no closing
// expression written for the region at all. Nothing then says where the region
// that is to be encrypted stops, so there is no region to seal and the text
// comes back character for character -- including the opening expression, which
// delimits nothing on its own.
TEST(ProtectEndEncryptionInput, WithNoClosingExpressionNothingIsSealed) {
  std::string src = "`pragma protect begin\n";
  src.append(kSealedDesign);
  EXPECT_EQ(Encrypted(src), src);
}

// The other half of that negative form: the expression written where no region
// was ever opened. It stops nothing, because there is nothing under way for it
// to stop, and the design beside it is text of the source like any other.
//
// The equality settles the other heading's negative over this same input at the
// same time, which is why that heading carries no case of its own for it. A
// text that came back byte for byte is a text nothing was written into: the
// word the author wrote is still in it, and §34.5.4's word is not, so the
// closing expression of a region that never existed was replaced by nothing.
TEST(ProtectEndEncryptionInput, TheExpressionWithNoRegionOpenStopsNothing) {
  std::string src(kSealedDesign);
  src.append(kClosingDirective);
  EXPECT_EQ(Encrypted(src), src);
}

// The word standing inside a previously generated protected block, built from
// what §34.5.4 really delimits rather than from a hand-written imitation of it.
// §34.5.3 leaves the expressions of those lines uninterpreted, so the word
// there stops nothing: the region runs on to the word written outside the
// block, and the design after the block goes into the same envelope as the
// design before it.
TEST(ProtectEndEncryptionInput, TheWordInsideAProtectedBlockStopsNothing) {
  std::string body = "`pragma protect begin_protected\n";
  body.append(kClosingDirective);
  body.append("`pragma protect end_protected\n");
  body.append(kSealedDesign);
  std::string written = Encrypted(RegionClosedWith(body, kClosingDirective));
  EXPECT_FALSE(Holds(written, kSealedStatement));
  EXPECT_EQ(Occurrences(written, kProducedClosing), 1U);
}

// ---------------------------------------------------------------------------
// ENCRYPTION OUTPUT: the expression the closing expression is replaced by.
// ---------------------------------------------------------------------------

// The replacement, read in both directions: the word §34.5.4 defines stands in
// the output stream and the word this subclause defines does not. Checking only
// that the first appeared would pass on an output carrying both.
TEST(ProtectEndEncryptionOutput, TheClosingExpressionIsReplaced) {
  std::string written = Encrypted(Region(kSealedDesign));
  EXPECT_TRUE(Holds(written, "`pragma protect end_protected\n"));
  EXPECT_FALSE(Holds(written, kClosingDirective));
}

// It is the expression that is replaced rather than the directive carrying it.
// The expressions written beside it described the region and go on describing
// the envelope standing in its place, so the one thing changed on that line is
// the word naming the delimiter.
TEST(ProtectEndEncryptionOutput, OnlyTheDelimitingWordChangesOnItsLine) {
  std::string closing = "`pragma protect author=\"Acme Corp\", end\n";
  std::string written = Encrypted(RegionClosedWith(kSealedDesign, closing));
  constexpr std::string_view kTransformed =
      "`pragma protect author=\"Acme Corp\", end_protected\n";
  EXPECT_TRUE(Holds(written, kTransformed));
}

// The other side of the same line. An expression written after the delimiter
// belongs to the list the delimiter belongs to, so it is carried onto the
// produced directive on the side it was written on, and the replacement reaches
// only the word between the two.
TEST(ProtectEndEncryptionOutput, ExpressionsAfterTheDelimiterAreCarried) {
  std::string closing = "`pragma protect end, comment=\"sealed above\"\n";
  std::string written = Encrypted(RegionClosedWith(kSealedDesign, closing));
  constexpr std::string_view kTransformed =
      "`pragma protect end_protected, comment=\"sealed above\"\n";
  EXPECT_TRUE(Holds(written, kTransformed));
}

// The one thing written after the delimiter that is not carried across, and the
// reason the two are told apart: a comment is not a pragma expression and
// states nothing about the envelope. The replacement leaves it where the source
// wrote it rather than copying it onto the produced directive.
TEST(ProtectEndEncryptionOutput, ACommentAfterTheDelimiterIsNotCarried) {
  std::string closing = "`pragma protect end // the region stops here\n";
  std::string written = Encrypted(RegionClosedWith(kSealedDesign, closing));
  EXPECT_TRUE(Holds(written, "`pragma protect end_protected\n"));
  EXPECT_FALSE(Holds(written, "the region stops here"));
}

// Where in the produced envelope the replacement lands. The word closed the
// region, so what stands in its place closes the envelope the region became: it
// follows the block recording that region rather than merely appearing
// somewhere in the text. A search of the whole output would be answered by an
// expression written anywhere.
TEST(ProtectEndEncryptionOutput, TheReplacementFollowsTheBlockItCloses) {
  std::string written = Encrypted(Region(kSealedDesign));
  size_t opening = written.find("`pragma protect begin_protected");
  size_t data_block = written.find("`pragma protect data_block=");
  size_t closing = written.find(kProducedClosing);
  ASSERT_NE(opening, std::string::npos);
  ASSERT_NE(data_block, std::string::npos);
  ASSERT_NE(closing, std::string::npos);
  EXPECT_LT(opening, data_block);
  EXPECT_LT(data_block, closing);
}

// The replacement is made once per region rather than once per text. Two
// regions written one after another leave two envelopes, so each of the two
// words the source wrote was replaced where it stood.
TEST(ProtectEndEncryptionOutput, EachRegionsWordIsReplacedWhereItStood) {
  std::string src = Region("  initial first = 1;\n");
  src.append(Region("  initial second = 2;\n"));
  std::string written = Encrypted(src);
  EXPECT_EQ(Occurrences(written, kProducedClosing), 2U);
  EXPECT_FALSE(Holds(written, kClosingDirective));
}

// The closest input that gets no replacement is a word with no region for it to
// have closed, and it is settled under the heading above: a text that came back
// byte for byte was written into nowhere, so the word standing in it was
// replaced by nothing. Restating that here would be the same call over the same
// characters, asking less of the answer.
//
// The input that gets none for a different reason is a region with no key to be
// sealed under. There is nothing for an envelope to record, so no envelope is
// written and the expression stands in the output as the author wrote it.
TEST(ProtectEndEncryptionOutput, WithNoKeyTheExpressionStandsAsWritten) {
  std::string src = Region(kSealedDesign);
  EXPECT_EQ(EncryptEnvelopes(src, ""), src);
}

// The same claim on the path that really reads the text. A caller with nowhere
// to report to is handed a keyless text straight back without its regions being
// walked at all, so the case above would answer the same however the
// replacement behaved -- it observes the shortcut rather than the rule.
//
// Asking to be told what the input carried is what suppresses that shortcut,
// and the walk then reaches this region, finds the word, and finds no key for
// the region it closed. Nothing was written for the word to have been replaced
// in, so the word comes back where the author put it.
TEST(ProtectEndEncryptionOutput, TheUnreplacedWordSurvivesTheReadingItself) {
  std::string src = Region(kSealedDesign);
  ProtectEncryptionReport report;
  // Byte equality is the whole of the claim: a text nothing was written into
  // still carries the word the author wrote and carries §34.5.4's nowhere.
  // Naming those two characters again would only restate what it already says.
  EXPECT_EQ(EncryptEnvelopes(src, "", ProtectKeyList(), &report), src);
}

// A word inside a previously generated protected block is replaced by nothing
// either, and for a different reason than the two above: it is text of the
// region being sealed, so it goes into the block along with the design. Neither
// the word nor a replacement for it is anywhere in the output.
TEST(ProtectEndEncryptionOutput, AWordInsideAProtectedBlockIsSealedInstead) {
  std::string body = "`pragma protect begin_protected\n";
  body.append(kClosingDirective);
  body.append("`pragma protect end_protected\n");
  body.append(kSealedDesign);
  std::string written = Encrypted(RegionClosedWith(body, kClosingDirective));
  EXPECT_FALSE(Holds(written, kClosingDirective));
  EXPECT_EQ(Occurrences(written, kProducedClosing), 1U);
}

// ---------------------------------------------------------------------------
// DECRYPTION INPUT: none.
// ---------------------------------------------------------------------------

// The expression asks for nothing on the decryption side. A region delimited by
// it in a decryption input stream holds cleartext, so there is nothing to put
// back and the design between the delimiters reaches the step after the
// preprocessor exactly as it was written.
TEST(ProtectEndDecryptionInput, TheExpressionDecryptsNothing) {
  ReadSource run(Region(kSealedDesign), kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, kSealedStatement));
}

// And it changes nothing about the envelopes that do ask for something. The
// same produced envelope is read with the expression standing ahead of it and
// gives up the same design, so the expression plays no part in what a
// decryption input stream yields.
TEST(ProtectEndDecryptionInput, AnEnvelopeAfterItYieldsTheSameDesign) {
  std::string written = Encrypted(Region(kSealedDesign));
  ReadSource plain(written, kAuthorKey);
  ReadSource preceded(std::string(kClosingDirective) + written, kAuthorKey);
  EXPECT_FALSE(preceded.diag.HasErrors());
  EXPECT_TRUE(Holds(plain.text, kSealedStatement));
  EXPECT_TRUE(Holds(preceded.text, kSealedStatement));
}

// The remaining position the expression can be written in on that side: inside
// a decryption envelope, among the expressions describing the block about to be
// opened. It describes nothing there either, so the block opens on what the
// envelope really did state and gives up the same design.
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
