// §34.3 Processing protected envelopes.
//
// The subclause defines the two processes an envelope may be put through and
// then binds each of them to a tool.
//
//   Envelope encryption recognizes the encryption envelopes of a source text
//   and leaves a decryption envelope in the place of each one. A tool that
//   performs it is only obliged to process the protect pragma directives, and
//   applies no other interpretation to text that is not part of one.
//
//   Envelope decryption recognizes the decryption envelopes of an input text
//   and puts back the cleartext each one stands for, for the compilation step
//   that follows. A tool that processes SystemVerilog source text performs it
//   for every decryption envelope the text holds, given the proper key.
//
// Both are preprocessor-stage rules. The encrypting half lives in
// src/preprocessor/protect_processing.cpp, which reads a source text and
// writes one back; the decrypting half is wired into the pragma handler in
// src/preprocessor/preprocessor_lines.cpp, so the text that leaves the
// preprocessor -- the text the compilation step after it reads -- is where its
// effect is observed.
//
// Every envelope here is written as the real `pragma directive syntax of
// §22.11, the dependency both processes consume: an envelope is only ever
// reached by way of directives the preprocessor tokenized and parsed for
// itself. What a decrypted design goes on to compute is observed at the
// simulator stage instead.

#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

// The key an IP author encrypts under. What the rules turn on is whether the
// key a text is read with is the key its regions were written with, so a
// second key is kept beside it to stand for every key that is not the proper
// one.
constexpr std::string_view kAuthorKey = "acme-exchange-key";
constexpr std::string_view kStrangerKey = "not-the-authors-key";

// Preprocesses `src` with `key` supplied for envelope decryption. The text the
// preprocessor produced is what the compilation step after it would read, and
// the diagnostics are kept beside it because one of the rules is about what
// happens when the cleartext cannot be recovered.
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

// Envelope encryption over a source text, under the author's key.
std::string Encrypted(const std::string& src) {
  return EncryptEnvelopes(src, kAuthorKey);
}

// The regions a transformed text records, in writing order -- one per
// decryption envelope the transformation produced. Reading them back is how a
// test sees what the encrypting half put where an envelope's body used to be
// without any key having been applied to the text yet.
std::vector<std::string> RecordedRegions(std::string_view text) {
  std::vector<std::string> regions;
  std::string_view opening = "data_block=\"";
  size_t pos = text.find(opening);
  while (pos != std::string_view::npos) {
    size_t start = pos + opening.size();
    size_t close = text.find('"', start);
    regions.emplace_back(text.substr(start, close - start));
    pos = text.find(opening, close);
  }
  return regions;
}

// The cleartext `region` stands for under `key`, or the empty string when the
// key is not the one it was encrypted under.
std::string Recovered(const std::string& region, std::string_view key) {
  std::string cleartext;
  if (!DecryptProtectedRegion(region, key, &cleartext)) return "";
  return cleartext;
}

// Whether `region` can be recovered under `key` at all. The cleartext on its
// own cannot answer that: a region standing for no text and a value standing
// for no region both hand back nothing, and the rules tell them apart.
bool Recoverable(const std::string& region, std::string_view key) {
  std::string cleartext;
  return DecryptProtectedRegion(region, key, &cleartext);
}

// The single region an encrypted text records. Every source given to this one
// carries exactly one envelope.
std::string OneRegion(const std::string& src) {
  std::vector<std::string> regions = RecordedRegions(Encrypted(src));
  return regions.empty() ? "" : regions.front();
}

// One directive recording a region, in the syntax of §22.11.
std::string DataBlockLine(const std::string& region) {
  return "`pragma protect data_block=\"" + region + "\"\n";
}

// A decryption envelope written around one recorded region, and around
// whatever `inner` holds. The regions come out of the encrypting half, so what
// is composed here is the arrangement of the envelopes rather than any of
// their content.
std::string EnvelopeAround(const std::string& region,
                           const std::string& inner) {
  return "`pragma protect begin_protected\n" + DataBlockLine(region) + inner +
         "`pragma protect end_protected\n";
}

// ---------------------------------------------------------------------------
// Envelope encryption: an encryption envelope becomes a decryption envelope.
// ---------------------------------------------------------------------------

// The transformation the process is named for. The delimiters that opened and
// closed a region for encryption are gone, and the pair that delimits a
// protected region stands where they were.
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

// What the envelope enclosed is not written in the envelope it became: the
// region was encrypted, so its own characters are nowhere in the transformed
// text. Without this the first test would pass on a transformation that only
// renamed the delimiters.
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

// The closest input the process has to leave alone: a source text holding no
// encryption envelope has nothing to recognize, so it comes back as the text
// that went in, character for character.
TEST(ProtectedEnvelopeProcessing, TextWithNoEnvelopeIsReturnedUnchanged) {
  std::string src =
      "module m;\n"
      "  initial result = 1;\n"
      "endmodule\n";
  EXPECT_EQ(Encrypted(src), src);
  EXPECT_TRUE(RecordedRegions(Encrypted(src)).empty());
}

// An opening expression the source never closed delimits no region, so there
// is no envelope to recognize and the text it gathered stays text.
TEST(ProtectedEnvelopeProcessing, UnclosedRegionIsNotTransformed) {
  std::string transformed = Encrypted(
      "`pragma protect begin\n"
      "  initial result = 42;\n");
  EXPECT_TRUE(Holds(transformed, "initial result = 42;"));
  EXPECT_TRUE(RecordedRegions(transformed).empty());
}

// A decryption envelope is what this process produces, not what it consumes:
// one already written in the source text is not an encryption envelope, so the
// text it delimits is carried across untouched.
TEST(ProtectedEnvelopeProcessing, DecryptionEnvelopeIsNotEncryptedAgain) {
  std::string src =
      "`pragma protect begin_protected\n"
      "  initial result = 42;\n"
      "`pragma protect end_protected\n";
  EXPECT_EQ(Encrypted(src), src);
}

// Each envelope of the source text is recognized, so two of them leave two
// decryption envelopes behind rather than one covering everything between the
// outermost delimiters.
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
  // The text between the two envelopes was never inside either of them.
  EXPECT_TRUE(Holds(transformed, "initial between = 2;"));
}

// The smallest region there is. Delimiters written next to each other enclose
// no text, and that is still a region for the process to recognize: the
// envelope is transformed, and what it records recovers as the nothing it
// stood for. The two claims are separated because a recovery that failed would
// also hand back nothing, and only one of the two is the rule.
TEST(ProtectedEnvelopeProcessing, AnEmptyRegionIsStillAnEnvelope) {
  std::vector<std::string> regions =
      RecordedRegions(Encrypted("`pragma protect begin\n"
                                "`pragma protect end\n"));
  ASSERT_EQ(regions.size(), 1U);
  EXPECT_FALSE(regions.front().empty());
  EXPECT_TRUE(Recoverable(regions.front(), kAuthorKey));
  EXPECT_EQ(Recovered(regions.front(), kAuthorKey), "");
}

// The same region read back through the preprocessor. An envelope standing for
// no text puts none back, and the lines it was written between are still there
// on either side of it, so contributing nothing is not the same as consuming
// what surrounds it.
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

// The delimiter is a pragma expression rather than a whole directive, so a
// directive that describes the envelope and opens it in one line -- the form
// the standard's own example is written in -- opens the same region.
TEST(ProtectedEnvelopeProcessing, DelimiterBesideOtherExpressionsIsRecognized) {
  std::string transformed = Encrypted(
      "`pragma protect data_method=\"x-caesar\", key_keyname=\"rot13\", begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n");
  ASSERT_EQ(RecordedRegions(transformed).size(), 1U);
  EXPECT_EQ(Recovered(RecordedRegions(transformed)[0], kAuthorKey),
            "  initial result = 42;\n");
}

// ---------------------------------------------------------------------------
// Envelope encryption interprets protect pragma directives and nothing else.
// ---------------------------------------------------------------------------

// A macro definition and a use of it inside a region are text, not a pragma
// directive, so the process neither defines the macro nor substitutes it: what
// the region records is the two lines as they were written.
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

// The same for a directive that would have to reach outside the text to be
// acted on. Naming a file that does not exist is safe precisely because the
// line is never read as a request for a file.
TEST(ProtectedEnvelopeProcessing, IncludeInsideARegionIsNotResolved) {
  std::string transformed = Encrypted(
      "`pragma protect begin\n"
      "`include \"no_such_file_anywhere.svh\"\n"
      "`pragma protect end\n");
  ASSERT_EQ(RecordedRegions(transformed).size(), 1U);
  EXPECT_EQ(Recovered(RecordedRegions(transformed)[0], kAuthorKey),
            "`include \"no_such_file_anywhere.svh\"\n");
}

// A directive belonging to some other pragma is not part of a protect pragma
// directive either, so it is content of the region like any other line.
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

// Text the process is given no way to read is still text it carries: a region
// that is not SystemVerilog at all comes back exactly as it went in, so
// nothing about it had to parse for the region to be protected.
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

// Outside every envelope the rule is the same. A macro definition written
// where no region is open stands in the transformed text as it was written,
// rather than being consumed the way the preprocessor proper would consume it.
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

// The negative form of the one thing the process does interpret. A delimiter
// spelled against another pragma_name is not part of a protect pragma
// directive, so it delimits nothing and the text stays whole.
TEST(ProtectedEnvelopeProcessing, DelimiterUnderAnotherPragmaNameDelimitsNone) {
  std::string src =
      "`pragma acme_tool begin\n"
      "  initial result = 42;\n"
      "`pragma acme_tool end\n";
  EXPECT_EQ(Encrypted(src), src);
  EXPECT_TRUE(RecordedRegions(Encrypted(src)).empty());
}

// ---------------------------------------------------------------------------
// Envelope decryption: a decryption envelope becomes the cleartext it stands
// for, for the compilation step that follows.
// ---------------------------------------------------------------------------

// The round trip, read at the point where the compilation step reads it: the
// region's own text is back in the text the preprocessor produced, and the
// envelope that carried it is not.
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

// The cleartext is the region, not an approximation of it: a body of several
// lines comes back with all of them, in order, so nothing was dropped or
// reordered on the way through the envelope.
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

// Every decryption envelope of the text is processed, not merely the first one
// met. Nothing in a text carrying one envelope can tell those two readings
// apart, which is why this one carries two.
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

// An envelope written inside another one is contained in the source text too,
// so it is processed as well. The regions come out of the encrypting half; how
// they are arranged is what this input varies.
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

// One envelope may record more than one region, and each of them stands for
// cleartext the step after this one has to read. Both come back, and they come
// back in the order they were written rather than in either one's own order.
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

// The other position the same two regions can be written in. A run of
// expressions means the same thing however it is spread over directives, so
// two regions recorded on one directive are put back exactly as two directives
// would have put them.
TEST(ProtectedEnvelopeProcessing, TwoRegionsOnOneDirectiveArePutBack) {
  std::string first = OneRegion(
      "`pragma protect begin\n"
      "  initial first = 1;\n"
      "`pragma protect end\n");
  std::string second = OneRegion(
      "`pragma protect begin\n"
      "  initial second = 2;\n"
      "`pragma protect end\n");
  ReadWithKey run(
      "`pragma protect begin_protected\n"
      "`pragma protect data_block=\"" +
          first + "\", data_block=\"" + second +
          "\"\n`pragma protect end_protected\n",
      kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, "initial first = 1;"));
  EXPECT_TRUE(Holds(run.text, "initial second = 2;"));
  EXPECT_LT(run.text.find("initial first = 1;"),
            run.text.find("initial second = 2;"));
}

// The key is what makes the process possible, so a key that is not the one the
// region was encrypted under recovers nothing. Reporting it is what keeps the
// design that did not arrive from reading as a design that was empty.
TEST(ProtectedEnvelopeProcessing, AKeyThatIsNotTheProperOneRecoversNothing) {
  std::string sealed = Encrypted(
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n");
  ReadWithKey run(sealed, kStrangerKey);
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma data block cannot be decrypted with the key supplied",
      LineHolding(sealed, "data_block="), "34.3.2"));
  EXPECT_FALSE(Holds(run.text, "initial result = 42;"));
}

// The same where the user supplied no key at all, which is the state a tool
// reading protected source starts in.
TEST(ProtectedEnvelopeProcessing, NoKeySuppliedRecoversNothing) {
  std::string sealed = Encrypted(
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n");
  ReadWithKey run(sealed, "");
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma data block cannot be decrypted with the key supplied",
      LineHolding(sealed, "data_block="), "34.3.2"));
  EXPECT_FALSE(Holds(run.text, "initial result = 42;"));
}

// A decryption envelope enclosing no recorded region stands for no cleartext,
// so there is nothing to put back and nothing to report. This is the envelope
// the delimiters alone describe, and it leaves the text it encloses to the
// compilation step exactly as §34.2 leaves it.
TEST(ProtectedEnvelopeProcessing, AnEnvelopeRecordingNoRegionPassesQuietly) {
  ReadWithKey run(
      "`pragma protect begin_protected\n"
      "  initial result = 42;\n"
      "`pragma protect end_protected\n",
      kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, "initial result = 42;"));
}

// A recorded region is only a region of a decryption envelope. The same
// expression written where no such envelope is open records nothing this
// process is asked to put back, so it recovers nothing and reports nothing.
TEST(ProtectedEnvelopeProcessing, ARegionOutsideAnEnvelopeIsNotRecovered) {
  std::string region = OneRegion(
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n");
  ReadWithKey run("`pragma protect data_block=\"" + region + "\"\n",
                  kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(Holds(run.text, "initial result = 42;"));
}

// ---------------------------------------------------------------------------
// Values that record no region at all. The key is not what is wrong with any
// of these, so each one has to be turned away on its own account rather than
// on the key's.
// ---------------------------------------------------------------------------

// An encrypted region is written in one alphabet. A value carrying a character
// outside it was never produced by encrypting anything, so no key opens it and
// the condition is reported instead of a stretch of arbitrary bytes being
// handed to the compilation step as though it were design text.
TEST(ProtectedEnvelopeProcessing, AValueOutsideTheAlphabetRecordsNoRegion) {
  EXPECT_FALSE(Recoverable("AAAA*AAA", kAuthorKey));
  ReadWithKey run(EnvelopeAround("AAAA*AAA", ""), kAuthorKey);
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma value is not written in the encoding in effect", 2,
      "34.5.9.2"));
}

// The alphabet writes bytes in groups, and the shortest group that carries a
// whole byte is two characters. A value whose last group is a single character
// stops part way through a byte, so it records no region either -- and this is
// the closest such value to a well-formed one, differing from it by a single
// character of length.
TEST(ProtectedEnvelopeProcessing, AValueEndingMidGroupRecordsNoRegion) {
  EXPECT_FALSE(Recoverable("AAAAA", kAuthorKey));
  ReadWithKey run(EnvelopeAround("AAAAA", ""), kAuthorKey);
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma value is not written in the encoding in effect", 2,
      "34.5.9.2"));
}

// A region carries a fingerprint of its own text ahead of the text, so a value
// decoding to fewer bytes than that fingerprint occupies records no region
// however well formed its spelling is. Without this the shortest values would
// be read as a region whose fingerprint ran off the end of what was there.
TEST(ProtectedEnvelopeProcessing, AValueShorterThanAFingerprintRecordsNone) {
  EXPECT_FALSE(Recoverable("AAA", kAuthorKey));
  // The spelling is one the scheme writes, so the value is read and the block
  // it stands for is what cannot be opened.
  ReadWithKey run(EnvelopeAround("AAA", ""), kAuthorKey);
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma data block cannot be decrypted with the key supplied", 2,
      "34.3.2"));
}

}  // namespace
