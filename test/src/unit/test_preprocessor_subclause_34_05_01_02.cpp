// §34.5.1.2 Description, for the protect pragma keyword that opens an
// encryption envelope. The syntax block above it settles how the expression is
// spelled; this one settles what an encrypting tool does when it reads one, and
// it settles it three times over -- once for each of the three headings the
// subclause writes its rules under.
//
// ENCRYPTION INPUT. The expression marks the point at which encryption begins,
// so what stands ahead of it is text a tool carries across and what stands from
// it on is text a tool seals. A second such expression written while a region
// is still open is an error: two points at which encryption begins, with no
// point in between at which it ended, ask for a block inside a block. The one
// thing the subclause does allow inside an open region is a previously
// generated begin_protected-end_protected block, and it is allowed on terms
// that make it no nesting at all -- those lines are a byte stream, encrypted
// along with everything else the region holds rather than read as the
// description of anything.
//
// ENCRYPTION OUTPUT. The expression is replaced by §34.5.3's, and everything
// the produced envelope has to state about itself is written between that
// expression and §34.5.4's, the blocks of §34.5.15 and §34.5.27 among it. Every
// character standing between the opening expression and the closing one that
// answers it -- comments and further protect pragmas included, unless some
// other subclause has claimed one -- is encrypted and recorded on §34.5.15's
// expression. The arbitrary comment text the subclause permits a tool to pad
// the input with is a permission rather than an obligation, and this
// implementation adds none.
//
// DECRYPTION INPUT: none. The expression asks for nothing on that side, so a
// text carrying one is decrypted exactly as the same text without it would be.
//
// All of it is preprocessor-stage. src/preprocessor/protect_processing.cpp
// reads a source text for the point each region begins at and reports a region
// opened inside an open one, and src/preprocessor/protect_envelope_output.cpp
// writes the envelope that stands where a region was. The inputs here are
// written as the real directive syntax of §22.5.1 and driven through those two
// halves and through the preprocessor that reads what they produce, so every
// region is delimited, described and sealed the way a source text would have
// delimited, described and sealed it.

#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_protect_keys.h"
#include "helpers_reported_error.h"
#include "helpers_text_lines.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_keywords.h"
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
// looks for, and it is the stricter thing to find missing from an output.
constexpr std::string_view kSealedStatement = "initial result = 42;";

// The entity that provided the key a region's own keys travel under, and one of
// its keys, for the arrangement §34.5.27 writes a key block for. The names are
// nothing to this subclause; what they are here for is producing an envelope
// that carries such a block, so that where the block is written can be read off
// it.
constexpr std::string_view kKeyProvider = "aegis-custody";
constexpr std::string_view kKeyProviderKeyName = "wrapping-2026";
constexpr std::string_view kKeyProviderKey = "aegis-custody-wrapping-key";

// A second such entity, for the region designating two of them. §34.5.27 makes
// two designations two ways into one envelope rather than one designation
// restated, so a region writing both has asked for two blocks and each of them
// has to land where this subclause says a block is found.
constexpr std::string_view kSecondProvider = "borealis-trust";
constexpr std::string_view kSecondProviderKeyName = "wrapping-2027";
constexpr std::string_view kSecondProviderKey = "borealis-trust-wrapping-key";
// One protect pragma expression with a value written against it, as a directive
// of its own.
std::string Writes(std::string_view keyword, std::string_view value) {
  std::string text = "`pragma protect ";
  text.append(keyword).append("=\"").append(value).append("\"\n");
  return text;
}

// One encryption envelope, delimited by the expression this subclause defines
// and the one §34.5.2 defines, with `described` and then `body` between them.
std::string Region(std::string_view described, std::string_view body) {
  std::string text = "`pragma protect begin\n";
  text.append(described).append(body);
  text.append("`pragma protect end\n");
  return text;
}

// The characters a written envelope records its region on. §34.5.15 carries
// them as a quoted pragma_value, so the block is what stands between the
// quotes, and two regions differing in a single character of their text leave
// two different runs of them.
std::string DataBlockOf(const std::string& written) {
  constexpr std::string_view kOpening = "`pragma protect data_block=\"";
  size_t at = written.find(kOpening);
  if (at == std::string::npos) return {};
  size_t start = at + kOpening.size();
  size_t end = written.find('"', start);
  if (end == std::string::npos) return {};
  return written.substr(start, end - start);
}

// Envelope encryption over a source text under the author's key.
std::string Encrypted(const std::string& src) {
  return EncryptEnvelopes(src, kAuthorKey);
}

// The same, with the reports the reading made about the input kept beside the
// text it produced. The transformation runs to the end of the input whatever it
// found, so the two are read together rather than one in place of the other.
//
// The source is added to the manager so that a report stands at the line of it
// that carries the breach, which is what the cases below name.
struct EncryptionRun {
  SourceManager mgr;
  DiagEngine diag{mgr};
  std::string text;

  explicit EncryptionRun(const std::string& src)
      : text(EncryptEnvelopes(src, kAuthorKey, ProtectKeyList(), &diag,
                              mgr.AddFile("<test>", src))) {}
};

// A source text read through the whole preprocessor, with what the reading left
// behind kept beside it. `key` is the one a user supplies for reading protected
// regions back; a test reading a produced envelope needs the key it was formed
// under, or the region would stay sealed and its absence from the output would
// say nothing.
struct ReadSource {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp;
  std::string text;

  ReadSource(const std::string& src, std::string_view key)
      : pp(mgr, diag, KeyConfig(key)) {
    text = pp.Preprocess(mgr.AddFile("<test>", src));
  }

  static PreprocConfig KeyConfig(std::string_view key) {
    PreprocConfig config;
    config.protect_key = std::string(key);
    return config;
  }
};

// ---------------------------------------------------------------------------
// ENCRYPTION INPUT: the point at which encryption begins.
// ---------------------------------------------------------------------------

// The rule at its plainest, read from both sides of the point it marks. The
// design written ahead of the expression is text an encrypting tool carries
// across and the design written after it is text that tool seals, so the one
// line between them is what decided the fate of each.
TEST(ProtectBeginEncryptionInput, TheExpressionIsWhereEncryptionStarts) {
  std::string src = "module secret;\n  int cleartext = 1;\n";
  src += Region("", kSealedDesign);
  EncryptionRun run(src);
  EXPECT_TRUE(Holds(run.text, "int cleartext = 1;"));
  EXPECT_FALSE(Holds(run.text, kSealedStatement));
}

// The same point marked from the other syntactic position §22.5.1 allows the
// expression: last in a list whose earlier expressions describe the envelope.
// The list is one run of expressions however it is spread over directives, so
// encryption begins where the word stands rather than where its directive does,
// and the design written on the line ahead of it stays in the clear.
TEST(ProtectBeginEncryptionInput, AListedExpressionMarksThePointToo) {
  EncryptionRun run(
      "  int cleartext = 1;\n"
      "`pragma protect author=\"Acme Corp\", begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n");
  EXPECT_TRUE(Holds(run.text, "int cleartext = 1;"));
  EXPECT_FALSE(Holds(run.text, kSealedStatement));
}

// The closest input the rule has to turn away: the same text with no opening
// expression in it at all. Nothing then says where encryption begins, so there
// is no region to seal and the text comes back character for character --
// including the closing expression, which delimits nothing on its own.
TEST(ProtectBeginEncryptionInput, WithNoOpeningExpressionNothingIsSealed) {
  std::string src = "  initial result = 42;\n`pragma protect end\n";
  EXPECT_EQ(Encrypted(src), src);
}

// Each expression marks a point of its own rather than one of them putting a
// whole text under encryption. A text carrying a single region cannot tell
// those two readings apart, which is why this one carries two with cleartext
// between them.
TEST(ProtectBeginEncryptionInput, EachExpressionMarksItsOwnPoint) {
  std::string src = Region("", "  initial first = 1;\n");
  src += "  int between = 3;\n";
  src += Region("", "  initial second = 2;\n");
  EncryptionRun run(src);
  EXPECT_FALSE(Holds(run.text, "initial first = 1;"));
  EXPECT_FALSE(Holds(run.text, "initial second = 2;"));
  EXPECT_TRUE(Holds(run.text, "int between = 3;"));
}

// ---------------------------------------------------------------------------
// ENCRYPTION INPUT: a region opened inside an open region.
// ---------------------------------------------------------------------------

// The condition the subclause makes an error: a second point at which
// encryption begins, written where the region the first one opened has not been
// closed. There is no block for a block to go inside of, so the input is
// reported.
TEST(ProtectBeginEncryptionInput, ARegionOpenedInsideAnOpenRegionIsReported) {
  EncryptionRun run(
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect begin\n"
      "  initial other = 7;\n"
      "`pragma protect end\n");
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(),
                            "opens a region inside a begin-end block", 3,
                            "34.5.1"));
}

// What the condition costs is the report rather than the transformation. The
// rest of the input is ordinary source text, so the reading runs to the end of
// it and the region opened first is sealed as it would have been.
TEST(ProtectBeginEncryptionInput, TheReportedInputIsStillTransformed) {
  EncryptionRun run(
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect begin\n"
      "  initial other = 7;\n"
      "`pragma protect end\n");
  EXPECT_TRUE(Holds(run.text, "`pragma protect begin_protected\n"));
  EXPECT_FALSE(Holds(run.text, kSealedStatement));
  EXPECT_FALSE(Holds(run.text, "initial other = 7;"));
}

// Where the closing expression leaves the reading, which is what makes the
// second opening expression text of the first region rather than the opening of
// a second. The closing expression written first is the one answering the
// opening expression written first, so the design after it is in the clear
// while the design between them is not.
TEST(ProtectBeginEncryptionInput, TheFirstClosingExpressionAnswersTheOpening) {
  EncryptionRun run(
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect begin\n"
      "`pragma protect end\n"
      "  int after = 3;\n");
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(),
                            "opens a region inside a begin-end block", 3,
                            "34.5.1"));
  EXPECT_FALSE(Holds(run.text, kSealedStatement));
  EXPECT_TRUE(Holds(run.text, "int after = 3;"));
}

// The closest accepting neighbor of the reported input, and the one an author
// sealing two models writes: the same two opening expressions with a closing
// expression between them. Neither region is inside the other, so nothing is
// reported and each is sealed into an envelope of its own.
//
// This is also what the reported inputs above are read against. A report set
// for every region a text holds would look exactly like one set for the nested
// region alone, so an accepting input has to be shown reporting nothing -- and
// showing it over regions that really were sealed is what keeps the silence
// from being the silence of a reading that did nothing.
TEST(ProtectBeginEncryptionInput, RegionsWrittenOneAfterAnotherAreNoNesting) {
  std::string src = Region("", "  initial first = 1;\n");
  src += Region("", "  initial second = 2;\n");
  EncryptionRun run(src);
  EXPECT_EQ(run.diag.ErrorCount(), 0U);
  EXPECT_EQ(TimesWritten(run.text, "`pragma protect begin_protected"), 2U);
}

// The reserved word written inside the region in the spelling §34.5.1.1 does
// not define it with. The expression opening a region is the word standing
// alone, so a word carrying a pragma_value opens nothing and there is no second
// region for the first to contain.
TEST(ProtectBeginEncryptionInput, AValuedWordInsideTheRegionIsNoNesting) {
  EncryptionRun run(
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect begin=\"again\"\n"
      "`pragma protect end\n");
  EXPECT_EQ(run.diag.ErrorCount(), 0U);
}

// The other syntactic position the second opening expression can be written in:
// among a list, rather than as the whole of its directive. A list means the
// same thing however it is spread over directives, so an opening expression
// standing in one opens a region as much as one standing alone, and one written
// where a region is still open is the same error.
TEST(ProtectBeginEncryptionInput, ANestedExpressionInAListIsReportedToo) {
  EncryptionRun run(
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect author=\"Acme Corp\", begin\n"
      "`pragma protect end\n");
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(),
                            "opens a region inside a begin-end block", 3,
                            "34.5.1"));
}

// The condition belongs to the text rather than to the keys a tool was handed.
// An author who ran the encrypting half without supplying one gave it the same
// nested input, so a run with somewhere to report to reports it on the same
// terms. The text comes back exactly as it was written -- there being nothing
// any region could be encrypted under -- which is what tells this apart from a
// reading that reported the error by refusing to do its work.
TEST(ProtectBeginEncryptionInput, ANestedRegionIsReportedWithNoKeyToo) {
  std::string src =
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect begin\n"
      "`pragma protect end\n";
  SourceManager mgr;
  DiagEngine diag(mgr);
  EXPECT_EQ(EncryptEnvelopes(src, "", ProtectKeyList(), &diag,
                             mgr.AddFile("<test>", src)),
            src);
  EXPECT_TRUE(ReportedError(diag.Diagnostics(),
                            "opens a region inside a begin-end block", 3,
                            "34.5.1"));
}

// ---------------------------------------------------------------------------
// ENCRYPTION INPUT: previously encrypted content inside the region.
// ---------------------------------------------------------------------------

// The arrangement the subclause permits, built from what §34.5.3 and §34.5.4
// really delimit rather than from a hand-written imitation of it: a model this
// tool sealed already, written inside a region this tool is about to seal. The
// block is content of the larger region, so the envelope it was is gone from
// the output and the only envelope written there is the outer one.
TEST(ProtectBeginEncryptionInput, APreviouslyProtectedBlockInsideIsSealed) {
  std::string inner = Encrypted(Region("", "  initial inner = 2;\n"));
  EncryptionRun run(Region("", inner));
  EXPECT_TRUE(Holds(inner, "`pragma protect begin_protected"));
  EXPECT_FALSE(Holds(run.text, inner));
  EXPECT_EQ(TimesWritten(run.text, "`pragma protect begin_protected"), 1U);
}

// The same arrangement read against the rule above it: an opening expression
// standing inside such a block is not a region opened inside an open region.
// §34.5.3 leaves the expressions of those lines uninterpreted, so the word
// there opens nothing and the block travels into the larger region whole.
TEST(ProtectBeginEncryptionInput, AWordInsideThatBlockIsNoNesting) {
  EncryptionRun run(
      "`pragma protect begin\n"
      "`pragma protect begin_protected\n"
      "`pragma protect begin\n"
      "`pragma protect end_protected\n"
      "`pragma protect end\n");
  EXPECT_EQ(run.diag.ErrorCount(), 0U);
}

// Previously encrypted content may itself hold previously encrypted content, so
// one of these blocks stands inside another as readily as it stands inside a
// region. What ends a block is then the closing expression answering its own
// opening rather than the first one met, and the opening expression written
// after the inner block closes is what says which reading was taken: still
// inside the outer block, it opens nothing and is no error. A reading that had
// let the inner block's closing expression end the outer one would have found
// that word standing in the open and reported it.
TEST(ProtectBeginEncryptionInput, TheBlockClosingMatchesItsOwnOpening) {
  std::string sealed = Encrypted(Region("", "  initial inner = 2;\n"));
  std::string enclosing = "`pragma protect begin_protected\n";
  enclosing += sealed;
  enclosing += "`pragma protect begin\n";
  enclosing += "`pragma protect end_protected\n";
  EncryptionRun run(Region("", enclosing));
  EXPECT_EQ(run.diag.ErrorCount(), 0U);
  EXPECT_FALSE(Holds(run.text, sealed));
}

// What treating those lines as a byte stream rules out. The block's own
// description of itself names a cipher this tool never used and carries
// characters no reading here produced, and neither reaches the output: the
// lines were encrypted as text rather than read as the description of the
// envelope being written.
TEST(ProtectBeginEncryptionInput, ThatBlocksDescriptionDescribesNothing) {
  std::string inner = "`pragma protect begin_protected\n";
  inner += Writes("data_method", "acme-cipher");
  inner += Writes("data_block", "NOTABLOCKOFTHISTOOLS");
  inner += "`pragma protect end_protected\n";
  EncryptionRun run(Region("", inner));
  EXPECT_FALSE(Holds(run.text, "acme-cipher"));
  EXPECT_FALSE(Holds(run.text, "NOTABLOCKOFTHISTOOLS"));
}

// The permission is for blocks rather than for a block, so two sealed models
// stand inside one region as readily as one does. Both come back when the outer
// envelope is read, which is what says each of them survived the encryption
// enclosing it rather than merely disappearing from the output.
TEST(ProtectBeginEncryptionInput, TwoSuchBlocksInsideOneRegionBothSurvive) {
  std::string first = Encrypted(Region("", "  initial first = 1;\n"));
  std::string second = Encrypted(Region("", "  initial second = 2;\n"));
  EncryptionRun run(Region("", first + second));
  ReadSource read(run.text, kAuthorKey);
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_TRUE(Holds(read.text, "initial first = 1;"));
  EXPECT_TRUE(Holds(read.text, "initial second = 2;"));
}

// The negative form of the permission: the identical block with no region
// enclosing it. Nothing marked a point at which encryption begins, so there is
// no larger region for the block to be content of and the text stands as it was
// written.
TEST(ProtectBeginEncryptionInput, TheSameBlockOutsideEveryRegionIsLeftAlone) {
  std::string inner = Encrypted(Region("", "  initial inner = 2;\n"));
  EncryptionRun run(inner);
  EXPECT_EQ(run.text, inner);
}

// ---------------------------------------------------------------------------
// ENCRYPTION OUTPUT: the expression the opening expression is replaced by.
// ---------------------------------------------------------------------------

// The replacement, read in both directions: the word §34.5.3 defines stands in
// the output stream and the word this subclause defines does not. Checking only
// that the first appeared would pass on an output carrying both.
TEST(ProtectBeginEncryptionOutput, TheOpeningExpressionIsReplaced) {
  EncryptionRun run(Region("", kSealedDesign));
  EXPECT_TRUE(Holds(run.text, "`pragma protect begin_protected\n"));
  EXPECT_FALSE(Holds(run.text, "`pragma protect begin\n"));
}

// It is the expression that is replaced rather than the directive carrying it.
// The expressions written beside it described the region and go on describing
// the envelope standing in its place, so the one thing changed on that line is
// the word naming the delimiter.
TEST(ProtectBeginEncryptionOutput, OnlyTheDelimitingWordChangesOnItsLine) {
  EncryptionRun run(
      "`pragma protect author=\"Acme Corp\", begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n");
  constexpr std::string_view kTransformed =
      "`pragma protect author=\"Acme Corp\", begin_protected\n";
  EXPECT_TRUE(Holds(run.text, kTransformed));
}

// The other side of the same line. An expression written after the delimiter
// belongs to the list the delimiter belongs to, so it is carried onto the
// produced directive on the side it was written on, and the replacement reaches
// only the word between the two.
TEST(ProtectBeginEncryptionOutput, ExpressionsAfterTheDelimiterAreCarried) {
  EncryptionRun run(
      "`pragma protect begin, comment=\"the region below\"\n"
      "  initial result = 42;\n"
      "`pragma protect end\n");
  constexpr std::string_view kTransformed =
      "`pragma protect begin_protected, comment=\"the region below\"\n";
  EXPECT_TRUE(Holds(run.text, kTransformed));
}

// The one thing written after the delimiter that is not carried across, and the
// reason the two are told apart: a comment is not a pragma expression and
// states nothing about the envelope. Carrying one would also put whatever the
// produced directive goes on to say inside it, so the replacement leaves the
// comment where the source wrote it rather than copying it onto the envelope.
TEST(ProtectBeginEncryptionOutput, ACommentAfterTheDelimiterIsNotCarried) {
  EncryptionRun run(
      "`pragma protect begin // the region starts here\n"
      "  initial result = 42;\n"
      "`pragma protect end\n");
  EXPECT_TRUE(Holds(run.text, "`pragma protect begin_protected\n"));
  EXPECT_FALSE(Holds(run.text, "the region starts here"));
}

// The closest input that gets no replacement: the same region with no key to be
// sealed under. There is nothing for an envelope to record, so no envelope is
// written and the expression stands in the output as the author wrote it.
TEST(ProtectBeginEncryptionOutput, WithNoKeyTheExpressionStandsAsWritten) {
  std::string src = Region("", kSealedDesign);
  EXPECT_EQ(EncryptEnvelopes(src, ""), src);
}

// ---------------------------------------------------------------------------
// ENCRYPTION OUTPUT: what is generated between the two delimiters.
// ---------------------------------------------------------------------------

// Everything the produced envelope has to state about itself is generated after
// the expression replacing this one and before the expression closing it. Each
// is looked for by position rather than by presence, because an expression
// written outside the pair would be found by a search of the whole text just as
// readily as one written inside it.
TEST(ProtectBeginEncryptionOutput, TheRequiredExpressionsPrecedeTheClosing) {
  EncryptionRun run(Region("", kSealedDesign));
  size_t opening = run.text.find("`pragma protect begin_protected");
  size_t closing = run.text.find("`pragma protect end_protected");
  size_t agent = run.text.find("`pragma protect encrypt_agent=");
  size_t method = run.text.find("`pragma protect data_method=");
  size_t encoding = run.text.find("`pragma protect encoding=");
  ASSERT_NE(opening, std::string::npos);
  ASSERT_NE(closing, std::string::npos);
  EXPECT_LT(opening, agent);
  EXPECT_LT(agent, closing);
  EXPECT_LT(opening, method);
  EXPECT_LT(method, closing);
  EXPECT_LT(opening, encoding);
  EXPECT_LT(encoding, closing);
}

// The half the test above cannot reach. Searching for where an expression first
// stands says nothing about a second copy of it written past the closing
// expression, and a reader that has left the envelope is a reader those
// expressions no longer describe anything for. Nothing required as encryption
// output is written after the envelope closes; §34.4's expression putting the
// keywords back to their defaults is what does follow, and it is required of
// the text around the envelope rather than of the envelope.
TEST(ProtectBeginEncryptionOutput, NothingRequiredAsOutputFollowsTheClose) {
  EncryptionRun run(Region("", kSealedDesign));
  size_t closing = run.text.find("`pragma protect end_protected");
  ASSERT_NE(closing, std::string::npos);
  std::string after = run.text.substr(closing);
  EXPECT_FALSE(Holds(after, "`pragma protect encrypt_agent="));
  EXPECT_FALSE(Holds(after, "`pragma protect data_method="));
  EXPECT_FALSE(Holds(after, "`pragma protect encoding="));
  EXPECT_FALSE(Holds(after, "`pragma protect data_block="));
  EXPECT_FALSE(Holds(after, "`pragma protect key_block"));
}

// The two expressions the subclause names outright. §34.5.15's introduces the
// encrypted data and §34.5.27's introduces the keys, and each is written where
// the subclause says one is always found: inside the pair of delimiters.
//
// The region is written under the arrangement producing a key block at all --
// it designates a key of an entity whose keys the tool holds, and names no key
// for its data -- so both blocks are there to be placed.
TEST(ProtectBeginEncryptionOutput, TheTwoBlocksStandInsideTheWrittenEnvelope) {
  ProtectKeyList keys;
  keys.Add(KeyOf(kKeyProvider, kKeyProviderKeyName, kKeyProviderKey));
  std::string described = Writes("key_keyowner", kKeyProvider);
  described += Writes("key_keyname", kKeyProviderKeyName);
  std::string written =
      EncryptEnvelopes(Region(described, kSealedDesign), "", keys);
  size_t opening = written.find("`pragma protect begin_protected");
  size_t closing = written.find("`pragma protect end_protected");
  size_t key_block = written.find("`pragma protect key_block");
  size_t data_block = written.find("`pragma protect data_block");
  ASSERT_NE(opening, std::string::npos);
  ASSERT_NE(closing, std::string::npos);
  ASSERT_NE(key_block, std::string::npos);
  ASSERT_NE(data_block, std::string::npos);
  EXPECT_LT(opening, key_block);
  EXPECT_LT(key_block, closing);
  EXPECT_LT(opening, data_block);
  EXPECT_LT(data_block, closing);
}

// The plural of the rule above. A region designating a key of each of two
// entities has asked for a block apiece, those being two ways into the one
// envelope, and the subclause says of every one of them that it is found within
// the pair of delimiters. The last of them is what the position is read from:
// with the first inside and the last inside, so is everything between.
TEST(ProtectBeginEncryptionOutput, EveryKeyBlockAskedForIsInsideTheEnvelope) {
  ProtectKeyList keys;
  keys.Add(KeyOf(kKeyProvider, kKeyProviderKeyName, kKeyProviderKey));
  keys.Add(KeyOf(kSecondProvider, kSecondProviderKeyName, kSecondProviderKey));
  std::string described = Writes("key_keyowner", kKeyProvider);
  described += Writes("key_keyname", kKeyProviderKeyName);
  described += Writes("key_keyowner", kSecondProvider);
  described += Writes("key_keyname", kSecondProviderKeyName);
  std::string written =
      EncryptEnvelopes(Region(described, kSealedDesign), "", keys);
  size_t opening = written.find("`pragma protect begin_protected");
  size_t closing = written.find("`pragma protect end_protected");
  size_t last_block = written.rfind("`pragma protect key_block");
  ASSERT_NE(opening, std::string::npos);
  ASSERT_NE(closing, std::string::npos);
  ASSERT_NE(last_block, std::string::npos);
  EXPECT_EQ(TimesWritten(written, "`pragma protect key_block"), 2U);
  EXPECT_LT(opening, last_block);
  EXPECT_LT(last_block, closing);
}

// Two models sealed apart and then met in one decryption input stream, which is
// the interaction a self-contained envelope is written to avoid. Each carries
// its own block between its own pair of delimiters, so neither depends on
// anything the other stated, and both give up their designs from the one
// stream.
TEST(ProtectBeginEncryptionOutput, TwoWrittenEnvelopesInOneStreamBothOpen) {
  std::string first = Encrypted(Region("", "  int a = 1;\n"));
  std::string second = Encrypted(Region("", "  int b = 2;\n"));
  EXPECT_EQ(TimesWritten(first, "`pragma protect data_block="), 1U);
  EXPECT_EQ(TimesWritten(second, "`pragma protect data_block="), 1U);
  ReadSource run(first + second, kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, "int a = 1;"));
  EXPECT_TRUE(Holds(run.text, "int b = 2;"));
}

// ---------------------------------------------------------------------------
// ENCRYPTION OUTPUT: what the block between the delimiters records.
// ---------------------------------------------------------------------------

// The design between the delimiters is recorded on §34.5.15's expression rather
// than merely dropped. Reading the produced envelope back under the key it was
// formed under returns the design, so the characters missing from the output
// went into the block.
TEST(ProtectBeginEncryptionOutput, TheEnclosedTextIsRecordedOnTheBlock) {
  EncryptionRun run(Region("", kSealedDesign));
  EXPECT_FALSE(Holds(run.text, kSealedStatement));
  ReadSource read(run.text, kAuthorKey);
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_TRUE(Holds(read.text, kSealedStatement));
}

// A comment is text occurring between the delimiters, so it is text the block
// records. The comparison is what says so: the same region without the comment
// leaves a different block, which no reading that had discarded the comment on
// the way could produce.
TEST(ProtectBeginEncryptionOutput, ACommentBetweenTheDelimitersIsRecorded) {
  std::string body = "  // the answer\n";
  body += kSealedDesign;
  std::string with = Encrypted(Region("", body));
  std::string without = Encrypted(Region("", kSealedDesign));
  EXPECT_FALSE(Holds(with, "// the answer"));
  EXPECT_FALSE(DataBlockOf(with).empty());
  EXPECT_NE(DataBlockOf(with), DataBlockOf(without));
}

// A further protect pragma is text occurring between the delimiters too. The
// keyword §34.5.30 defines carries a documentation string nothing interprets,
// so no other subclause has claimed it out of the block, and it is recorded
// along with the design.
TEST(ProtectBeginEncryptionOutput, AProtectPragmaBetweenThemIsRecordedToo) {
  std::string described = Writes("comment", "an uninterpreted string");
  std::string with = Encrypted(Region(described, kSealedDesign));
  std::string without = Encrypted(Region("", kSealedDesign));
  EXPECT_FALSE(Holds(with, "an uninterpreted string"));
  EXPECT_FALSE(DataBlockOf(with).empty());
  EXPECT_NE(DataBlockOf(with), DataBlockOf(without));
}

// A compiler directive of another kind, which is the third thing a region's
// lines can be. It is text occurring between the delimiters like any other, so
// it goes into the block rather than being acted on by the tool doing the
// encrypting -- and what it defines is in effect for the text after the
// envelope once a reader has put the region back, which is the whole of what
// recording it was for.
TEST(ProtectBeginEncryptionOutput, ADirectiveBetweenThemIsRecordedToo) {
  std::string src = Region("", "`define ANSWER 42\n");
  src += "  int answer = `ANSWER;\n";
  EncryptionRun run(src);
  EXPECT_FALSE(Holds(run.text, "`define ANSWER 42"));
  ReadSource read(run.text, kAuthorKey);
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_FALSE(Holds(read.text, "`ANSWER"));
  EXPECT_TRUE(Holds(read.text, "42"));
}

// ---------------------------------------------------------------------------
// DECRYPTION INPUT: none.
// ---------------------------------------------------------------------------

// The expression asks for nothing on the decryption side. A region delimited by
// it in a decryption input stream holds cleartext, so there is nothing to put
// back and the design between the delimiters reaches the step after the
// preprocessor exactly as it was written.
TEST(ProtectBeginDecryptionInput, TheExpressionDecryptsNothing) {
  ReadSource run(Region("", kSealedDesign), kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, kSealedStatement));
}

// And it changes nothing about the envelopes that do ask for something. The
// same produced envelope is read with the expression standing ahead of it and
// gives up the same design, so the expression plays no part in what a
// decryption input stream yields.
TEST(ProtectBeginDecryptionInput, AnEnvelopeAfterItYieldsTheSameDesign) {
  std::string written = Encrypted(Region("", kSealedDesign));
  ReadSource plain(written, kAuthorKey);
  ReadSource preceded("`pragma protect begin\n" + written, kAuthorKey);
  EXPECT_FALSE(preceded.diag.HasErrors());
  EXPECT_TRUE(Holds(plain.text, kSealedStatement));
  EXPECT_TRUE(Holds(preceded.text, kSealedStatement));
}

// The remaining position the expression can be written in on that side: inside
// a decryption envelope, among the expressions describing the block about to be
// opened. It describes nothing there either, so the block opens on what the
// envelope really did state and gives up the same design.
TEST(ProtectBeginDecryptionInput, TheExpressionInsideAnEnvelopeChangesNothing) {
  std::string written = Encrypted(Region("", kSealedDesign));
  size_t first_line = written.find('\n');
  ASSERT_NE(first_line, std::string::npos);
  std::string spliced = written.substr(0, first_line + 1);
  spliced += "`pragma protect begin\n";
  spliced += written.substr(first_line + 1);
  ReadSource run(spliced, kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, kSealedStatement));
}

}  // namespace
