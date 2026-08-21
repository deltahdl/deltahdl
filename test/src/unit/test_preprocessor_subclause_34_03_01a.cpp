// §34.3.1 Encryption.
//
// The subclause says what an encrypting tool owes the text it is handed:
//
//   Each encryption envelope of the source text is replaced by a decryption
//   envelope, and that envelope is formed by encrypting the source text the
//   encryption envelope enclosed, according to the expressions specifying it.
//
//   Source text no encryption envelope contains is not modified.
//
//   A decryption envelope is formed by transforming the expressions specifying
//   the encryption envelope into the expressions specifying the decryption
//   envelope and the expressions describing its content. The enclosed body is
//   encrypted under the key the author specified -- the exchange key -- and is
//   recorded in the decryption envelope on a data_block expression.
//
//   An algorithm encrypting and decrypting under one key is symmetric, and so
//   is that key; one needing a second key to decrypt is asymmetric. A tool may
//   also offer a session key: a key made for the region, recorded encrypted
//   under the exchange key on a key_block expression, with the region
//   encrypted under it and recorded on a data_block. That last is a permission
//   rather than an obligation, and this implementation encrypts under the
//   exchange key directly.
//
// All of it is preprocessor-stage. src/preprocessor/protect_processing.cpp is
// where a source text is read and the transformed text written, and the
// envelope the transformation produced is read back through the pragma handler
// in src/preprocessor/preprocessor_lines.cpp, so what an envelope specifies is
// observed through the grammar it was written in rather than as a string.
//
// Every envelope here is written as the real `pragma directive syntax of
// §22.11, and every expression beside a delimiter is one of the reserved names
// of §34.4 carrying a value of the kind §34.5 defines for it, because those
// are the expressions this rule transforms.

#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_envelope.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

// The key the IP author specifies for encryption. Everything here turns on
// whether one key serves both halves, so a second key stands beside it for
// every key that is not the author's.
constexpr std::string_view kExchangeKey = "acme-exchange-key";
constexpr std::string_view kOtherKey = "not-the-authors-key";

// Envelope encryption over a source text, under the author's exchange key.
std::string Encrypted(std::string_view src) {
  return EncryptEnvelopes(src, kExchangeKey);
}

// One envelope the author specified, in the arrangement the standard's own
// example uses: two of the reserved names of §34.4 carrying string values,
// written on the directive that opens the envelope. Several rules are read out
// of this one text, so it is written once.
constexpr std::string_view kSpecifiedEnvelope =
    "`pragma protect data_method=\"x-caesar\", "
    "data_keyname=\"rot13\", begin\n"
    "  initial result = 42;\n"
    "`pragma protect end\n";

bool Holds(std::string_view text, std::string_view needle) {
  return text.find(needle) != std::string_view::npos;
}

// The blocks a transformed text records, in writing order -- one per
// decryption envelope the transformation formed. Reading them back is how a
// test sees what was put where the enclosed text used to be, before any key
// has been applied to the text.
std::vector<std::string> RecordedBlocks(std::string_view text) {
  std::vector<std::string> blocks;
  std::string_view opening = "data_block=\"";
  size_t pos = text.find(opening);
  while (pos != std::string_view::npos) {
    size_t start = pos + opening.size();
    size_t close = text.find('"', start);
    blocks.emplace_back(text.substr(start, close - start));
    pos = text.find(opening, close);
  }
  return blocks;
}

// The cleartext `block` records under `key`, or the empty string where `key`
// is not the one it was encrypted under.
std::string Recovered(const std::string& block, std::string_view key) {
  std::string cleartext;
  if (!DecryptProtectedRegion(block, key, &cleartext)) return "";
  return cleartext;
}

// Whether `block` opens under `key` at all. The cleartext alone cannot say: a
// block recording no text and a value recording no block both hand back
// nothing.
bool Recoverable(const std::string& block, std::string_view key) {
  std::string cleartext;
  return DecryptProtectedRegion(block, key, &cleartext);
}

// The one block a transformed text records. Every source given to this carries
// exactly one envelope.
std::string OneBlock(std::string_view src) {
  std::vector<std::string> blocks = RecordedBlocks(Encrypted(src));
  return blocks.empty() ? "" : blocks.front();
}

// Reads a transformed text back through the pragma grammar, with the author's
// key supplied. What an envelope specifies is envelope state rather than
// output text, so the Preprocessor outlives the call, and the text it produced
// is kept beside it for the rules about what reaches the step after.
struct ReadBack {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp;
  std::string text;
  // The envelope the text closed. Every source read back here carries one, and
  // a text that closed none leaves this naming no expressions at all, so a
  // transformation that stopped producing envelopes fails rather than reads
  // off the end of the list.
  ProtectedEnvelope envelope{};

  explicit ReadBack(const std::string& src) : pp(mgr, diag, KeyConfig()) {
    text = pp.Preprocess(mgr.AddFile("<test>", src));
    if (!pp.ProtectEnvelopes().ClosedEnvelopes().empty()) {
      envelope = pp.ProtectEnvelopes().ClosedEnvelopes().front();
    }
  }

  static PreprocConfig KeyConfig() {
    PreprocConfig config;
    config.protect_key = kExchangeKey;
    return config;
  }
};

// Whether `keywords` names `keyword`. The expressions specifying an envelope
// and the ones describing its content are each read off the envelope as a
// list, and what these tests ask of a list is which names it holds.
bool Names(const std::vector<std::string>& keywords, std::string_view keyword) {
  for (const std::string& name : keywords) {
    if (name == keyword) return true;
  }
  return false;
}

// ---------------------------------------------------------------------------
// The expressions specifying the encryption envelope become the expressions
// specifying the decryption envelope.
// ---------------------------------------------------------------------------

// The transformation the subclause describes, read as text. The expressions
// the author wrote beside the opening delimiter are still written beside it,
// and the delimiter itself is the one that opens an envelope for the other
// mode of processing. Without this the author's specification would be dropped
// on the way and the envelope produced would describe nothing.
TEST(EnvelopeEncryption, SpecifyingExpressionsAreCarriedOntoTheNewEnvelope) {
  std::string opening =
      "`pragma protect data_method=\"x-caesar\", "
      "data_keyname=\"rot13\", begin_protected\n";
  std::string written = Encrypted(kSpecifiedEnvelope);
  EXPECT_TRUE(Holds(written, opening));
  EXPECT_FALSE(Holds(written, "begin\n"));
}

// The same envelope read back through the grammar it was written in. §34.2
// designates an expression standing ahead of the opening delimiter as one that
// specifies the envelope, so the names the author asked for come off the
// envelope as its own rather than as anything else the text happens to hold.
TEST(EnvelopeEncryption, CarriedExpressionsSpecifyTheDecryptionEnvelope) {
  ReadBack run(Encrypted(kSpecifiedEnvelope));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Names(run.envelope.envelope_keywords, "data_method"));
  EXPECT_TRUE(Names(run.envelope.envelope_keywords, "data_keyname"));
}

// The other half of the same transformation. The expressions describing how
// the region was encrypted, and the one recording it, are written inside the
// envelope, so they are its content expressions rather than expressions
// specifying it -- which is what puts each of them in effect at the point the
// block depending on it is read.
TEST(EnvelopeEncryption, TheRecordedBlockIsAContentExpressionOfTheEnvelope) {
  std::string src =
      "`pragma protect data_method=\"x-caesar\", begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n";
  ReadBack run(Encrypted(src));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Names(run.envelope.content_keywords, "data_block"));
  EXPECT_FALSE(Names(run.envelope.envelope_keywords, "data_block"));
}

// Each envelope is formed from the expressions specifying it, not from
// whatever the text happens to say elsewhere. Two envelopes specified
// differently keep their own specifications, which a text carrying one
// envelope could not tell apart from one specification covering everything.
TEST(EnvelopeEncryption, EachEnvelopeKeepsTheExpressionsThatSpecifiedIt) {
  std::string written = Encrypted(
      "`pragma protect author=\"Acme Corp\", begin\n"
      "  initial first = 1;\n"
      "`pragma protect end\n"
      "`pragma protect author_info=\"second team\", begin\n"
      "  initial second = 2;\n"
      "`pragma protect end\n");
  std::string first_opening =
      "`pragma protect author=\"Acme Corp\", begin_protected\n";
  std::string second_opening =
      "`pragma protect author_info=\"second team\", begin_protected\n";
  EXPECT_TRUE(Holds(written, first_opening));
  EXPECT_TRUE(Holds(written, second_opening));
  EXPECT_FALSE(Holds(written, "author=\"Acme Corp\", author_info="));
}

// The closing delimiter is transformed the same way, and an expression written
// beside it was inside the region, so it stays inside the region the new
// envelope delimits: it is written between the block and the closing
// delimiter, where §34.2 designates it a content expression.
TEST(EnvelopeEncryption, AnExpressionBesideTheClosingDelimiterStaysInside) {
  std::string src =
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect comment=\"end of the region\", end\n";
  ReadBack run(Encrypted(src));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Names(run.envelope.content_keywords, "comment"));
  EXPECT_FALSE(Names(run.envelope.envelope_keywords, "comment"));
}

// The other position a specifying expression can be written in: a directive of
// its own, standing ahead of the one that opens the envelope. Nothing encloses
// it, so it is left exactly where it was rather than gathered onto the opening
// directive -- and leaving it there is what keeps it specifying the envelope,
// because the reading that follows still reaches it before the delimiter.
TEST(EnvelopeEncryption, AnExpressionOnItsOwnDirectiveStillSpecifies) {
  std::string src =
      "`pragma protect author=\"Acme Corp\"\n"
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n";
  ReadBack run(Encrypted(src));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Names(run.envelope.envelope_keywords, "author"));
}

// What encrypting according to the specified expressions comes to when two
// writings of one name meet. The author asked for an algorithm beside the
// delimiter, and the envelope states the one it was really encrypted with on
// an expression written with the block. Both are read, and each governs where
// it stands: the author's specifies the envelope, and the one beside the block
// is in effect where the block is, so the block is read under the description
// it was made under rather than the one it was asked for.
//
// The design arriving is what shows which of the two governed: a block read
// under the algorithm the author asked for is a block nothing opens. What
// stands in effect where the reading stops shows nothing either way, because
// §34.4 has a reset follow the envelope and §34.5.31.2 has that reset put every
// protect pragma keyword back to its default -- the envelope's own writing of
// the name along with the author's.
TEST(EnvelopeEncryption, TheDescriptionWrittenWithTheBlockGovernsIt) {
  ReadBack run(Encrypted(kSpecifiedEnvelope));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Names(run.envelope.envelope_keywords, "data_method"));
  EXPECT_TRUE(Holds(run.text, "initial result = 42;"));
}

// A comment written on a delimiter's directive is not a pragma expression and
// says nothing about the envelope, so it is not among the things carried
// across. The expressions beside it are carried and the comment is not, which
// is also what keeps the produced envelope readable: a block comment the
// author never closed would otherwise be carried onto the opening directive
// and take the description and the block after it into the comment, leaving an
// envelope that closes nothing and a design that never arrives.
TEST(EnvelopeEncryption, ACommentOnADelimiterIsNotACarriedExpression) {
  std::string opening =
      "`pragma protect author=\"Acme Corp\", begin_protected\n";
  std::string src =
      "`pragma protect author=\"Acme Corp\", begin /* never closed\n"
      "  initial result = 42;\n"
      "`pragma protect end\n";
  std::string written = Encrypted(src);
  ReadBack run(written);
  EXPECT_TRUE(Holds(written, opening));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Names(run.envelope.envelope_keywords, "author"));
  EXPECT_TRUE(Holds(run.text, "initial result = 42;"));
}

// The negative form of the carrying rule: an envelope the author specified
// with nothing beside its delimiters is given nothing. The transformation
// carries what was written rather than inventing a specification for an
// envelope that had none.
TEST(EnvelopeEncryption, ADelimiterStandingAloneIsCarriedAlone) {
  std::string written = Encrypted(
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n");
  EXPECT_TRUE(Holds(written, "`pragma protect begin_protected\n"));
  EXPECT_TRUE(Holds(written, "`pragma protect end_protected\n"));
}

// ---------------------------------------------------------------------------
// The body of the encryption envelope is what gets encrypted.
// ---------------------------------------------------------------------------

// A protect pragma directive written inside the envelope is part of the text
// the envelope encloses, so it is encrypted along with the design rather than
// read as part of the envelope's specification. The standard's own example
// puts a licensing expression there, and this is that arrangement: the
// expression is nowhere in the transformed text, and it comes back with the
// design when the block is opened.
TEST(EnvelopeEncryption, AnExpressionInsideTheEnvelopeIsEncryptedWithIt) {
  std::string written = Encrypted(
      "`pragma protect begin\n"
      "`pragma protect runtime_license=(library=\"lic.so\")\n"
      "  initial result = 42;\n"
      "`pragma protect end\n");
  EXPECT_FALSE(Holds(written, "runtime_license"));
  ASSERT_EQ(RecordedBlocks(written).size(), 1U);
  EXPECT_EQ(Recovered(RecordedBlocks(written)[0], kExchangeKey),
            "`pragma protect runtime_license=(library=\"lic.so\")\n"
            "  initial result = 42;\n");
}

// The closest input to that one which the rule has to treat the other way. The
// same expression written ahead of the opening delimiter is not enclosed by
// anything, so it is not encrypted: it stands in the transformed text as the
// bytes the author wrote, and no block records it.
TEST(EnvelopeEncryption, TheSameExpressionOutsideTheEnvelopeIsNotEncrypted) {
  std::string written = Encrypted(
      "`pragma protect runtime_license=(library=\"lic.so\")\n"
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n");
  EXPECT_TRUE(Holds(written, "runtime_license=(library=\"lic.so\")\n"));
  ASSERT_EQ(RecordedBlocks(written).size(), 1U);
  EXPECT_EQ(Recovered(RecordedBlocks(written)[0], kExchangeKey),
            "  initial result = 42;\n");
}

// The smallest body there is. Delimiters written next to each other enclose no
// text, and an envelope enclosing nothing is still an envelope to replace: a
// block is recorded, it opens, and what it stands for is the nothing that was
// there. The last two claims are made apart because a block that failed to
// open would hand back nothing as well, and only one of the two is the rule.
TEST(EnvelopeEncryption, AnEnvelopeEnclosingNoTextIsStillReplaced) {
  std::string written = Encrypted(
      "`pragma protect begin\n"
      "`pragma protect end\n");
  std::vector<std::string> blocks = RecordedBlocks(written);
  ASSERT_EQ(blocks.size(), 1U);
  EXPECT_TRUE(Recoverable(blocks.front(), kExchangeKey));
  EXPECT_EQ(Recovered(blocks.front(), kExchangeKey), "");
}

// Forming the envelope asked nothing of what the envelope enclosed. A body
// that is not a design at all -- brackets that do not balance, a string with
// no closing quote -- is encrypted and comes back character for character, so
// none of it had to be read for the envelope to be formed from it.
TEST(EnvelopeEncryption, ABodyThatIsNotSystemVerilogIsEncryptedUnread) {
  std::string written = Encrypted(
      "`pragma protect begin\n"
      "?? not a design at all ((\n"
      "\"no closing quote\n"
      "`pragma protect end\n");
  ASSERT_EQ(RecordedBlocks(written).size(), 1U);
  EXPECT_EQ(Recovered(RecordedBlocks(written)[0], kExchangeKey),
            "?? not a design at all ((\n"
            "\"no closing quote\n");
}

// ---------------------------------------------------------------------------
// Text no encryption envelope contains is not modified.
// ---------------------------------------------------------------------------

// The closest input the process has to leave entirely alone. A source text
// holding no encryption envelope has none to replace, so every character of it
// comes back as it was written -- including a protect pragma directive, which
// is text the process does read -- and no block is recorded.
TEST(EnvelopeEncryption, ATextWithNoEnvelopeIsCarriedAcrossWhole) {
  std::string src =
      "module secret (a, b);\n"
      "`pragma protect author=\"Acme Corp\"\n"
      "  initial result = 42;\n"
      "endmodule\n";
  EXPECT_EQ(Encrypted(src), src);
  EXPECT_TRUE(RecordedBlocks(Encrypted(src)).empty());
}

// Each envelope is replaced where it stands, so a line written between two of
// them was enclosed by neither and is carried across whole. A process that
// took the outermost delimiters for one envelope would have swallowed that
// line into the first block, and both blocks would not recover as they do.
TEST(EnvelopeEncryption, TextBetweenTwoEnvelopesBelongsToNeither) {
  std::string written = Encrypted(
      "`pragma protect begin\n"
      "  initial first = 1;\n"
      "`pragma protect end\n"
      "  initial between = 2;\n"
      "`pragma protect begin\n"
      "  initial second = 3;\n"
      "`pragma protect end\n");
  ASSERT_EQ(RecordedBlocks(written).size(), 2U);
  EXPECT_TRUE(Holds(written, "  initial between = 2;\n"));
  EXPECT_EQ(Recovered(RecordedBlocks(written)[0], kExchangeKey),
            "  initial first = 1;\n");
  EXPECT_EQ(Recovered(RecordedBlocks(written)[1], kExchangeKey),
            "  initial second = 3;\n");
}

// The text on either side of an envelope comes back as it went in, down to the
// bytes. A protect pragma directive is the interesting case, because it is
// text the process does read: standing where no envelope encloses it, it is
// still text of the source and is left where it was rather than folded into
// the envelope that follows.
TEST(EnvelopeEncryption, TextOutsideAnEnvelopeIsCarriedAcrossByteForByte) {
  std::string unchanged =
      "module secret (a, b);\n"
      "`pragma protect author=\"Acme Corp\"\n"
      "`pragma protect begin_protected\n";
  std::string written = Encrypted(
      "module secret (a, b);\n"
      "`pragma protect author=\"Acme Corp\"\n"
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n"
      "endmodule\n");
  EXPECT_TRUE(Holds(written, unchanged));
  EXPECT_TRUE(Holds(written, "endmodule\n"));
}

// The negative form: the delimiting directives are contained in the envelope,
// so they are the one part of the text the process does modify. Without this
// the rule above would be satisfied by a process that modified nothing at all.
TEST(EnvelopeEncryption, TheDelimitingDirectivesThemselvesAreModified) {
  std::string src =
      "module secret (a, b);\n"
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n"
      "endmodule\n";
  EXPECT_NE(Encrypted(src), src);
  EXPECT_FALSE(Holds(Encrypted(src), "`pragma protect begin\n"));
  EXPECT_FALSE(Holds(Encrypted(src), "`pragma protect end\n"));
}

// An opening delimiter the source never closed encloses no region, so no
// envelope was replaced and there is nothing this process modified: the
// directive and every line after it are text of the source and come back as
// they stand.
TEST(EnvelopeEncryption, AnUnclosedDelimiterLeavesTheTextAsItWasWritten) {
  std::string src =
      "module secret (a, b);\n"
      "`pragma protect data_method=\"x-caesar\", begin\n"
      "  initial result = 42;\n";
  EXPECT_EQ(Encrypted(src), src);
  EXPECT_TRUE(RecordedBlocks(Encrypted(src)).empty());
}

// ---------------------------------------------------------------------------
// The exchange key, and the symmetry of the algorithm using it.
// ---------------------------------------------------------------------------

// The body is encrypted under the key the author specified, and that same key
// is what opens what was encrypted -- one key doing both, which is what makes
// the algorithm and the key symmetric.
//
// The envelope records the region and no key beside it, which says which of
// the two arrangements the standard describes this one is. A tool is permitted
// the other, in which a key_block carries a key made for the occasion,
// encrypted under the exchange key, and the data_block carries the region
// encrypted under that made key instead.
TEST(EnvelopeEncryption, TheRegionIsRecordedUnderTheExchangeKeyAlone) {
  std::string written = Encrypted(
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n");
  ASSERT_EQ(RecordedBlocks(written).size(), 1U);
  EXPECT_FALSE(Holds(written, "key_block"));
  EXPECT_EQ(Recovered(RecordedBlocks(written)[0], kExchangeKey),
            "  initial result = 42;\n");
}

// The negative form of symmetry, over the region the test above records. A
// second, different key opens nothing, so there is no asymmetric pair here in
// which one key encrypts and another decrypts -- which recovering under the
// encrypting key would otherwise leave open.
TEST(EnvelopeEncryption, ASecondKeyOpensNothingTheExchangeKeyEncrypted) {
  std::string block = OneBlock(
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n");
  EXPECT_FALSE(Recoverable(block, kOtherKey));
  EXPECT_EQ(Recovered(block, kOtherKey), "");
}

// The encrypting half given no key at all. There is nothing to encrypt a body
// under, so no envelope is replaced and the text stands as it was written --
// the negative form of the rule that the body is encrypted under the key the
// author specified. This is the encrypting half's own case: a text read
// afterwards without a key is the other half of the pair.
TEST(EnvelopeEncryption, NoKeyToEncryptUnderLeavesTheTextAsItStands) {
  std::string src =
      "module secret (a, b);\n"
      "`pragma protect data_method=\"x-caesar\", begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n"
      "endmodule\n";
  EXPECT_EQ(EncryptEnvelopes(src, ""), src);
  EXPECT_TRUE(RecordedBlocks(EncryptEnvelopes(src, "")).empty());
}

// What the whole transformation is for, read at the point the step after the
// preprocessor reads it: an envelope specified by the author, formed under the
// exchange key, and opened again with that same key hands back the design it
// carried, with none of the envelope left in the text.
TEST(EnvelopeEncryption, AnEnvelopeFormedHereOpensAgainUnderTheSameKey) {
  ReadBack run(Encrypted(kSpecifiedEnvelope));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, "initial result = 42;"));
  EXPECT_FALSE(Holds(run.text, "data_block"));
}

}  // namespace
