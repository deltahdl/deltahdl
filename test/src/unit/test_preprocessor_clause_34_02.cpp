// §34.2 Overview -- protected envelopes.
//
// The clause names one reserved pragma as the carrier of every piece of
// envelope information, gives each of the two modes of processing an opening
// and a closing pragma expression, pairs a closing expression with the most
// recent still-open opening one, floors the supported nesting of decryption
// envelopes, and splits the remaining expressions into the ones that describe
// an envelope and the ones that describe its content.
//
// All of it is preprocessor-stage state. The pragma handler in
// src/preprocessor/preprocessor_lines.cpp walks a directive's expressions and
// hands the ones belonging to the reserved pragma to
// src/preprocessor/protect_envelope.cpp, where the envelopes accumulate. Every
// input here is written as the real directive syntax of §22.11 and driven
// through Preprocessor::Preprocess.

#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_envelope.h"

using namespace delta;

namespace {

// Preprocesses `src` and keeps the Preprocessor alive afterwards. What these
// rules leave behind is envelope state rather than output text, so the state
// has to outlive the call that built it and the text is dropped. What a design
// carried through that text goes on to do is observed at the simulator stage
// instead.
struct EnvelopeRun {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp{mgr, diag, {}};

  explicit EnvelopeRun(const std::string& src) {
    pp.Preprocess(mgr.AddFile("<test>", src));
  }

  const ProtectEnvelopeState& Envelopes() const {
    return pp.ProtectEnvelopes();
  }
};

// Builds `count` directives, one per line, each holding the same expression.
// Used by the nesting tests, where the interesting number is the depth rather
// than any one line's text.
std::string RepeatDirective(const std::string& keyword, size_t count) {
  std::string src;
  for (size_t n = 0; n < count; ++n) {
    src += "`pragma protect " + keyword + "\n";
  }
  return src;
}

// ---------------------------------------------------------------------------
// The protect pragma is what introduces envelope information.
// ---------------------------------------------------------------------------

// The reserved pragma name carries the expression that opens an encryption
// envelope, so the directive leaves one envelope open.
TEST(ProtectedEnvelopeOverview, ProtectPragmaOpensEncryptionEnvelope) {
  EnvelopeRun run("`pragma protect begin\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.Envelopes().EncryptionEnvelopeDepth(), 1U);
}

// The name is reserved for this description, so the same expression under any
// other pragma_name describes no envelope. Without this the whole clause would
// hang off the spelling of the expression rather than off the pragma.
TEST(ProtectedEnvelopeOverview, OtherPragmaNameOpensNoEnvelope) {
  EnvelopeRun run(
      "`pragma acme_tool begin\n"
      "`pragma acme_tool begin_protected\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.Envelopes().EncryptionEnvelopeDepth(), 0U);
  EXPECT_EQ(run.Envelopes().DecryptionEnvelopeDepth(), 0U);
}

// An opening expression is a pragma_keyword, and a pragma_keyword is a simple
// identifier. The escaped spelling of the same name is a pragma_value instead,
// so it opens nothing.
TEST(ProtectedEnvelopeOverview, EscapedIdentifierOpensNoEnvelope) {
  EnvelopeRun run("`pragma protect \\begin\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.Envelopes().EncryptionEnvelopeDepth(), 0U);
}

// The expressions that act on envelopes are the pragma's own, not the ones
// nested inside a parenthesized value that qualifies some other keyword.
TEST(ProtectedEnvelopeOverview, KeywordNestedInsideAValueOpensNoEnvelope) {
  EnvelopeRun run("`pragma protect encoding = ( begin )\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.Envelopes().EncryptionEnvelopeDepth(), 0U);
}

// ---------------------------------------------------------------------------
// Encryption envelopes: opened by begin, closed by end.
// ---------------------------------------------------------------------------

// The closing expression closes the region the opening one started, leaving a
// finished envelope of the encryption mode behind.
TEST(ProtectedEnvelopeOverview, EndClosesTheEncryptionEnvelope) {
  EnvelopeRun run("`pragma protect begin\n`pragma protect end\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.Envelopes().EncryptionEnvelopeDepth(), 0U);
  ASSERT_EQ(run.Envelopes().ClosedEnvelopes().size(), 1U);
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes()[0].mode,
            EnvelopeMode::kEncryption);
}

// The pairing rule, and the reason the locations are kept: with two openings
// outstanding, the closing expression takes the more recent one. Reading the
// depth alone would not tell the two candidate pairings apart, so the line the
// closed envelope opened on is what is checked.
TEST(ProtectedEnvelopeOverview, EndPairsWithTheMostRecentBegin) {
  EnvelopeRun run(
      "`pragma protect begin\n"
      "`pragma protect begin\n"
      "`pragma protect end\n");
  EXPECT_FALSE(run.diag.HasErrors());
  ASSERT_EQ(run.Envelopes().ClosedEnvelopes().size(), 1U);
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes()[0].begin_loc.line, 2U);
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes()[0].end_loc.line, 3U);
  EXPECT_EQ(run.Envelopes().EncryptionEnvelopeDepth(), 1U);
}

// The closest input the pairing rule has to turn away: with no opening
// expression outstanding there is nothing for the closing one to be associated
// with, so it closes no envelope and leaves no finished one behind.
TEST(ProtectedEnvelopeOverview, EndWithNothingOpenClosesNoEnvelope) {
  EnvelopeRun run("`pragma protect end\n");
  EXPECT_EQ(run.Envelopes().EncryptionEnvelopeDepth(), 0U);
  EXPECT_TRUE(run.Envelopes().ClosedEnvelopes().empty());
}

// ---------------------------------------------------------------------------
// Decryption envelopes: opened by begin_protected, closed by end_protected.
// ---------------------------------------------------------------------------

// The other mode of processing has its own opening expression, and the code it
// encloses is protected code.
TEST(ProtectedEnvelopeOverview, BeginProtectedOpensADecryptionEnvelope) {
  EnvelopeRun run("`pragma protect begin_protected\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.Envelopes().DecryptionEnvelopeDepth(), 1U);
  EXPECT_TRUE(run.Envelopes().InProtectedRegion());
}

// An encryption envelope encloses the cleartext that is still to be encrypted,
// so what it encloses is not protected code. Without this the two modes would
// be indistinguishable to a reader asking whether code is protected.
TEST(ProtectedEnvelopeOverview, EncryptionEnvelopeDoesNotProtectItsCode) {
  EnvelopeRun run("`pragma protect begin\n");
  EXPECT_FALSE(run.Envelopes().InProtectedRegion());
}

// Closing the decryption envelope ends the protected region.
TEST(ProtectedEnvelopeOverview, EndProtectedEndsTheProtectedRegion) {
  EnvelopeRun run(
      "`pragma protect begin_protected\n"
      "`pragma protect end_protected\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.Envelopes().InProtectedRegion());
  ASSERT_EQ(run.Envelopes().ClosedEnvelopes().size(), 1U);
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes()[0].mode,
            EnvelopeMode::kDecryption);
}

// The two modes keep their own openings: an encryption envelope's closing
// expression is not the one that closes a decryption envelope, and vice versa.
TEST(ProtectedEnvelopeOverview, ClosingExpressionsDoNotCrossModes) {
  EnvelopeRun run(
      "`pragma protect begin_protected\n"
      "`pragma protect end\n");
  EXPECT_EQ(run.Envelopes().DecryptionEnvelopeDepth(), 1U);
  EXPECT_TRUE(run.Envelopes().ClosedEnvelopes().empty());
}

// A decryption envelope may hold further envelopes, and its closing expression
// takes the most recent opening one that is still open -- so the inner pair
// closes first and the outer pair closes second.
TEST(ProtectedEnvelopeOverview, EndProtectedPairsWithTheInnermostOpenEnvelope) {
  EnvelopeRun run(
      "`pragma protect begin_protected\n"
      "`pragma protect begin_protected\n"
      "`pragma protect end_protected\n"
      "`pragma protect end_protected\n");
  EXPECT_FALSE(run.diag.HasErrors());
  ASSERT_EQ(run.Envelopes().ClosedEnvelopes().size(), 2U);
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes()[0].begin_loc.line, 2U);
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes()[1].begin_loc.line, 1U);
  EXPECT_EQ(run.Envelopes().DecryptionEnvelopeDepth(), 0U);
}

// The counterpart of the encryption mode's unmatched closing expression. The
// two modes keep separate openings, so an unmatched closing expression in one
// of them is not covered by the other's: with no decryption envelope open
// there is nothing this expression can be associated with.
TEST(ProtectedEnvelopeOverview, EndProtectedWithNothingOpenClosesNoEnvelope) {
  EnvelopeRun run("`pragma protect end_protected\n");
  EXPECT_EQ(run.Envelopes().DecryptionEnvelopeDepth(), 0U);
  EXPECT_TRUE(run.Envelopes().ClosedEnvelopes().empty());
}

// What a decryption envelope may enclose is envelopes, not merely further
// decryption envelopes. An encryption envelope written inside an open
// decryption envelope is paired off against its own opening expression, and
// the enclosing pair closes after it.
TEST(ProtectedEnvelopeOverview, EncryptionEnvelopeNestsInsideADecryptionOne) {
  EnvelopeRun run(
      "`pragma protect begin_protected\n"
      "`pragma protect begin\n"
      "`pragma protect end\n"
      "`pragma protect end_protected\n");
  EXPECT_FALSE(run.diag.HasErrors());
  ASSERT_EQ(run.Envelopes().ClosedEnvelopes().size(), 2U);
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes()[0].mode,
            EnvelopeMode::kEncryption);
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes()[0].begin_loc.line, 2U);
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes()[1].mode,
            EnvelopeMode::kDecryption);
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes()[1].begin_loc.line, 1U);
}

// Protectedness follows the enclosing decryption envelope rather than the
// innermost one: closing the inner pair leaves the code that follows still
// inside the outer envelope, so it is still protected.
TEST(ProtectedEnvelopeOverview, CodeStaysProtectedWhileAnOuterEnvelopeIsOpen) {
  EnvelopeRun run(
      "`pragma protect begin_protected\n"
      "`pragma protect begin_protected\n"
      "`pragma protect end_protected\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.Envelopes().InProtectedRegion());
  EXPECT_EQ(run.Envelopes().DecryptionEnvelopeDepth(), 1U);
}

// An encryption envelope does not protect its own code, but it does not
// unprotect the decryption envelope it is nested in either: what decides is
// whether a decryption envelope encloses the code, not which envelope opened
// most recently.
TEST(ProtectedEnvelopeOverview, NestedEncryptionEnvelopeKeepsCodeProtected) {
  EnvelopeRun run(
      "`pragma protect begin_protected\n"
      "`pragma protect begin\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.Envelopes().InProtectedRegion());
  EXPECT_EQ(run.Envelopes().EncryptionEnvelopeDepth(), 1U);
  EXPECT_EQ(run.Envelopes().DecryptionEnvelopeDepth(), 1U);
}

// How deep decryption envelopes may nest is the implementation's choice, but
// the clause puts a floor under it. Eight nested envelopes are inside any
// conforming implementation's capacity, so all eight are open at once.
TEST(ProtectedEnvelopeOverview, EightNestedDecryptionEnvelopesAreProcessed) {
  EnvelopeRun run(RepeatDirective(
      "begin_protected", ProtectEnvelopeState::kMinNestedDecryptionEnvelopes));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.Envelopes().DecryptionEnvelopeDepth(),
            ProtectEnvelopeState::kMinNestedDecryptionEnvelopes);
}

// The eight nested envelopes close as eight envelopes rather than collapsing
// into one, which is what makes the floor a nesting depth and not just a count
// of directives that were tolerated.
TEST(ProtectedEnvelopeOverview, EightNestedDecryptionEnvelopesAllClose) {
  const size_t kDepth = ProtectEnvelopeState::kMinNestedDecryptionEnvelopes;
  EnvelopeRun run(RepeatDirective("begin_protected", kDepth) +
                  RepeatDirective("end_protected", kDepth));
  EXPECT_FALSE(run.diag.HasErrors());
  ASSERT_EQ(run.Envelopes().ClosedEnvelopes().size(), kDepth);
  EXPECT_EQ(run.Envelopes().DecryptionEnvelopeDepth(), 0U);
  // The last envelope to close is the first that opened.
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes().back().begin_loc.line, 1U);
}

// Past the depth this implementation supports there is no envelope to open, so
// the condition is reported rather than silently dropped.
TEST(ProtectedEnvelopeOverview, NestingBeyondTheSupportedDepthIsReported) {
  EnvelopeRun run(RepeatDirective(
      "begin_protected",
      ProtectEnvelopeState::kNestedDecryptionEnvelopeLimit + 1));
  EXPECT_TRUE(run.diag.HasErrors());
  EXPECT_EQ(run.Envelopes().DecryptionEnvelopeDepth(),
            ProtectEnvelopeState::kNestedDecryptionEnvelopeLimit);
}

// ---------------------------------------------------------------------------
// Envelope keywords and content keywords.
// ---------------------------------------------------------------------------

// An expression written where no envelope is open precedes the opening one, so
// it describes the envelope that opening expression goes on to open.
TEST(ProtectedEnvelopeOverview, ExpressionsBeforeBeginDescribeTheEnvelope) {
  EnvelopeRun run(
      "`pragma protect data_method = \"aes128-cbc\"\n"
      "`pragma protect begin\n");
  EXPECT_FALSE(run.diag.HasErrors());
  ASSERT_EQ(run.Envelopes().OpenEnvelopes().size(), 1U);
  EXPECT_EQ(run.Envelopes().OpenEnvelopes()[0].envelope_keywords,
            std::vector<std::string>{"data_method"});
  EXPECT_TRUE(run.Envelopes().OpenEnvelopes()[0].content_keywords.empty());
  // The opening expression took the waiting keyword with it.
  EXPECT_TRUE(run.Envelopes().PendingEnvelopeKeywords().empty());
}

// An expression written between an opening expression and the closing one it
// pairs with sits in the region that gets transformed, so it describes the
// envelope's content instead.
TEST(ProtectedEnvelopeOverview, ExpressionsInsideAnEnvelopeDescribeItsContent) {
  EnvelopeRun run(
      "`pragma protect begin\n"
      "`pragma protect key_keyname = \"acme-key\"\n"
      "`pragma protect end\n");
  EXPECT_FALSE(run.diag.HasErrors());
  ASSERT_EQ(run.Envelopes().ClosedEnvelopes().size(), 1U);
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes()[0].content_keywords,
            std::vector<std::string>{"key_keyname"});
  EXPECT_TRUE(run.Envelopes().ClosedEnvelopes()[0].envelope_keywords.empty());
}

// The content region stops at the closing expression: an expression written
// after it is outside every envelope again, so it describes the next envelope
// rather than joining the one that has just closed.
TEST(ProtectedEnvelopeOverview, ExpressionsAfterEndDescribeTheNextEnvelope) {
  EnvelopeRun run(
      "`pragma protect begin\n"
      "`pragma protect end\n"
      "`pragma protect encrypt_agent = \"AcmeCrypt\"\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.Envelopes().PendingEnvelopeKeywords(),
            std::vector<std::string>{"encrypt_agent"});
  ASSERT_EQ(run.Envelopes().ClosedEnvelopes().size(), 1U);
  EXPECT_TRUE(run.Envelopes().ClosedEnvelopes()[0].content_keywords.empty());
  EXPECT_TRUE(run.Envelopes().ClosedEnvelopes()[0].envelope_keywords.empty());
}

// The role an expression is designated is decided by where it is written, not
// by what its value looks like, so a keyword carrying a number is designated
// the same way one carrying a string is. The number takes its own branch of
// the pragma_value grammar, which is why it is written out rather than assumed
// to follow the string case.
TEST(ProtectedEnvelopeOverview, KeywordWithANumberValueTakesTheSameRole) {
  EnvelopeRun run(
      "`pragma protect begin\n"
      "`pragma protect bytes = 4096\n"
      "`pragma protect end\n");
  EXPECT_FALSE(run.diag.HasErrors());
  ASSERT_EQ(run.Envelopes().ClosedEnvelopes().size(), 1U);
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes()[0].content_keywords,
            std::vector<std::string>{"bytes"});
  EXPECT_TRUE(run.Envelopes().ClosedEnvelopes()[0].envelope_keywords.empty());
}

// The same for a keyword whose value is a parenthesized list of further
// expressions. The keyword takes its role from its position; the expressions
// inside its value qualify the value, so they are designated nothing.
TEST(ProtectedEnvelopeOverview, ParenthesizedValueKeywordTakesTheSameRole) {
  EnvelopeRun run(
      "`pragma protect encoding = ( enctype = \"base64\", line_length = 64 )\n"
      "`pragma protect begin\n");
  EXPECT_FALSE(run.diag.HasErrors());
  ASSERT_EQ(run.Envelopes().OpenEnvelopes().size(), 1U);
  EXPECT_EQ(run.Envelopes().OpenEnvelopes()[0].envelope_keywords,
            std::vector<std::string>{"encoding"});
  EXPECT_TRUE(run.Envelopes().OpenEnvelopes()[0].content_keywords.empty());
}

// A decryption envelope splits the two roles the same way its encryption
// counterpart does.
TEST(ProtectedEnvelopeOverview, BeginProtectedSplitsTheSameTwoRoles) {
  EnvelopeRun run(
      "`pragma protect key_keyowner = \"Acme Corp\"\n"
      "`pragma protect begin_protected\n"
      "`pragma protect data_block\n"
      "`pragma protect end_protected\n");
  EXPECT_FALSE(run.diag.HasErrors());
  ASSERT_EQ(run.Envelopes().ClosedEnvelopes().size(), 1U);
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes()[0].envelope_keywords,
            std::vector<std::string>{"key_keyowner"});
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes()[0].content_keywords,
            std::vector<std::string>{"data_block"});
}

// A keyword describes the particular envelope it was written against, so two
// envelopes in one source text keep their descriptions apart rather than
// pooling them. Nothing in a one-envelope input can tell the two models apart,
// which is why this input carries two.
TEST(ProtectedEnvelopeOverview, EachEnvelopeKeepsItsOwnKeywords) {
  EnvelopeRun run(
      "`pragma protect data_method = \"aes128-cbc\"\n"
      "`pragma protect begin\n"
      "`pragma protect key_keyname = \"first-key\"\n"
      "`pragma protect end\n"
      "`pragma protect encrypt_agent = \"AcmeCrypt\"\n"
      "`pragma protect begin_protected\n"
      "`pragma protect data_block\n"
      "`pragma protect end_protected\n");
  EXPECT_FALSE(run.diag.HasErrors());
  ASSERT_EQ(run.Envelopes().ClosedEnvelopes().size(), 2U);
  const auto& first = run.Envelopes().ClosedEnvelopes()[0];
  const auto& second = run.Envelopes().ClosedEnvelopes()[1];
  EXPECT_EQ(first.envelope_keywords, std::vector<std::string>{"data_method"});
  EXPECT_EQ(first.content_keywords, std::vector<std::string>{"key_keyname"});
  EXPECT_EQ(second.envelope_keywords,
            std::vector<std::string>{"encrypt_agent"});
  EXPECT_EQ(second.content_keywords, std::vector<std::string>{"data_block"});
}

// A keyword written inside a region belongs to the innermost envelope open at
// that point, not to the one enclosing it, so nesting splits the descriptions
// the same way separate envelopes do.
TEST(ProtectedEnvelopeOverview, NestedEnvelopesKeepTheirKeywordsApart) {
  EnvelopeRun run(
      "`pragma protect begin_protected\n"
      "`pragma protect key_keyowner = \"Acme Corp\"\n"
      "`pragma protect begin\n"
      "`pragma protect data_block\n"
      "`pragma protect end\n"
      "`pragma protect end_protected\n");
  EXPECT_FALSE(run.diag.HasErrors());
  ASSERT_EQ(run.Envelopes().ClosedEnvelopes().size(), 2U);
  // The inner envelope closes first and holds only what was written inside it.
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes()[0].mode,
            EnvelopeMode::kEncryption);
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes()[0].content_keywords,
            std::vector<std::string>{"data_block"});
  // The keyword written before the inner envelope opened is already inside the
  // enclosing region, so it describes that region's content.
  EXPECT_EQ(run.Envelopes().ClosedEnvelopes()[1].content_keywords,
            std::vector<std::string>{"key_keyowner"});
}

// ---------------------------------------------------------------------------
// The order the expressions are read in, and how they are distributed.
// ---------------------------------------------------------------------------

// The expressions of one directive are read left to right. The opening
// expression sits between the other two, so the one on its left describes the
// envelope and the one on its right describes the content -- the reverse of
// what reading the list from the right would give.
TEST(ProtectedEnvelopeOverview, ExpressionsOfOneDirectiveAreReadLeftToRight) {
  EnvelopeRun run(
      "`pragma protect encrypt_agent = \"AcmeCrypt\", begin, "
      "key_keyname = \"acme-key\"\n");
  EXPECT_FALSE(run.diag.HasErrors());
  ASSERT_EQ(run.Envelopes().OpenEnvelopes().size(), 1U);
  EXPECT_EQ(run.Envelopes().OpenEnvelopes()[0].envelope_keywords,
            std::vector<std::string>{"encrypt_agent"});
  EXPECT_EQ(run.Envelopes().OpenEnvelopes()[0].content_keywords,
            std::vector<std::string>{"key_keyname"});
}

// The same sequence of expressions means the same thing however it is
// distributed over directives, so writing the sequence above as three
// directives leaves the identical roles behind.
TEST(ProtectedEnvelopeOverview, SplittingASequenceOverDirectivesKeepsTheRoles) {
  EnvelopeRun run(
      "`pragma protect encrypt_agent = \"AcmeCrypt\"\n"
      "`pragma protect begin\n"
      "`pragma protect key_keyname = \"acme-key\"\n");
  EXPECT_FALSE(run.diag.HasErrors());
  ASSERT_EQ(run.Envelopes().OpenEnvelopes().size(), 1U);
  EXPECT_EQ(run.Envelopes().OpenEnvelopes()[0].envelope_keywords,
            std::vector<std::string>{"encrypt_agent"});
  EXPECT_EQ(run.Envelopes().OpenEnvelopes()[0].content_keywords,
            std::vector<std::string>{"key_keyname"});
}

// The distribution does not change the envelopes either: an opening expression
// in one directive is paired with a closing expression in another, and a pair
// written into a single directive is paired just the same.
TEST(ProtectedEnvelopeOverview, SplittingASequenceKeepsThePairing) {
  EnvelopeRun joined("`pragma protect begin, end\n");
  EnvelopeRun split("`pragma protect begin\n`pragma protect end\n");
  EXPECT_EQ(joined.Envelopes().ClosedEnvelopes().size(), 1U);
  EXPECT_EQ(split.Envelopes().ClosedEnvelopes().size(), 1U);
  EXPECT_EQ(joined.Envelopes().EncryptionEnvelopeDepth(), 0U);
  EXPECT_EQ(split.Envelopes().EncryptionEnvelopeDepth(), 0U);
}

}  // namespace
