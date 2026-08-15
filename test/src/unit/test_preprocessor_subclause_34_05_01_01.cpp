// §34.5.1.1 Syntax, for the protect pragma keyword that opens an encryption
// envelope.
//
// The subclause is a syntax block holding one line, and what that line settles
// is the spelling of the expression:
//
//   The keyword is written as the word by itself.
//
// §22.5.1 offers a pragma expression two spellings -- a pragma_keyword
// standing alone, and a pragma_keyword with a pragma_value written against it
// -- and other keywords of this same table are defined with the second of
// them, `author = <string>` among them. This one is defined with the first, so
// a value written against the word leaves an expression the standard does not
// define: it opens no envelope, and it is not one of the other keywords
// either.
//
// The word is a pragma_keyword of the protect pragma, so it is reached through
// the `pragma directive of §22.5.1 carrying the pragma_name of §34.2, and what
// it opens is only visible once something closes it or reads it: §34.5.2.1's
// closing keyword pairs with it, and §34.3.1's encrypting half takes it as the
// delimiter of the region it replaces. Every input here is therefore written
// as real directive syntax and read through the whole preprocessor rather than
// handed to the envelope state directly.
//
// All of it is preprocessor-stage. src/preprocessor/preprocessor_lines.cpp
// reads the directive's expressions and reports a word written with a value it
// is not defined with, src/preprocessor/protect_envelope.cpp holds the word
// and the rule for what spells it, and src/preprocessor/protect_processing.cpp
// is the second reader of the same word, on the encrypting side.

#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_protect_read.h"
#include "helpers_reported_error.h"
#include "helpers_text_lines.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_envelope.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// The word standing on its own is the expression.
// ---------------------------------------------------------------------------

// The syntax block read at its plainest: the word written by itself as the
// whole expression list of a protect pragma directive opens an envelope for
// encryption, and nothing about the directive is complained of.
TEST(ProtectBeginSyntax, TheWordAloneOpensAnEncryptionEnvelope) {
  ReadSource run("`pragma protect begin\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 1U);
}

// The same word read against the keyword §34.5.2.1 defines to close what it
// opened. What the pair leaves behind is one envelope defined for encryption
// rather than for decryption, which is the mode this word's envelope has and
// the other opening keyword's does not.
TEST(ProtectBeginSyntax, TheEnvelopeItOpenedIsTheOneThatWasClosed) {
  ReadSource run(
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 0U);
  ASSERT_EQ(run.Closed().size(), 1U);
  EXPECT_EQ(run.Closed().front().mode, EnvelopeMode::kEncryption);
}

// A directive carrying the word is a directive like any other as far as the
// text leaving the preprocessor goes: it is consumed, and the source written
// around it arrives at the step after unchanged.
TEST(ProtectBeginSyntax, TheDirectiveCarryingTheWordContributesNoText) {
  ReadSource run(
      "module secret;\n"
      "`pragma protect begin\n"
      "endmodule\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(Holds(run.text, "pragma"));
  EXPECT_TRUE(Holds(run.text, "module secret;"));
  EXPECT_TRUE(Holds(run.text, "endmodule"));
}

// The position the standard's own example writes the word in: last in a list
// whose earlier expressions are keywords defined with a value. The word is
// still the word standing alone -- each expression of the list is spelled on
// its own -- so it still opens the envelope those expressions describe.
TEST(ProtectBeginSyntax, TheWordLastAfterValuedExpressionsStillOpens) {
  ReadSource run(
      "`pragma protect author=\"Acme Corp\", "
      "data_method=\"x-caesar\", begin\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 1U);
}

// The other order over the same list. A comma ends the expression before it,
// so a valued keyword written after the word qualifies neither the word nor
// the envelope's opening, and the word standing ahead of it is still the word
// standing alone.
TEST(ProtectBeginSyntax, TheWordFirstAheadOfAValuedExpressionStillOpens) {
  ReadSource run("`pragma protect begin, comment=\"the region below\"\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 1U);
}

// The word as the whole of its own directive, with the expressions describing
// the envelope written on the directive ahead of it. One expression list means
// the same thing however it is spread over directives, so the word opens here
// exactly as it does when it shares a directive with them.
TEST(ProtectBeginSyntax, TheWordAloneOnItsOwnDirectiveStillOpens) {
  ReadSource run(
      "`pragma protect author=\"Acme Corp\"\n"
      "`pragma protect begin\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 1U);
}

// The word need not be written in the source as the word: a directive's text
// is ordinary source text, so a macro usage in it is substituted before the
// pragma grammar reads it, and what the grammar then reads is the word.
TEST(ProtectBeginSyntax, AMacroExpandingToTheWordOpensTheEnvelope) {
  ReadSource run(
      "`define OPEN begin\n"
      "`pragma protect `OPEN\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 1U);
}

// A comment is not a pragma expression, so a directive whose word is followed
// by one carries the word alone and opens on it. Without this the word would
// have to be the last thing on its line to be the word.
TEST(ProtectBeginSyntax, ACommentAfterTheWordLeavesItStandingAlone) {
  ReadSource run("`pragma protect begin // the region starts here\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 1U);
}

// The second reader of the same word, on the encrypting side. What the word
// delimits there is the region replaced by an envelope for the other mode of
// processing, so the word standing alone is what makes a region get encrypted
// at all.
TEST(ProtectBeginSyntax, TheEncryptingHalfTakesTheWordAloneAsItsDelimiter) {
  std::string written = EncryptedByTheAuthor(
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n");
  EXPECT_TRUE(Holds(written, "`pragma protect begin_protected\n"));
  EXPECT_TRUE(Holds(written, "data_block=\""));
  EXPECT_FALSE(Holds(written, "initial result = 42;"));
}

// The word driving both halves from end to end, over the expressions §34.5.3.1
// and §34.5.15.1 define rather than over any written by hand: the region the
// word opened is encrypted, the envelope produced in its place is handed back
// to the same directive handler with the author's key, and the design arrives
// at the step after the preprocessor with none of the envelope left in it.
//
// This is what the spelling of the word decides. Nothing else in the input
// says which lines are to be protected.
TEST(ProtectBeginSyntax, ARegionTheWordOpenedComesBackUnderTheAuthorsKey) {
  std::string written = EncryptedByTheAuthor(
      "`pragma protect begin\n"
      "  initial result = 42;\n"
      "`pragma protect end\n");
  ReadSource run(written, kExchangeKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, "initial result = 42;"));
  EXPECT_FALSE(Holds(run.text, "data_block"));
}

// ---------------------------------------------------------------------------
// A pragma_value written against the word.
// ---------------------------------------------------------------------------

// The closest input the rule has to turn away: the reserved word, written in
// the other spelling §22.5.1 allows a pragma expression. The definition covers
// the word alone, so this is not that expression -- it is reported, and no
// envelope opens on it.
//
// The value here carries text of its own. Which text it carries is not an
// input to this rule, which is defined on whether a value was written at all,
// so the number and identifier forms reach it as this one does and are not
// written out again below.
TEST(ProtectBeginSyntax, AStringWrittenAgainstTheWordIsReported) {
  ReadSource run("`pragma protect begin=\"now\"\n");
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma begin keyword is written on its own and takes no "
      "pragma_value",
      1, "34.5.1.1"));
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 0U);
}

// The value form that does carry a different input: a parenthesized list of
// further expressions, which leaves no text on the keyword at all. This is the
// one writing the rule cannot be told from the bare word by looking at what
// the value says, so it is the pair to the test above rather than a repeat of
// it.
TEST(ProtectBeginSyntax, AParenthesizedValueAgainstTheWordIsReported) {
  ReadSource run("`pragma protect begin=(enctype=\"raw\")\n");
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma begin keyword is written on its own and takes no "
      "pragma_value",
      1, "34.5.1.1"));
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 0U);
}

// The rejection does not stop the reading, and it does not spread: the
// directive after the reported one is read as it stands, the word on it opens
// its envelope, and it is the one directive that was wrong that was reported.
TEST(ProtectBeginSyntax, AWordWrittenProperlyAfterAReportedOneStillOpens) {
  ReadSource run(
      "`pragma protect begin=\"now\"\n"
      "`pragma protect begin\n");
  EXPECT_EQ(run.diag.ErrorCount(), 1U);
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 1U);
}

// The same input read by the encrypting half. A word written with a value
// delimits nothing there either, so the lines it stands among are text no
// envelope contains and come back exactly as they were written, with no region
// recorded anywhere.
TEST(ProtectBeginSyntax, TheValuedWordDelimitsNothingForTheEncryptingHalf) {
  std::string src =
      "`pragma protect begin=\"now\"\n"
      "  initial result = 42;\n"
      "`pragma protect end\n";
  std::string written = EncryptedByTheAuthor(src);
  EXPECT_EQ(written, src);
  EXPECT_FALSE(Holds(written, "data_block"));
}

// The parenthesized value read by the encrypting half, which is the pairing
// the test above makes at the other reader. That half steps over a value
// written in parentheses whole, so the letters of this value reach none of the
// code the quoted one's do, and the word ahead of it has to be turned away on
// its own account rather than on the other's.
TEST(ProtectBeginSyntax, AParenthesizedValueDelimitsNothingWhenEncrypting) {
  std::string src =
      "`pragma protect begin=(enctype=\"raw\")\n"
      "  initial result = 42;\n"
      "`pragma protect end\n";
  EXPECT_EQ(EncryptedByTheAuthor(src), src);
}

// A directive whose expression list opens with an '=' has no name ahead of it,
// so it names no expression at all and this word least of all. The line
// delimits nothing and is carried across as the text it is.
TEST(ProtectBeginSyntax, ADirectiveWithNoWordAheadOfItsValueDelimitsNothing) {
  std::string src =
      "`pragma protect =\"now\"\n"
      "  initial result = 42;\n"
      "`pragma protect end\n";
  EXPECT_EQ(EncryptedByTheAuthor(src), src);
}

// The negative form of the round trip, and what the rule is guarding. A word
// written with a value opened no region, so the encrypting half had nothing to
// replace: the design the author meant to seal stands in the produced text as
// the cleartext it always was, and reading that text back hands it on
// unprotected and reports the word that failed to seal it.
TEST(ProtectBeginSyntax, AValuedWordLeavesTheDesignUnprotectedEndToEnd) {
  std::string written = EncryptedByTheAuthor(
      "`pragma protect begin=\"now\"\n"
      "  initial result = 42;\n"
      "`pragma protect end\n");
  ReadSource run(written, kExchangeKey);
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma begin keyword is written on its own and takes no "
      "pragma_value",
      LineHolding(written, "begin=\"now\""), "34.5.1.1"));
  EXPECT_TRUE(Holds(run.text, "initial result = 42;"));
}

// ---------------------------------------------------------------------------
// Words that are not this word.
// ---------------------------------------------------------------------------

// A pragma_keyword is a simple identifier, so the same letters written as an
// escaped identifier name something else. Nothing opens on it, and nothing is
// wrong with it either: it is a legal pragma_value that this specification has
// no keyword for.
TEST(ProtectBeginSyntax, TheLettersAsAnEscapedIdentifierAreNotTheWord) {
  ReadSource run("`pragma protect \\begin\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 0U);
}

// SystemVerilog distinguishes case, so the word written in another case is a
// different word and opens nothing.
TEST(ProtectBeginSyntax, TheWordInAnotherCaseIsNotTheWord) {
  ReadSource run("`pragma protect BEGIN\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 0U);
}

// The reserved word that starts with the same letters is the one §34.5.3.1
// defines, and it opens an envelope for the other mode of processing. Reading
// the word as a prefix rather than as a whole name would open an envelope for
// this mode here as well.
TEST(ProtectBeginSyntax, ALongerReservedNameSharingItsLettersIsNotTheWord) {
  ReadSource run("`pragma protect begin_protected\n");
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 0U);
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 1U);
}

// The letters standing on the right of an '=' are a pragma_value of the
// keyword written on its left, not a pragma_keyword of the list. The word only
// opens an envelope where it names an expression of its own.
TEST(ProtectBeginSyntax, TheWordWrittenAsAValueOpensNothing) {
  ReadSource run("`pragma protect author=begin\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 0U);
}

// The word is a keyword of the protect pragma, which is the specification the
// pragma_name selects. Written under another pragma_name it asks a
// specification this implementation does not recognize for something, and
// leaves the protected envelopes of the text alone.
TEST(ProtectBeginSyntax, TheWordUnderAnotherPragmaNameOpensNothing) {
  ReadSource run("`pragma acme begin\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 0U);
}

// The other position the word can be written in on a directive of this shape:
// the pragma_name itself. There it names a specification rather than asking
// one for something, and the specification it names is not the one protected
// envelopes belong to, so nothing opens and nothing is wrong.
TEST(ProtectBeginSyntax, TheWordAsThePragmaNameOpensNothing) {
  ReadSource run("`pragma begin\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 0U);
}

// A pragma_value may itself be a list of pragma expressions, and the word
// written inside one belongs to that list rather than to the directive's own.
// It qualifies the value of the keyword carrying it, so it names no expression
// of the directive and opens nothing -- the same conclusion as the word
// standing on the right of an '=', reached by a different reading.
TEST(ProtectBeginSyntax, TheWordInsideAParenthesizedValueOpensNothing) {
  ReadSource run("`pragma protect encoding=(begin)\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 0U);
}

// The same nesting read by the encrypting half, which steps over a
// parenthesized value whole rather than walking into it. Two separate readings
// have to reach the same conclusion about where the word counts, and either
// one could come to it alone.
TEST(ProtectBeginSyntax, TheWordInsideAParenthesizedValueDelimitsNothing) {
  std::string src =
      "`pragma protect encoding=(begin)\n"
      "  initial result = 42;\n"
      "`pragma protect end\n";
  EXPECT_EQ(EncryptedByTheAuthor(src), src);
}

}  // namespace
