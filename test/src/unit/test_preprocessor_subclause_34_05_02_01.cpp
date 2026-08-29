// §34.5.2.1 Syntax, for the protect pragma keyword that closes an encryption
// envelope.
//
// The subclause is a syntax block holding one line, and what that line settles
// is the spelling of the expression:
//
//   The keyword is written as the word by itself.
//
// §22.5.1 offers a pragma expression two spellings -- a pragma_keyword standing
// alone, and a pragma_keyword with a pragma_value written against it -- and
// other keywords of this same table are defined with the second of them, the
// one naming the author of an envelope among them. This one is defined with
// the first, so a value written against the word leaves an expression the
// standard does not define: it closes no envelope, and it is not one of the
// other keywords either.
//
// A closing word that does not close is not the same failure as an opening word
// that does not open. The region the word was written for stays open, so the
// text the author wrote after it goes on being read as text of that region.
// That is why every reading below is carried past the word rather than stopped
// at it, and why the tests ask what became of the text on either side of it
// rather than only whether the word was complained of.
//
// The word is a pragma_keyword of the protect pragma, so it is reached through
// the `pragma directive of §22.5.1 carrying the pragma_name of §34.2, and what
// it closes has to have been opened first: §34.5.1.1's opening word is what
// every input here is built from, and §34.3.1's encrypting half is the second
// reader of the pair. Every input is therefore written as real directive syntax
// and read through the whole preprocessor rather than handed to the envelope
// state directly.
//
// All of it is preprocessor-stage. src/preprocessor/protect_envelope.cpp holds
// the word and the rule for what spells it, and two readings of a source text
// ask that rule the same question about different inputs:
// src/preprocessor/preprocessor_lines.cpp reads the directive's expressions out
// of its tokens and reports a word written with a value it is not defined with,
// while src/preprocessor/protect_processing.cpp finds the delimiters of a
// region on the encrypting side, over names that
// src/preprocessor/protect_pragma_line.cpp collects by walking a line's
// characters.
//
// Those two find their names by different means, so each spelling this word can
// be confused with is written twice below -- once for each reading. The pairs
// are not repetition: a name the one reading passes over and the other takes
// for this word would have an encrypting tool seal a region its author left
// open, and neither test alone would show it.

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

// A source text opening one encryption envelope, with `closing` written after
// it. The opening directive spells §34.5.1.1's word, which is what gives this
// subclause's word something to act on: a text that opened nothing would answer
// the same whichever way the closing word was spelled.
//
// The line between the two delimiters is design rather than filler. The tests
// on the encrypting side ask whether it went into a block or stayed in the
// clear, and a region holding nothing would answer neither way.
std::string RegionClosedWith(std::string_view closing) {
  std::string text = "`pragma protect begin\n";
  text.append("  initial result = 42;\n");
  text.append(closing);
  return text;
}

// ---------------------------------------------------------------------------
// The word standing on its own is the expression.
// ---------------------------------------------------------------------------

// The syntax block read at its plainest: the word written by itself as the
// whole expression list of a protect pragma directive closes the envelope the
// directive above it opened, and nothing about the directive is complained of.
//
// The envelope that comes back is the one defined for encryption rather than
// for decryption, which is the mode of the envelope this word closes and not of
// the one §34.5.4.1's word closes.
TEST(ProtectEndSyntax, TheWordAloneClosesTheEnvelopeThatWasOpen) {
  ReadSource run(RegionClosedWith("`pragma protect end\n"));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 0U);
  ASSERT_EQ(run.Closed().size(), 1U);
  EXPECT_EQ(run.Closed().front().mode, EnvelopeMode::kEncryption);
}

// A directive carrying the word is a directive like any other as far as the
// text leaving the preprocessor goes: it is consumed, and the source written
// around it arrives at the step after unchanged.
TEST(ProtectEndSyntax, TheDirectiveCarryingTheWordContributesNoText) {
  ReadSource run(
      "module secret;\n"
      "`pragma protect begin\n"
      "`pragma protect end\n"
      "endmodule\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(Holds(run.text, "pragma"));
  EXPECT_TRUE(Holds(run.text, "module secret;"));
  EXPECT_TRUE(Holds(run.text, "endmodule"));
}

// The word written last in a list whose earlier expressions are keywords
// defined with a value, which is the position §34.3.1's example writes the
// matching delimiter in. Each expression of a list is spelled on its own, so
// the word here is still the word standing alone and still closes what was
// open.
TEST(ProtectEndSyntax, TheWordLastAfterValuedExpressionsStillCloses) {
  std::string closing =
      "`pragma protect author=\"Acme Corp\", data_method=\"x-caesar\", end\n";
  ReadSource run(RegionClosedWith(closing));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 0U);
}

// The other order over the same list. A comma ends the expression before it, so
// a valued keyword written after the word qualifies neither the word nor the
// envelope's closing, and the word standing ahead of it is still the word
// standing alone.
TEST(ProtectEndSyntax, TheWordFirstAheadOfAValuedExpressionStillCloses) {
  std::string closing = "`pragma protect end, comment=\"above\"\n";
  ReadSource run(RegionClosedWith(closing));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 0U);
}

// The word as the whole of its own directive, with an expression describing the
// envelope written on the directive ahead of it. One expression list means the
// same thing however it is spread over directives, so the word closes here
// exactly as it does when it shares a directive with them.
TEST(ProtectEndSyntax, TheWordAloneOnItsOwnDirectiveStillCloses) {
  std::string closing = "`pragma protect comment=\"sealed\"\n";
  closing.append("`pragma protect end\n");
  ReadSource run(RegionClosedWith(closing));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 0U);
}

// The word need not be written in the source as the word: a directive's text is
// ordinary source text, so a macro usage in it is substituted before the pragma
// grammar reads it, and what the grammar then reads is the word.
TEST(ProtectEndSyntax, AMacroExpandingToTheWordClosesTheEnvelope) {
  std::string src = "`define CLOSE end\n";
  src.append(RegionClosedWith("`pragma protect `CLOSE\n"));
  ReadSource run(src);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 0U);
}

// A comment is not a pragma expression, so a directive whose word is followed
// by one carries the word alone and closes on it. Without this the word would
// have to be the last thing on its line to be the word.
TEST(ProtectEndSyntax, ACommentAfterTheWordLeavesItStandingAlone) {
  std::string closing = "`pragma protect end // the region stops here\n";
  ReadSource run(RegionClosedWith(closing));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 0U);
}

// The second reader of the same word, on the encrypting side. The region the
// pair delimits is replaced by an envelope for the other mode of processing,
// and it is this word that gives that half somewhere to stop reading: with no
// closing expression there is no region to replace.
TEST(ProtectEndSyntax, TheEncryptingHalfTakesTheWordAloneAsItsDelimiter) {
  std::string written =
      EncryptedByTheAuthor(RegionClosedWith("`pragma protect end\n"));
  EXPECT_TRUE(Holds(written, "`pragma protect end_protected\n"));
  // §34.5.15.1 spells the announcing keyword standing alone and §34.5.15.2
  // puts the block on the line after it, so the newline is what is looked for.
  EXPECT_TRUE(Holds(written, "`pragma protect data_block\n"));
  EXPECT_FALSE(Holds(written, "initial result = 42;"));
}

// Where the word stands is where the region stops. Text written after it is
// outside the region, so the encrypting half leaves that text in the clear
// while the text written ahead of it goes into the block.
//
// This is the claim the spelling carries that no count of open envelopes shows:
// the expression is read at the point it is written, so a design split by the
// word comes back half sealed and half readable.
TEST(ProtectEndSyntax, TheTextAfterTheWordIsOutsideTheRegionItClosed) {
  std::string src = RegionClosedWith("`pragma protect end\n");
  src.append("  initial published = 7;\n");
  std::string written = EncryptedByTheAuthor(src);
  EXPECT_FALSE(Holds(written, "initial result = 42;"));
  EXPECT_TRUE(Holds(written, "initial published = 7;"));
}

// The word driving both halves from end to end: the region it closed is
// encrypted, the envelope produced in its place is handed back to the same
// directive handler with the author's key, and the design arrives at the step
// after the preprocessor with none of the envelope left in it.
TEST(ProtectEndSyntax, ARegionTheWordClosedComesBackUnderTheAuthorsKey) {
  std::string written =
      EncryptedByTheAuthor(RegionClosedWith("`pragma protect end\n"));
  ReadSource run(written, kReadingExchangeKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, "initial result = 42;"));
  EXPECT_FALSE(Holds(run.text, "data_block"));
}

// ---------------------------------------------------------------------------
// A pragma_value written against the word.
// ---------------------------------------------------------------------------

// The closest input the rule has to turn away: the reserved word, written in
// the other spelling §22.5.1 allows a pragma expression. The definition covers
// the word alone, so this is not that expression -- it is reported, and the
// envelope it was written for is left open.
//
// The value here carries text of its own. Which text it carries is not an input
// to this rule, which is defined on whether a value was written at all, so the
// number and identifier forms reach it as this one does and are not written out
// again below.
TEST(ProtectEndSyntax, AStringWrittenAgainstTheWordIsReported) {
  std::string closing = "`pragma protect end=\"now\"\n";
  ReadSource run(RegionClosedWith(closing));
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma end keyword is written on its own and takes no "
      "pragma_value",
      3, "34.5.2.1"));
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 1U);
  EXPECT_TRUE(run.Closed().empty());
}

// The value form that does carry a different input: a parenthesized list of
// further expressions, which leaves no text on the keyword at all. This is the
// one writing the rule cannot be told from the bare word by looking at what the
// value says, so it is the pair to the test above rather than a repeat of it.
TEST(ProtectEndSyntax, AParenthesizedValueAgainstTheWordIsReported) {
  std::string closing = "`pragma protect end=(enctype=\"raw\")\n";
  ReadSource run(RegionClosedWith(closing));
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma end keyword is written on its own and takes no "
      "pragma_value",
      3, "34.5.2.1"));
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 1U);
}

// The rejection does not stop the reading, and it does not spread: the
// directive after the reported one is read as it stands, the word on it closes
// the region that is still open, and it is the one directive that was wrong
// that was reported.
TEST(ProtectEndSyntax, AWordWrittenProperlyAfterAReportedOneStillCloses) {
  std::string closing = "`pragma protect end=\"now\"\n";
  closing.append("`pragma protect end\n");
  ReadSource run(RegionClosedWith(closing));
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma end keyword is written on its own and takes no "
      "pragma_value",
      3, "34.5.2.1"));
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 0U);
  EXPECT_EQ(run.Closed().size(), 1U);
}

// The same input read by the encrypting half. A word written with a value ends
// nothing there either, so the region runs to the end of the text and there is
// no closed region to replace: the lines come back exactly as they were
// written, with no envelope recorded anywhere.
TEST(ProtectEndSyntax, TheValuedWordDelimitsNothingForTheEncryptingHalf) {
  std::string src = RegionClosedWith("`pragma protect end=\"now\"\n");
  std::string written = EncryptedByTheAuthor(src);
  EXPECT_EQ(written, src);
  EXPECT_FALSE(Holds(written, "data_block"));
}

// The parenthesized value read by the encrypting half, which is the pairing the
// test above makes at the other reader. That half steps over a value written in
// parentheses whole, so the letters of this value reach none of the code the
// quoted one's do, and the word ahead of it has to be turned away on its own
// account rather than on the other's.
TEST(ProtectEndSyntax, AParenthesizedValueDelimitsNothingWhenEncrypting) {
  std::string closing = "`pragma protect end=(enctype=\"raw\")\n";
  std::string src = RegionClosedWith(closing);
  EXPECT_EQ(EncryptedByTheAuthor(src), src);
}

// Which of two candidate lines the encrypting half stops the region at, put
// directly. The valued word does not end it, so the line carrying that word is
// text of the region like any other and travels into the block; the bare word
// below it is where the region really stops.
TEST(ProtectEndSyntax, AValuedWordIsEncryptedAsTextOfTheRegionItLeftOpen) {
  std::string closing = "`pragma protect end=\"now\"\n";
  closing.append("`pragma protect end\n");
  std::string written = EncryptedByTheAuthor(RegionClosedWith(closing));
  EXPECT_TRUE(Holds(written, "`pragma protect data_block\n"));
  EXPECT_FALSE(Holds(written, "end=\"now\""));
}

// The negative form of the round trip, and what the rule is guarding. A word
// written with a value closed no region, so the encrypting half had nothing to
// replace: the design the author meant to seal stands in the produced text as
// the cleartext it always was, and reading that text back hands it on
// unprotected and reports the word that failed to seal it.
TEST(ProtectEndSyntax, AValuedWordLeavesTheDesignUnprotectedEndToEnd) {
  std::string closing = "`pragma protect end=\"now\"\n";
  std::string written = EncryptedByTheAuthor(RegionClosedWith(closing));
  ReadSource run(written, kReadingExchangeKey);
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma end keyword is written on its own and takes no "
      "pragma_value",
      LineHolding(written, "end=\"now\""), "34.5.2.1"));
  EXPECT_TRUE(Holds(run.text, "initial result = 42;"));
}

// ---------------------------------------------------------------------------
// Words that are not this word.
// ---------------------------------------------------------------------------

// A pragma_keyword is a simple identifier, so the same letters written as an
// escaped identifier name something else. Nothing closes on it, and nothing is
// wrong with it either: it is a legal pragma_value that this specification has
// no keyword for.
TEST(ProtectEndSyntax, TheLettersAsAnEscapedIdentifierAreNotTheWord) {
  ReadSource run(RegionClosedWith("`pragma protect \\end\n"));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 1U);
}

// The same letters read by the encrypting half, which finds the names on a
// line by walking its characters rather than by reading the directive's tokens.
// A walk that stepped over the backslash alone would find this word standing
// where the other reading finds a value, and would seal a region the author
// never closed -- writing out a delimiter with a backslash still in front of it
// that nothing can read back.
TEST(ProtectEndSyntax, TheLettersAsAnEscapedIdentifierDelimitNothing) {
  std::string src = RegionClosedWith("`pragma protect \\end\n");
  std::string written = EncryptedByTheAuthor(src);
  EXPECT_EQ(written, src);
  EXPECT_FALSE(Holds(written, "end_protected"));
}

// SystemVerilog distinguishes case, so the word written in another case is a
// different word and closes nothing.
TEST(ProtectEndSyntax, TheWordInAnotherCaseIsNotTheWord) {
  ReadSource run(RegionClosedWith("`pragma protect END\n"));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 1U);
}

// The same at the encrypting half, which compares the name it scanned against
// the word rather than folding either one's case first.
TEST(ProtectEndSyntax, TheWordInAnotherCaseDelimitsNothing) {
  std::string src = RegionClosedWith("`pragma protect END\n");
  EXPECT_EQ(EncryptedByTheAuthor(src), src);
}

// The reserved word that starts with the same letters is the one §34.5.4.1
// defines, and it closes an envelope of the other mode of processing. Reading
// the word as a prefix rather than as a whole name would close this mode's
// envelope here as well.
TEST(ProtectEndSyntax, ALongerReservedNameSharingItsLettersIsNotTheWord) {
  ReadSource run(RegionClosedWith("`pragma protect end_protected\n"));
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 1U);
  EXPECT_TRUE(run.Closed().empty());
}

// The same at the encrypting half, whose walk collects a name by running to the
// end of its letters. Stopping that walk at the length of this word would leave
// the longer name looking exactly like it.
TEST(ProtectEndSyntax, ALongerReservedNameSharingItsLettersDelimitsNothing) {
  std::string src = RegionClosedWith("`pragma protect end_protected\n");
  EXPECT_EQ(EncryptedByTheAuthor(src), src);
}

// The letters standing on the right of an '=' are a pragma_value of the keyword
// written on its left, not a pragma_keyword of the list. The word only closes
// an envelope where it names an expression of its own.
TEST(ProtectEndSyntax, TheWordWrittenAsAValueClosesNothing) {
  ReadSource run(RegionClosedWith("`pragma protect comment=end\n"));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 1U);
}

// The same at the encrypting half. Its walk meets the two names one after the
// other and has to carry, from the '=' to the letters after it, the fact that
// what it is reading is a value; a walk that forgot would find this word here.
TEST(ProtectEndSyntax, TheWordWrittenAsAValueDelimitsNothing) {
  std::string src = RegionClosedWith("`pragma protect comment=end\n");
  EXPECT_EQ(EncryptedByTheAuthor(src), src);
}

// The word is a keyword of the protect pragma, which is the specification the
// pragma_name selects. Written under another pragma_name it asks a
// specification this implementation does not recognize for something, and
// leaves the protected envelopes of the text alone.
TEST(ProtectEndSyntax, TheWordUnderAnotherPragmaNameClosesNothing) {
  ReadSource run(RegionClosedWith("`pragma acme end\n"));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 1U);
}

// The same at the encrypting half, which decides whether a line is worth
// reading for names at all by the pragma_name on it. A half that searched every
// directive for the word would take this one as the end of the region.
//
// The word standing in the pragma_name slot instead is turned away by this very
// check, before any name is looked for, so this reader answers that spelling
// here rather than in a case of its own. The word is written in the body
// position on purpose: that is where this reader does look, which makes it the
// spelling that would slip through.
TEST(ProtectEndSyntax, TheWordUnderAnotherPragmaNameDelimitsNothing) {
  std::string src = RegionClosedWith("`pragma acme end\n");
  EXPECT_EQ(EncryptedByTheAuthor(src), src);
}

// The other position the word can be written in on a directive of this shape:
// the pragma_name itself. There it names a specification rather than asking one
// for something, and the specification it names is not the one protected
// envelopes belong to, so nothing closes and nothing is wrong.
TEST(ProtectEndSyntax, TheWordAsThePragmaNameClosesNothing) {
  ReadSource run(RegionClosedWith("`pragma end\n"));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 1U);
}

// A pragma_value may itself be a list of pragma expressions, and the word
// written inside one belongs to that list rather than to the directive's own.
// It qualifies the value of the keyword carrying it, so it names no expression
// of the directive and closes nothing -- the same conclusion as the word
// standing on the right of an '=', reached by a different reading.
TEST(ProtectEndSyntax, TheWordInsideAParenthesizedValueClosesNothing) {
  ReadSource run(RegionClosedWith("`pragma protect encoding=(end)\n"));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 1U);
}

// The same nesting read by the encrypting half, which steps over a
// parenthesized value whole rather than walking into it. Two separate readings
// have to reach the same conclusion about where the word counts, and either one
// could come to it alone.
TEST(ProtectEndSyntax, TheWordInsideAParenthesizedValueDelimitsNothing) {
  std::string src = RegionClosedWith("`pragma protect encoding=(end)\n");
  EXPECT_EQ(EncryptedByTheAuthor(src), src);
}

}  // namespace
