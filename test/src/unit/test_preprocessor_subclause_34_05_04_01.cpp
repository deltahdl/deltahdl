// §34.5.4.1 Syntax, for the protect pragma keyword that closes a region of text
// that was encrypted already.
//
// The subclause is a syntax block holding one line, and what that line settles
// is the spelling of the expression:
//
//   The keyword is written as the word by itself.
//
// §22.5.1 offers a pragma expression two spellings -- a pragma_keyword standing
// alone, and a pragma_keyword with a pragma_value written against it -- and
// other keywords of this same table are defined with the second of them, the
// one naming the author of an envelope among them. This one is defined with the
// first, so a value written against the word leaves an expression the standard
// does not define: it closes no region, and it is not one of the other keywords
// either.
//
// What turns on the spelling is where somebody else's text stops being theirs.
// The word marks the point past which the reading is out of a sealed model
// again, so the expressions written after it describe the reading now in
// process rather than that model, and the text written after it is the design
// around the model rather than more of it. A word that fails to mark the point
// therefore does not merely leave a region open -- it hands every later line to
// whichever processing is running as though somebody else had written it, which
// is why every reading below is carried past the word and asked what became of
// the text on either side of it rather than only whether the word was
// complained of.
//
// The word is a pragma_keyword of the protect pragma, so it is reached through
// the `pragma directive of §22.5.1 carrying the pragma_name of §34.2, and what
// it closes has to have been opened first: §34.5.3.1's word is what every input
// here is built from. §34.5.1.1's and §34.5.2.1's pair delimits the encryption
// region that an already-sealed model is written inside of, and §34.3's
// encrypting half is what reads that arrangement. §34.5.5.1's author expression
// is what a design says about itself, and it is the expression these tests
// watch to see which encryption a description was read as belonging to.
// §34.5.9.1's parenthesized encoding value states the writing an envelope's
// block is under, so an envelope this word closes can be one that could not be
// read at all had the statement gone unread. Every input is written as real
// directive syntax and read through the whole preprocessor, or produced by the
// encrypting half from real directive syntax, rather than handed to the
// envelope state directly.
//
// All of it is preprocessor-stage. src/preprocessor/protect_envelope.cpp holds
// the word and the rule for what spells it, and two readings of a source text
// ask that rule the same question about different inputs:
// src/preprocessor/preprocessor_protect_keys.cpp reads the directive's
// expressions out of its tokens and reports a word written with a value it is
// not defined with, while src/preprocessor/protect_processing.cpp finds where
// an already-sealed model stops on the encrypting side, over names that
// src/preprocessor/protect_pragma_line.cpp collects by walking a line's
// characters.
//
// Those two find their names by different means, so each spelling this word can
// be confused with is written twice below -- once for each reading. The pairs
// are not repetition: a name the one reading takes for this word and the other
// passes over would have an encrypting tool go on reading its own author's
// design as somebody else's sealed model, and neither test alone would show it.

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
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

// A source text opening one decryption envelope, with `closing` written after
// it. The opening directive spells §34.5.3.1's word, which is what gives this
// subclause's word something to act on: a text that opened nothing would answer
// the same whichever way the closing word was spelled.
std::string RegionClosedWith(std::string_view closing) {
  std::string text = "`pragma protect begin_protected\n";
  text.append(closing);
  return text;
}

// The design an author would seal, written as the region §34.5.1.1 and
// §34.5.2.1 delimit. The line between the two delimiters is what the encrypting
// half has to have something to put in a block, and what a reading of the
// produced envelope has to have something to get back.
std::string Design() {
  std::string text = "`pragma protect begin\n";
  text.append("  initial result = 42;\n");
  text.append("`pragma protect end\n");
  return text;
}

// The same design, with the coding scheme its block is to be written in stated
// inside the region in the spelling §34.5.9.1 defines: the keyword with a
// parenthesized list of subkeywords written against it.
//
// The scheme is one the table sets aside rather than this implementation's own,
// so an envelope formed from this states something the default states nothing
// about, and a reading of that envelope has to have taken the statement in to
// get the design back. That is what makes this an input built from the
// dependency's real syntax rather than a second spelling of the plain region
// above: the word under test closes an envelope whose block is unreadable
// except under a scheme the source named.
std::string DesignUnderDeclaredEncoding() {
  std::string text = "`pragma protect begin\n";
  text.append("`pragma protect encoding=(enctype=\"base64\")\n");
  text.append("  initial result = 42;\n");
  text.append("`pragma protect end\n");
  return text;
}

// The closing directive of a produced envelope, written in the other spelling
// §22.5.1 allows. A decryption envelope cannot be written out by hand -- what
// its block holds depends on the key the region was sealed under -- so the one
// spelling under test is put into a real produced envelope rather than a text
// standing in for one. A text the encrypting half wrote no closing word into
// comes back as it stands, and the expectations of whichever test asked for the
// substitution then fail on the envelope that was never altered.
std::string WithValuedClosingWord(const std::string& written) {
  constexpr std::string_view kClosing = "`pragma protect end_protected\n";
  constexpr std::string_view kValued = "`pragma protect end_protected=\"1\"\n";
  size_t at = written.find(kClosing);
  if (at == std::string::npos) return written;
  std::string valued(written);
  valued.replace(at, kClosing.size(), kValued);
  return valued;
}

// A block written in the clear, as a tool reading a text would meet one. It is
// not the block of anything: what it says is deliberately not a value any
// coding scheme writes, so a reading that took it for an envelope's block would
// have to say so, and one that left it alone has nothing to say about it.
constexpr std::string_view kStrayBlockDirective =
    "`pragma protect data_block=\"not a block at all\"\n";

// An encryption region holding a model that some earlier encryption sealed
// already, whose closing directive is written as `closing`.
//
// The lines standing on either side of that directive are what make the
// arrangement readable in the produced text. Ahead of it, inside the sealed
// model, stands a name belonging to whoever wrote that model rather than to the
// encryption now running. Past it stands the design's own author, and a block
// written in the clear -- which §34.5.15 makes an error exactly where no
// already-sealed model encloses it, and so reports on where the word did its
// work and stays silent where it did not.
std::string RegionAroundSealedModel(std::string_view closing) {
  std::string text = "`pragma protect begin\n";
  text.append("  initial result = 42;\n");
  text.append("`pragma protect begin_protected\n");
  text.append("`pragma protect author=\"Other Corp\"\n");
  text.append(closing);
  text.append("`pragma protect author=\"Acme Corp\"\n");
  text.append(kStrayBlockDirective);
  text.append("`pragma protect end\n");
  return text;
}

// The same arrangement with a second already-sealed model written inside the
// first, which §34.5.1 allows: the inner one is bytes of the outer like
// everything else it holds.
//
// Two of this word stand in it, and the two names they are separated by are
// what tell them apart in the produced text. The name written between the two
// closing directives is still inside the outer model, so it belongs to whoever
// sealed that model; the name written past the outer one belongs to the design
// being encrypted now. A reading that paired the words differently swaps which
// of the two the envelope carries in the clear.
std::string RegionAroundNestedSealedModels() {
  std::string text = "`pragma protect begin\n";
  text.append("  initial result = 42;\n");
  text.append("`pragma protect begin_protected\n");
  text.append("`pragma protect begin_protected\n");
  text.append("`pragma protect end_protected\n");
  text.append("`pragma protect author=\"Other Corp\"\n");
  text.append("`pragma protect end_protected\n");
  text.append("`pragma protect author=\"Acme Corp\"\n");
  text.append("`pragma protect end\n");
  return text;
}

// ---------------------------------------------------------------------------
// The word standing on its own is the expression.
// ---------------------------------------------------------------------------

// The syntax block read at its plainest: the word written by itself as the
// whole expression list of a protect pragma directive closes the envelope the
// directive above it opened, and nothing about the directive is complained of.
//
// The envelope that comes back is the one defined for decryption rather than
// for encryption, which is the mode this word closes and not the mode
// §34.5.2.1's word closes.
TEST(ProtectEndProtectedSyntax, TheWordAloneClosesTheEnvelopeThatWasOpen) {
  ReadSource run(RegionClosedWith("`pragma protect end_protected\n"));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
  ASSERT_EQ(run.Closed().size(), 1U);
  EXPECT_EQ(run.Closed().front().mode, EnvelopeMode::kDecryption);
}

// A directive carrying the word is a directive like any other as far as the
// text leaving the preprocessor goes: it is consumed, and the source written
// around it arrives at the step after unchanged.
TEST(ProtectEndProtectedSyntax, TheDirectiveCarryingTheWordContributesNoText) {
  ReadSource run(
      "module sealed;\n"
      "`pragma protect begin_protected\n"
      "`pragma protect end_protected\n"
      "endmodule\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(Holds(run.text, "pragma"));
  EXPECT_TRUE(Holds(run.text, "module sealed;"));
  EXPECT_TRUE(Holds(run.text, "endmodule"));
}

// Which envelope the word answers, where one of each mode stands open. It is
// the mode of the word §34.5.3.1 defines, so a region marked for encryption
// that encloses this one is left open: an expression closing the wrong mode's
// region would leave the reading protected where the text says it is not, or in
// the clear where the text says it is.
TEST(ProtectEndProtectedSyntax, TheWordLeavesTheOtherModesEnvelopeOpen) {
  ReadSource run(
      "`pragma protect begin\n"
      "`pragma protect begin_protected\n"
      "`pragma protect end_protected\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 1U);
}

// The word written last in a list whose earlier expressions are keywords
// defined with a value, which is the position §34.3's produced envelope writes
// its describing expressions in. Each expression of a list is spelled on its
// own, so the word here is still the word standing alone and still closes what
// was open.
TEST(ProtectEndProtectedSyntax, TheWordLastAfterValuedExpressionsStillCloses) {
  std::string closing =
      "`pragma protect author=\"Acme Corp\", data_method=\"x-caesar\", "
      "end_protected\n";
  ReadSource run(RegionClosedWith(closing));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
}

// The other order over the same list. A comma ends the expression before it, so
// a valued keyword written after the word qualifies neither the word nor the
// envelope's closing, and the word standing ahead of it is still the word
// standing alone.
TEST(ProtectEndProtectedSyntax,
     TheWordFirstAheadOfAValuedExpressionStillCloses) {
  ReadSource run(
      RegionClosedWith("`pragma protect end_protected, comment=\"done\"\n"));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
}

// The word as the whole of its own directive, with an expression describing the
// envelope written on the directive ahead of it. One expression list means the
// same thing however it is spread over directives, so the word closes here
// exactly as it does when it shares a directive with them.
TEST(ProtectEndProtectedSyntax, TheWordAloneOnItsOwnDirectiveStillCloses) {
  std::string closing = "`pragma protect comment=\"sealed\"\n";
  closing.append("`pragma protect end_protected\n");
  ReadSource run(RegionClosedWith(closing));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
}

// The word need not be written in the source as the word: a directive's text is
// ordinary source text, so a macro usage in it is substituted before the pragma
// grammar reads it, and what the grammar then reads is the word.
TEST(ProtectEndProtectedSyntax, AMacroExpandingToTheWordClosesTheEnvelope) {
  std::string src = "`define CLOSE end_protected\n";
  src.append(RegionClosedWith("`pragma protect `CLOSE\n"));
  ReadSource run(src);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
}

// A comment is not a pragma expression, so a directive whose word is followed
// by one carries the word alone and closes on it. Without this the word would
// have to be the last thing on its line to be the word.
TEST(ProtectEndProtectedSyntax, ACommentAfterTheWordLeavesItStandingAlone) {
  ReadSource run(RegionClosedWith(
      "`pragma protect end_protected // sealed model ends here\n"));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
}

// The word written where two envelopes of its own mode stand open. §34.2 has
// such envelopes nest, so this is a position the word is written in rather than
// a spelling of it, and one word answers one opening word.
TEST(ProtectEndProtectedSyntax, TheWordClosesOneOfTwoNestedEnvelopes) {
  ReadSource run(
      "`pragma protect begin_protected\n"
      "`pragma protect begin_protected\n"
      "`pragma protect end_protected\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 1U);
  EXPECT_EQ(run.Closed().size(), 1U);
}

// Where the word stands is where protected text stops, which is the claim no
// count of closed envelopes shows on its own. A block written in the clear past
// the envelope is a block of nothing: outside every region there is no envelope
// for it to have come out of and no key it could be read under, so the reading
// leaves it alone rather than trying it and reporting what it found.
TEST(ProtectEndProtectedSyntax, TextAfterTheWordIsOutsideTheRegionItClosed) {
  std::string src = EncryptedByTheAuthor(Design());
  src.append(kStrayBlockDirective);
  ReadSource run(src, kExchangeKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.Protected());
}

// The word driving the reading from end to end: a region an author sealed with
// the key below is closed by the word the encrypting half wrote, its block is
// read back under that key, and the design arrives at the step after the
// preprocessor with none of the envelope left in it.
TEST(ProtectEndProtectedSyntax, ARegionTheWordClosesComesBackUnderTheKey) {
  ReadSource run(EncryptedByTheAuthor(Design()), kExchangeKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, "initial result = 42;"));
  EXPECT_FALSE(Holds(run.text, "data_block"));
}

// The same reading over an envelope that states something about itself, built
// from §34.5.9.1's own syntax rather than from a default. The region names a
// coding scheme, the encrypting half writes the block in it and states it on
// the envelope, and the word ends the envelope a reading got the design back
// out of.
//
// The assertion on the produced text stands ahead of the reading on purpose: it
// is what says the scheme reached the envelope at all. Without it a run that
// silently fell back to this implementation's own writing would look exactly
// like a run that honored what the source stated, and the round trip would pass
// either way.
TEST(ProtectEndProtectedSyntax,
     ARegionUnderADeclaredEncodingComesBackThroughTheWord) {
  std::string written = EncryptedByTheAuthor(DesignUnderDeclaredEncoding());
  ASSERT_TRUE(Holds(written, "enctype=\"base64\""));
  ReadSource run(written, kExchangeKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, "initial result = 42;"));
  EXPECT_FALSE(run.Protected());
}

// ---------------------------------------------------------------------------
// The word read by the encrypting half.
// ---------------------------------------------------------------------------

// The second reader of the same word, which finds it by walking a line's
// characters rather than by reading a directive's tokens. §34.5.3 has the
// contents of an already-sealed model treated as input cleartext, and it is
// this word that tells that half where such a model stops: the block written
// past it belongs to no earlier envelope, which §34.5.15 makes an error, and
// that report is the reading saying it came back out of the sealed model here.
TEST(ProtectEndProtectedSyntax, TheWordAloneEndsASealedModelForEncrypting) {
  std::string src = RegionAroundSealedModel("`pragma protect end_protected\n");
  EncryptionRun run(src);
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(),
                            "data_block is written where no previously",
                            LineHolding(src, "data_block="), "34.5.15"));
}

// What that ending is worth in the produced text. The lines past the word are
// the design being encrypted, so the expression naming its author is read as
// this encryption's own description and written in the clear on the envelope
// standing in the region's place, while the design itself goes into the block.
TEST(ProtectEndProtectedSyntax, TheDesignPastTheWordIsThisEncryptionsOwn) {
  std::string written = EncryptedByTheAuthor(
      RegionAroundSealedModel("`pragma protect end_protected\n"));
  EXPECT_TRUE(Holds(written, "author=\"Acme Corp\""));
  EXPECT_FALSE(Holds(written, "not a block at all"));
  EXPECT_FALSE(Holds(written, "initial result = 42;"));
}

// The other half of what the word ends: the expressions written inside the
// sealed model describe that model, so none of them is read as description of
// the encryption now in process. The name written ahead of the word is not this
// design's author, and the word is what keeps it from being taken for one.
TEST(ProtectEndProtectedSyntax,
     TheSealedModelsDescriptionStopsWhereTheWordStands) {
  std::string written = EncryptedByTheAuthor(
      RegionAroundSealedModel("`pragma protect end_protected\n"));
  EXPECT_FALSE(Holds(written, "author=\"Other Corp\""));
}

// The word written last in a list whose earlier expressions are keywords
// defined with a value, read by this half rather than by the other. The two
// find their names by different means, so the position the word is written in
// is an input to each of them separately: this one walks a line's characters
// and has to carry, across the punctuation and the quoted text ahead of the
// word, the fact that what it is now reading names an expression of the list.
//
// A half that only found the word where it opened a directive's list would
// leave this model unended and go on reading the design past it as somebody
// else's sealed bytes.
TEST(ProtectEndProtectedSyntax, TheWordLastAfterValuedExpressionsEndsTheModel) {
  std::string src = RegionAroundSealedModel(
      "`pragma protect encrypt_agent=\"other-tool\", end_protected\n");
  EncryptionRun run(src);
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(),
                            "data_block is written where no previously",
                            LineHolding(src, "data_block="), "34.5.15"));
}

// The other order over the same list, at the same half. A comma ends the
// expression before it, so a valued keyword written after the word qualifies
// neither the word nor the model's ending, and the word standing ahead of it is
// still the word standing alone.
//
// This is the pair to the test above rather than a repeat of it: there the walk
// reaches the word having already stepped over a value, here it reaches a value
// having already taken the word, and only one of the two orders exercises the
// state a walk carries forward from an '='.
TEST(ProtectEndProtectedSyntax,
     TheWordFirstAheadOfAValuedExpressionEndsTheModel) {
  std::string src = RegionAroundSealedModel(
      "`pragma protect end_protected, comment=\"done\"\n");
  EncryptionRun run(src);
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(),
                            "data_block is written where no previously",
                            LineHolding(src, "data_block="), "34.5.15"));
}

// A comment is not a pragma expression here either, so a directive whose word
// is followed by one carries the word alone and ends the model on it. This half
// collects a name by running to the end of its identifier characters, so a walk
// that read the rest of the line as part of the expression list -- or that took
// the comment's own letters for names -- would come to a different answer from
// the reading of the same line at the other half.
TEST(ProtectEndProtectedSyntax,
     ACommentAfterTheWordLeavesItStandingAloneWhenEncrypting) {
  std::string src = RegionAroundSealedModel(
      "`pragma protect end_protected // that model ends here\n");
  EncryptionRun run(src);
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(),
                            "data_block is written where no previously",
                            LineHolding(src, "data_block="), "34.5.15"));
}

// The word where two already-sealed models stand one inside the other, each of
// them ended by a word of its own. Which model each word ended is what the two
// names on either side of the outer one show: the name written between the two
// closing directives describes the outer sealed model, and the name written
// past both is the design's own.
//
// Both failures the pairing can have show up here. A word that finished the
// outer model at the inner boundary hands the first name to the envelope being
// written now, publishing one author's name on another author's envelope; a
// word that finished nothing leaves the design's own name inside a sealed model
// still, so it goes into the block unread and the envelope says nothing about
// who wrote what it carries.
TEST(ProtectEndProtectedSyntax, TheInnerWordEndsOnlyTheInnerSealedModel) {
  std::string written = EncryptedByTheAuthor(RegionAroundNestedSealedModels());
  EXPECT_FALSE(Holds(written, "author=\"Other Corp\""));
  EXPECT_TRUE(Holds(written, "author=\"Acme Corp\""));
}

// ---------------------------------------------------------------------------
// A pragma_value written against the word.
// ---------------------------------------------------------------------------

// The closest input the rule has to turn away: the reserved word, written in
// the other spelling §22.5.1 allows a pragma expression. The definition covers
// the word alone, so this is not that expression -- it is reported, and the
// region it was written for is left open with the reading still inside
// protected code.
//
// The value here carries text of its own. Which text it carries is not an input
// to this rule, which is defined on whether a value was written at all, so the
// number and identifier forms reach it as this one does and are not written out
// again below.
TEST(ProtectEndProtectedSyntax, AStringWrittenAgainstTheWordIsReported) {
  ReadSource run(RegionClosedWith("`pragma protect end_protected=\"1\"\n"));
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma end_protected keyword is written on its own and takes "
      "no pragma_value",
      2, "34.5.4.1"));
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 1U);
  EXPECT_TRUE(run.Protected());
  EXPECT_TRUE(run.Closed().empty());
}

// The value form that does carry a different input: a parenthesized list of
// further expressions, which leaves no text on the keyword at all. This is the
// one writing the rule cannot be told from the bare word by looking at what the
// value says, so it is the pair to the test above rather than a repeat of it.
TEST(ProtectEndProtectedSyntax, AParenthesizedValueAgainstTheWordIsReported) {
  ReadSource run(
      RegionClosedWith("`pragma protect end_protected=(enctype=\"raw\")\n"));
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma end_protected keyword is written on its own and takes "
      "no pragma_value",
      2, "34.5.4.1"));
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 1U);
}

// A word turned away for its spelling is not quietly demoted to a keyword
// describing the content of the region it failed to close either. Nothing about
// the expression is put in effect, so the envelope left standing open holds
// nothing on its account.
TEST(ProtectEndProtectedSyntax,
     TheValuedWordDescribesNothingAboutTheOpenEnvelope) {
  ReadSource run(RegionClosedWith("`pragma protect end_protected=\"1\"\n"));
  ASSERT_EQ(run.Open().size(), 1U);
  EXPECT_TRUE(run.Open().front().content_keywords.empty());
}

// The rejection does not stop the reading, and it does not spread: the
// directive after the reported one is read as it stands, the word on it closes
// the region that is still open, and it is the one directive that was wrong
// that was reported.
TEST(ProtectEndProtectedSyntax, AWordWrittenProperlyAfterAReportedOneCloses) {
  std::string closing = "`pragma protect end_protected=\"1\"\n";
  closing.append("`pragma protect end_protected\n");
  ReadSource run(RegionClosedWith(closing));
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma end_protected keyword is written on its own and takes "
      "no pragma_value",
      2, "34.5.4.1"));
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
  EXPECT_EQ(run.Closed().size(), 1U);
}

// The negative form of the reading above, over a real envelope the encrypting
// half produced with only its closing word rewritten into the spelling the
// standard does not define. The region never ends, so the design written after
// the envelope is inside it: a block standing in the clear past the envelope is
// read as that envelope's own, which is text belonging to one author being
// opened as though it belonged to another.
TEST(ProtectEndProtectedSyntax, TextAfterAValuedWordIsStillReadAsProtected) {
  std::string src = WithValuedClosingWord(EncryptedByTheAuthor(Design()));
  src.append(kStrayBlockDirective);
  ReadSource run(src, kExchangeKey);
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma end_protected keyword is written on its own and takes "
      "no pragma_value",
      LineHolding(src, "end_protected="), "34.5.4.1"));
  EXPECT_TRUE(run.Protected());
}

// The same input read by the encrypting half. A word written with a value ends
// no already-sealed model there either, so the block written beneath it is
// inside one still -- nothing about it is reported, and the reading has gone on
// treating this author's own design as somebody else's sealed bytes.
TEST(ProtectEndProtectedSyntax, TheValuedWordEndsNoSealedModelWhenEncrypting) {
  EncryptionRun run(
      RegionAroundSealedModel("`pragma protect end_protected=\"1\"\n"));
  EXPECT_EQ(run.diag.ErrorCount(), 0U);
}

// The parenthesized value read by the encrypting half, which is the pairing the
// test above makes for the quoted one. This half steps over a value written in
// parentheses whole, so the letters inside it reach none of the code the quoted
// value's do, and the word ahead of it has to be turned away on its own account
// rather than on the quoted form's.
//
// The two halves settle the question by different means -- one looks ahead a
// token from the name, the other carries the fact of an '=' along a walk of the
// line's characters -- so a value form covered at one of them is not covered at
// the other.
TEST(ProtectEndProtectedSyntax,
     AParenthesizedValueEndsNoSealedModelWhenEncrypting) {
  EncryptionRun run(RegionAroundSealedModel(
      "`pragma protect end_protected=(enctype=\"raw\")\n"));
  EXPECT_EQ(run.diag.ErrorCount(), 0U);
}

// What the unended model costs the design around it, put directly. The sealed
// model runs to the end of the text, so the expression closing the encryption
// region is inside it as well and ends nothing: there is no region to replace,
// and the design the author meant to seal comes back from the encrypting half
// exactly as it was written, in the clear.
TEST(ProtectEndProtectedSyntax, TheValuedWordLeavesTheDesignUnsealedEndToEnd) {
  std::string src =
      RegionAroundSealedModel("`pragma protect end_protected=\"1\"\n");
  std::string written = EncryptedByTheAuthor(src);
  EXPECT_EQ(written, src);
  EXPECT_TRUE(Holds(written, "initial result = 42;"));
}

// ---------------------------------------------------------------------------
// Words that are not this word.
// ---------------------------------------------------------------------------

// A pragma_keyword is a simple identifier, so the same letters written as an
// escaped identifier name something else. Nothing closes on it, and nothing is
// wrong with it either: it is a legal pragma_value that this specification has
// no keyword for.
TEST(ProtectEndProtectedSyntax, TheLettersAsAnEscapedIdentifierAreNotTheWord) {
  ReadSource run(RegionClosedWith("`pragma protect \\end_protected\n"));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 1U);
}

// The same letters read by the encrypting half, whose walk would find this word
// standing where the other reading finds a value if it stepped over the
// backslash alone. It would then take the design written after it for its own
// rather than for the sealed model's, and read a name written there as this
// encryption's description of itself.
TEST(ProtectEndProtectedSyntax,
     TheLettersAsAnEscapedIdentifierEndNoSealedModel) {
  EncryptionRun run(
      RegionAroundSealedModel("`pragma protect \\end_protected\n"));
  EXPECT_EQ(run.diag.ErrorCount(), 0U);
}

// SystemVerilog distinguishes case, so the word written in another case is a
// different word and closes nothing.
TEST(ProtectEndProtectedSyntax, TheWordInAnotherCaseIsNotTheWord) {
  ReadSource run(RegionClosedWith("`pragma protect END_PROTECTED\n"));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 1U);
}

// The same at the encrypting half, which compares the name it scanned against
// the word rather than folding either one's case first.
TEST(ProtectEndProtectedSyntax, TheWordInAnotherCaseEndsNoSealedModel) {
  EncryptionRun run(RegionAroundSealedModel("`pragma protect END_PROTECTED\n"));
  EXPECT_EQ(run.diag.ErrorCount(), 0U);
}

// The reserved word that this one's opening letters spell is the one §34.5.2.1
// defines, and it closes an envelope of the other mode of processing. Reading a
// name by its opening letters rather than as a whole word would have this word
// close that mode's envelope, or that word close this mode's.
TEST(ProtectEndProtectedSyntax,
     AShorterReservedNameSharingItsLettersClosesTheOtherMode) {
  ReadSource run(
      "`pragma protect begin\n"
      "`pragma protect begin_protected\n"
      "`pragma protect end\n");
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 1U);
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 0U);
}

// The same at the encrypting half, whose walk collects a name by running to the
// end of its letters. Stopping that walk at the length of the shorter word
// would leave this one looking exactly like it, and a model somebody sealed
// already would be read as ending where the shorter word was written.
TEST(ProtectEndProtectedSyntax,
     AShorterReservedNameSharingItsLettersEndsNoSealedModel) {
  EncryptionRun run(RegionAroundSealedModel("`pragma protect end\n"));
  EXPECT_EQ(run.diag.ErrorCount(), 0U);
}

// The other direction of the same confusion, and the one no reserved word
// supplies: a name this word's whole spelling is the opening of. §34.5 sets
// aside no such name, so it is written here as an ordinary one, and it is a
// name of its own like any other identifier that happens to start this way.
//
// The shorter reserved word above cannot stand in for this. A reading that
// stopped at the end of the word it was looking for -- rather than at the end
// of the name the line wrote -- would answer that case correctly and this one
// wrongly, taking this line for the word and ending a region on a name the
// standard gives no meaning to.
TEST(ProtectEndProtectedSyntax, ALongerNameStartingWithTheWordIsNotTheWord) {
  ReadSource run(RegionClosedWith("`pragma protect end_protected_v2\n"));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 1U);
}

// The same at the encrypting half, whose walk collects a name by running to the
// end of its identifier characters and then compares the whole of it. Comparing
// only as far as the word's own length would leave this name looking exactly
// like the word.
TEST(ProtectEndProtectedSyntax,
     ALongerNameStartingWithTheWordEndsNoSealedModel) {
  EncryptionRun run(
      RegionAroundSealedModel("`pragma protect end_protected_v2\n"));
  EXPECT_EQ(run.diag.ErrorCount(), 0U);
}

// The letters standing on the right of an '=' are a pragma_value of the keyword
// written on its left, not a pragma_keyword of the list. The word only closes
// an envelope where it names an expression of its own.
TEST(ProtectEndProtectedSyntax, TheWordWrittenAsAValueClosesNothing) {
  ReadSource run(RegionClosedWith("`pragma protect comment=end_protected\n"));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 1U);
}

// The same at the encrypting half. Its walk meets the two names one after the
// other and has to carry, from the '=' to the letters after it, the fact that
// what it is reading is a value; a walk that forgot would find this word here.
TEST(ProtectEndProtectedSyntax, TheWordWrittenAsAValueEndsNoSealedModel) {
  EncryptionRun run(
      RegionAroundSealedModel("`pragma protect comment=end_protected\n"));
  EXPECT_EQ(run.diag.ErrorCount(), 0U);
}

// The word is a keyword of the protect pragma, which is the specification the
// pragma_name selects. Written under another pragma_name it asks a
// specification this implementation does not recognize for something, and
// leaves the protected envelopes of the text alone.
TEST(ProtectEndProtectedSyntax, TheWordUnderAnotherPragmaNameClosesNothing) {
  ReadSource run(RegionClosedWith("`pragma acme end_protected\n"));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 1U);
}

// The same at the encrypting half, which decides whether a line is worth
// reading for names at all by the pragma_name on it. A half that searched every
// directive for the word would take this one as the end of the sealed model.
//
// The word standing in the pragma_name slot instead is turned away by this very
// check, before any name is looked for, so this reader answers that spelling
// here rather than in a case of its own. The word is written in the body
// position on purpose: that is where this reader does look, which makes it the
// spelling that would slip through.
TEST(ProtectEndProtectedSyntax,
     TheWordUnderAnotherPragmaNameEndsNoSealedModel) {
  EncryptionRun run(RegionAroundSealedModel("`pragma acme end_protected\n"));
  EXPECT_EQ(run.diag.ErrorCount(), 0U);
}

// The other position the word can be written in on a directive of this shape:
// the pragma_name itself. There it names a specification rather than asking one
// for something, and the specification it names is not the one protected
// envelopes belong to, so nothing closes and nothing is wrong.
TEST(ProtectEndProtectedSyntax, TheWordAsThePragmaNameClosesNothing) {
  ReadSource run(RegionClosedWith("`pragma end_protected\n"));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 1U);
}

// The same arrangement driven through the encrypting half rather than argued
// from the test above it. That half decides whether a line is worth reading for
// names by the pragma_name on it, and the line here writes this word where that
// name belongs and nothing where the names belong.
//
// The line carrying a foreign pragma_name is not this input. There the check
// turns the line away because the name is one this specification knows nothing
// of; here it turns the line away because the name is not the protect pragma
// either, and the word the check is looking past is the very word the walk
// would otherwise be looking for. A check reading the name slot loosely would
// come to opposite answers on the two.
TEST(ProtectEndProtectedSyntax, TheWordAsThePragmaNameEndsNoSealedModel) {
  EncryptionRun run(RegionAroundSealedModel("`pragma end_protected\n"));
  EXPECT_EQ(run.diag.ErrorCount(), 0U);
}

// A pragma_value may itself be a list of pragma expressions, and the word
// written inside one belongs to that list rather than to the directive's own.
// It qualifies the value of the keyword carrying it, so it names no expression
// of the directive and closes nothing -- the same conclusion as the word
// standing on the right of an '=', reached by a different reading.
TEST(ProtectEndProtectedSyntax, TheWordInsideAParenthesizedValueClosesNothing) {
  ReadSource run(
      RegionClosedWith("`pragma protect encoding=(end_protected)\n"));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 1U);
}

// The same nesting read by the encrypting half, which steps over a
// parenthesized value whole rather than walking into it. Two separate readings
// have to reach the same conclusion about where the word counts, and either one
// could come to it alone.
TEST(ProtectEndProtectedSyntax,
     TheWordInsideAParenthesizedValueEndsNoSealedModel) {
  EncryptionRun run(
      RegionAroundSealedModel("`pragma protect encoding=(end_protected)\n"));
  EXPECT_EQ(run.diag.ErrorCount(), 0U);
}

}  // namespace
