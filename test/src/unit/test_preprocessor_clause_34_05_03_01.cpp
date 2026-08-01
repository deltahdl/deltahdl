// §34.5.3.1 Syntax, for the protect pragma keyword that opens a region of text
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
// does not define: it opens no region, and it is not one of the other keywords
// either.
//
// What turns on the spelling is which text belongs to whom. The word marks
// where a model somebody sealed earlier begins, and every reading of the text
// after it depends on the mark being there: the expressions written past the
// word describe that earlier model rather than the reading now in process, and
// the block written past it holds that model rather than nothing. A word that
// fails to mark the point therefore does not merely lose a region -- it hands
// somebody else's description of somebody else's envelope to whichever
// processing is running over the text, which is why every reading below is
// carried past the word rather than stopped at it.
//
// The word is a pragma_keyword of the protect pragma, so it is reached through
// the `pragma directive of §22.5.1 carrying the pragma_name of §34.2, and what
// it opens has to be closed by §34.5.4.1's word for there to be a region at
// all. §34.5.1.1's and §34.5.2.1's pair delimits the encryption region that an
// already-sealed model is written inside of, and §34.3's encrypting half is
// what reads that arrangement. §34.5.5.1's author expression is what a sealed
// model says about itself, and §34.5.9.1's parenthesized encoding value both
// supplies a valued spelling written beside the word and, in the round trip
// below, states the writing an envelope's block is under -- so an envelope this
// word opens can be one that could not be read at all had the statement gone
// unread. Every input is written as real directive syntax and read through the
// whole preprocessor, or produced by the encrypting half from real directive
// syntax, rather than handed to the envelope state directly.
//
// All of it is preprocessor-stage. src/preprocessor/protect_envelope.cpp holds
// the word and the rule for what spells it, and two readings of a source text
// ask that rule the same question about different inputs:
// src/preprocessor/preprocessor_protect_keys.cpp reads the directive's
// expressions out of its tokens and reports a word written with a value it is
// not defined with, while src/preprocessor/protect_processing.cpp finds an
// already-sealed model on the encrypting side, over names that
// src/preprocessor/protect_pragma_line.cpp collects by walking a line's
// characters.
//
// Those two find their names by different means, so each spelling this word can
// be confused with is written twice below -- once for each reading. The pairs
// are not repetition: a name the one reading passes over and the other takes
// for this word would have an encrypting tool treat a stretch of its own
// author's design as somebody else's sealed model, and neither test alone would
// show it.

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

// The key an author would hand the encrypting half, and hand back to a tool
// reading what it produced. Only the tests that read a produced envelope need
// one, and without a key nothing is sealed and nothing is opened, so those
// tests could not tell a word that opened no region from a key that was never
// supplied.
constexpr std::string_view kExchangeKey = "acme-exchange-key";

bool Holds(std::string_view text, std::string_view needle) {
  return text.find(needle) != std::string_view::npos;
}

// Envelope encryption over a source text, under the author's key.
std::string Encrypted(const std::string& src) {
  return EncryptEnvelopes(src, kExchangeKey);
}

// The same, with what the reading found in its input that the standard makes an
// error kept beside the text it produced. The transformation runs to the end of
// the input whatever it found, so the two are read together rather than one in
// place of the other.
struct EncryptionRun {
  ProtectEncryptionReport report;
  std::string text;

  explicit EncryptionRun(const std::string& src)
      : text(EncryptEnvelopes(src, kExchangeKey, ProtectKeyList(), &report)) {}
};

// A source text read through the preprocessor, with what the reading left
// behind kept beside it.
//
// Which envelopes a directive opened is state the preprocessor carries from one
// directive to the next rather than anything the output text shows, so the
// Preprocessor outlives the call and the text it produced is kept for the
// claims about what reaches the step after.
//
// `key` is the one the user supplies for reading protected regions back. Most
// of these tests are about which directives open a region and need none; the
// ones that read a produced envelope need the key it was formed under, or the
// region would stay sealed and its absence from the output would say nothing.
struct ReadSource {
  // What the reading is configured with, which is the key and nothing else.
  // It stands ahead of the constructor because the constructor's own member
  // initializer is what calls it.
  static PreprocConfig KeyConfig(std::string_view key) {
    PreprocConfig config;
    config.protect_key = std::string(key);
    return config;
  }

  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp;
  std::string text;

  explicit ReadSource(const std::string& src, std::string_view key = {})
      : pp(mgr, diag, KeyConfig(key)) {
    text = pp.Preprocess(mgr.AddFile("<test>", src));
  }

  // How many envelopes of the mode this word opens the reading still has open
  // where the text ends. This is what the word acts on, so a text writing
  // something that is not this expression says so here.
  size_t OpenDecryptionEnvelopes() const {
    return pp.ProtectEnvelopes().DecryptionEnvelopeDepth();
  }

  // The same for the other mode, which §34.5.1.1's word opens. The two words
  // share their opening letters, so the count that did not move is as much a
  // part of the claim as the one that did.
  size_t OpenEncryptionEnvelopes() const {
    return pp.ProtectEnvelopes().EncryptionEnvelopeDepth();
  }

  // Whether the reading stands inside protected code where the text ends.
  bool Protected() const { return pp.ProtectEnvelopes().InProtectedRegion(); }

  // The envelopes the reading opened and then closed, in closing order.
  const std::vector<ProtectedEnvelope>& Closed() const {
    return pp.ProtectEnvelopes().ClosedEnvelopes();
  }

  // The keywords the reading is holding for whichever envelope opens next. A
  // word turned away for its spelling describes nothing either, so it is absent
  // from here as well as from the counts above.
  const std::vector<std::string>& Pending() const {
    return pp.ProtectEnvelopes().PendingEnvelopeKeywords();
  }
};

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
// above: the word under test opens an envelope whose block is unreadable except
// under a scheme the source named.
std::string DesignUnderDeclaredEncoding() {
  std::string text = "`pragma protect begin\n";
  text.append("`pragma protect encoding=(enctype=\"base64\")\n");
  text.append("  initial result = 42;\n");
  text.append("`pragma protect end\n");
  return text;
}

// The opening directive of a produced envelope, written in the other spelling
// §22.5.1 allows. A decryption envelope cannot be written out by hand -- what
// its block holds depends on the key the region was sealed under -- so the one
// spelling under test is put into a real produced envelope rather than a text
// standing in for one. A text the encrypting half wrote no opening word into
// comes back as it stands, and the expectations of whichever test asked for the
// substitution then fail on the envelope that was never altered.
std::string WithValuedOpeningWord(const std::string& written) {
  constexpr std::string_view kOpening = "`pragma protect begin_protected\n";
  constexpr std::string_view kValued =
      "`pragma protect begin_protected=\"1\"\n";
  size_t at = written.find(kOpening);
  if (at == std::string::npos) return written;
  std::string valued(written);
  valued.replace(at, kOpening.size(), kValued);
  return valued;
}

// An encryption region holding a model that some earlier encryption sealed
// already, whose opening directive is written as `opening`.
//
// The three lines standing between that directive and §34.5.4.1's word are what
// make the arrangement readable in the produced text. One names the author of
// the sealed model, which is a description belonging to that model rather than
// to the encryption now running; one is the block that model was sealed into,
// which §34.5.15 makes an error anywhere no already-sealed model encloses it;
// and the marker in that block is long enough that finding it in the produced
// text means it was carried rather than coincided with.
std::string RegionAroundSealedModel(std::string_view opening) {
  std::string text = "`pragma protect begin\n";
  text.append("  initial result = 42;\n");
  text.append(opening);
  text.append("`pragma protect author=\"Other Corp\"\n");
  text.append("`pragma protect data_block=\"SEALEDMODELBLOCKMARKER\"\n");
  text.append("`pragma protect end_protected\n");
  text.append("`pragma protect end\n");
  return text;
}

// ---------------------------------------------------------------------------
// The word standing on its own is the expression.
// ---------------------------------------------------------------------------

// The syntax block read at its plainest: the word written by itself as the
// whole expression list of a protect pragma directive opens an envelope, and
// nothing about the directive is complained of.
//
// The envelope that opens is the one defined for decryption rather than for
// encryption, which is the mode this word opens and not the mode §34.5.1.1's
// word opens. That word's letters are the opening letters of this one, so the
// count that stayed where it was is as much of the claim as the count that
// moved.
//
// The standing the reading acquires is asserted here rather than apart, being
// the same state read through a shorter question: code an envelope of this mode
// encloses is protected code, and that is the condition the reading of a block
// and of an announced key are both gated on.
TEST(ProtectBeginProtectedSyntax, TheWordAloneOpensAnEnvelopeForDecryption) {
  ReadSource run("`pragma protect begin_protected\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 1U);
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 0U);
  EXPECT_TRUE(run.Protected());
}

// A directive carrying the word is a directive like any other as far as the
// text leaving the preprocessor goes: it is consumed, and the source written
// around it arrives at the step after unchanged.
TEST(ProtectBeginProtectedSyntax,
     TheDirectiveCarryingTheWordContributesNoText) {
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

// The envelope the word opened is the one §34.5.4.1's word answers, so a text
// writing the pair leaves one closed envelope of this mode behind and nothing
// open.
TEST(ProtectBeginProtectedSyntax, TheEnvelopeTheWordOpenedIsWhatCloses) {
  ReadSource run(
      "`pragma protect begin_protected\n"
      "`pragma protect end_protected\n");
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
  ASSERT_EQ(run.Closed().size(), 1U);
  EXPECT_EQ(run.Closed().front().mode, EnvelopeMode::kDecryption);
}

// The word written last in a list whose earlier expressions are keywords
// defined with a value, which is the position §34.3's produced envelope writes
// its describing expressions in. Each expression of a list is spelled on its
// own, so the word here is still the word standing alone and still opens.
TEST(ProtectBeginProtectedSyntax, TheWordLastAfterValuedExpressionsStillOpens) {
  ReadSource run(
      "`pragma protect author=\"Acme Corp\", data_method=\"x-caesar\", "
      "begin_protected\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 1U);
}

// The other order over the same list. A comma ends the expression before it, so
// a valued keyword written after the word qualifies neither the word nor the
// envelope's opening, and the word standing ahead of it is still the word
// standing alone.
TEST(ProtectBeginProtectedSyntax,
     TheWordFirstAheadOfAValuedExpressionStillOpens) {
  ReadSource run("`pragma protect begin_protected, comment=\"sealed\"\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 1U);
}

// The word as the whole of its own directive, with an expression describing the
// envelope written on the directive ahead of it. One expression list means the
// same thing however it is spread over directives, so the word opens here
// exactly as it does when it shares a directive with them.
TEST(ProtectBeginProtectedSyntax, TheWordAloneOnItsOwnDirectiveStillOpens) {
  ReadSource run(
      "`pragma protect author=\"Acme Corp\"\n"
      "`pragma protect begin_protected\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 1U);
}

// The word need not be written in the source as the word: a directive's text is
// ordinary source text, so a macro usage in it is substituted before the pragma
// grammar reads it, and what the grammar then reads is the word.
TEST(ProtectBeginProtectedSyntax, AMacroExpandingToTheWordOpensTheEnvelope) {
  ReadSource run(
      "`define OPEN begin_protected\n"
      "`pragma protect `OPEN\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 1U);
}

// A comment is not a pragma expression, so a directive whose word is followed
// by one carries the word alone and opens on it. Without this the word would
// have to be the last thing on its line to be the word.
TEST(ProtectBeginProtectedSyntax, ACommentAfterTheWordLeavesItStandingAlone) {
  ReadSource run("`pragma protect begin_protected // sealed model starts\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 1U);
}

// The word written where an envelope of its own mode is already open. §34.2
// has such envelopes nest, so this is a position the word is written in rather
// than a spelling of it, and the word opens there as it opens anywhere.
TEST(ProtectBeginProtectedSyntax, TheWordOpensAnEnvelopeInsideOneAlreadyOpen) {
  ReadSource run(
      "`pragma protect begin_protected\n"
      "`pragma protect begin_protected\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 2U);
}

// The word driving the reading from end to end: a region an author sealed with
// the key below is opened by the word the encrypting half wrote, its block is
// read back under that key, and the design arrives at the step after the
// preprocessor with none of the envelope left in it.
TEST(ProtectBeginProtectedSyntax, ARegionTheWordOpensComesBackUnderTheKey) {
  ReadSource run(Encrypted(Design()), kExchangeKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, "initial result = 42;"));
  EXPECT_FALSE(Holds(run.text, "data_block"));
}

// The same reading over an envelope that states something about itself, built
// from §34.5.9.1's own syntax rather than from a default. The region names a
// coding scheme, the encrypting half writes the block in it and states it on
// the envelope, and the word opens that envelope for a reading that gets the
// design back.
//
// The assertion on the produced text stands ahead of the reading on purpose: it
// is what says the scheme reached the envelope at all. Without it a run that
// silently fell back to this implementation's own writing would look exactly
// like a run that honored what the source stated, and the round trip would pass
// either way.
TEST(ProtectBeginProtectedSyntax,
     ARegionUnderADeclaredEncodingComesBackThroughTheWord) {
  std::string written = Encrypted(DesignUnderDeclaredEncoding());
  ASSERT_TRUE(Holds(written, "enctype=\"base64\""));
  ReadSource run(written, kExchangeKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, "initial result = 42;"));
}

// ---------------------------------------------------------------------------
// The word read by the encrypting half.
// ---------------------------------------------------------------------------

// The second reader of the same word, which finds it by walking a line's
// characters rather than by reading a directive's tokens. §34.5.3 has the
// contents of an already-sealed model treated as input cleartext, and it is
// this word that tells that half where such a model starts: the block written
// inside one belongs to the earlier envelope rather than to no envelope at all,
// so nothing about it is reported.
TEST(ProtectBeginProtectedSyntax, TheWordAloneMarksASealedModelForEncrypting) {
  EncryptionRun run(
      RegionAroundSealedModel("`pragma protect begin_protected\n"));
  EXPECT_FALSE(run.report.data_block_outside_protected_block);
}

// What that marking is worth in the produced text. The sealed model's lines are
// encrypted into the enclosing block as the bytes they are written with, so the
// block the earlier encryption produced is not readable in the output any more
// than the design around it is.
TEST(ProtectBeginProtectedSyntax, TheSealedModelTheWordMarkedIsEncryptedWhole) {
  std::string written =
      Encrypted(RegionAroundSealedModel("`pragma protect begin_protected\n"));
  EXPECT_TRUE(Holds(written, "data_block=\""));
  EXPECT_FALSE(Holds(written, "SEALEDMODELBLOCKMARKER"));
  EXPECT_FALSE(Holds(written, "initial result = 42;"));
}

// The other half of what the word marks: the expressions inside a sealed model
// describe that model, so none of them is read as description of the encryption
// now in process. §34.5.5 has the author of the design being encrypted written
// in the clear on the produced envelope, and the name written inside the sealed
// model is not that author.
TEST(ProtectBeginProtectedSyntax,
     TheSealedModelsDescriptionDoesNotReachTheEnvelopeBeingWritten) {
  std::string written =
      Encrypted(RegionAroundSealedModel("`pragma protect begin_protected\n"));
  EXPECT_FALSE(Holds(written, "author=\"Other Corp\""));
}

// ---------------------------------------------------------------------------
// A pragma_value written against the word.
// ---------------------------------------------------------------------------

// The closest input the rule has to turn away: the reserved word, written in
// the other spelling §22.5.1 allows a pragma expression. The definition covers
// the word alone, so this is not that expression -- it is reported, and no
// envelope opens.
//
// The value here carries text of its own. Which text it carries is not an input
// to this rule, which is defined on whether a value was written at all, so the
// number and identifier forms reach it as this one does and are not written out
// again below.
TEST(ProtectBeginProtectedSyntax, AStringWrittenAgainstTheWordIsReported) {
  ReadSource run("`pragma protect begin_protected=\"1\"\n");
  EXPECT_TRUE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
  EXPECT_FALSE(run.Protected());
}

// The value form that does carry a different input: a parenthesized list of
// further expressions, which leaves no text on the keyword at all. This is the
// one writing the rule cannot be told from the bare word by looking at what the
// value says, so it is the pair to the test above rather than a repeat of it.
TEST(ProtectBeginProtectedSyntax, AParenthesizedValueAgainstTheWordIsReported) {
  ReadSource run("`pragma protect begin_protected=(enctype=\"raw\")\n");
  EXPECT_TRUE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
}

// A word turned away for its spelling is not quietly demoted to a keyword that
// describes the envelope opening next either. Nothing about the expression is
// put in effect, so the reading holds nothing on its account.
TEST(ProtectBeginProtectedSyntax, TheValuedWordDescribesNoEnvelopeEither) {
  ReadSource run("`pragma protect begin_protected=\"1\"\n");
  EXPECT_TRUE(run.Pending().empty());
}

// The rejection does not stop the reading, and it does not spread: the
// directive after the reported one is read as it stands, the word on it opens
// an envelope, and it is the one directive that was wrong that was reported.
TEST(ProtectBeginProtectedSyntax, AWordWrittenProperlyAfterAReportedOneOpens) {
  ReadSource run(
      "`pragma protect begin_protected=\"1\"\n"
      "`pragma protect begin_protected\n");
  EXPECT_EQ(run.diag.ErrorCount(), 1U);
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 1U);
}

// The negative form of the round trip, and what the rule is guarding. The
// envelope is a real one the encrypting half produced, with only its opening
// word rewritten into the spelling the standard does not define: no region
// opens on it, so the block below it is the block of nothing, the design stays
// sealed, and the word that failed to open it is reported rather than the
// author being left to wonder where their design went.
TEST(ProtectBeginProtectedSyntax, AValuedOpeningWordLeavesTheDesignSealed) {
  ReadSource run(WithValuedOpeningWord(Encrypted(Design())), kExchangeKey);
  EXPECT_TRUE(run.diag.HasErrors());
  EXPECT_FALSE(Holds(run.text, "initial result = 42;"));
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
}

// The same input read by the encrypting half. A word written with a value marks
// no already-sealed model there either, so the block written beneath it stands
// outside every such model -- which §34.5.15 makes an error, there being no
// envelope it could have come out of.
TEST(ProtectBeginProtectedSyntax,
     TheValuedWordMarksNoSealedModelWhenEncrypting) {
  EncryptionRun run(
      RegionAroundSealedModel("`pragma protect begin_protected=\"1\"\n"));
  EXPECT_TRUE(run.report.data_block_outside_protected_block);
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
// the other. A half that marked the block here would seal an arbitrary run of
// this author's own design as somebody else's model and pass over its
// description of itself unread.
TEST(ProtectBeginProtectedSyntax,
     AParenthesizedValueMarksNoSealedModelWhenEncrypting) {
  EncryptionRun run(RegionAroundSealedModel(
      "`pragma protect begin_protected=(enctype=\"raw\")\n"));
  EXPECT_TRUE(run.report.data_block_outside_protected_block);
}

// What the unmarked model costs the envelope being written, put directly: its
// description was read as description of the encryption now in process, so the
// name of whoever wrote the other design is written in the clear on this one's
// envelope as though they had written this one.
TEST(ProtectBeginProtectedSyntax,
     TheValuedWordLetsTheOtherModelsAuthorOntoThisEnvelope) {
  std::string written = Encrypted(
      RegionAroundSealedModel("`pragma protect begin_protected=\"1\"\n"));
  EXPECT_TRUE(Holds(written, "author=\"Other Corp\""));
}

// ---------------------------------------------------------------------------
// Words that are not this word.
// ---------------------------------------------------------------------------

// A pragma_keyword is a simple identifier, so the same letters written as an
// escaped identifier name something else. Nothing opens on it, and nothing is
// wrong with it either: it is a legal pragma_value that this specification has
// no keyword for.
TEST(ProtectBeginProtectedSyntax,
     TheLettersAsAnEscapedIdentifierAreNotTheWord) {
  ReadSource run("`pragma protect \\begin_protected\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
}

// The same letters read by the encrypting half, whose walk would find this word
// standing where the other reading finds a value if it stepped over the
// backslash alone. It would then take the lines after it for somebody else's
// sealed model and pass over their description of themselves unread.
TEST(ProtectBeginProtectedSyntax,
     TheLettersAsAnEscapedIdentifierMarkNoSealedModel) {
  EncryptionRun run(
      RegionAroundSealedModel("`pragma protect \\begin_protected\n"));
  EXPECT_TRUE(run.report.data_block_outside_protected_block);
}

// SystemVerilog distinguishes case, so the word written in another case is a
// different word and opens nothing.
TEST(ProtectBeginProtectedSyntax, TheWordInAnotherCaseIsNotTheWord) {
  ReadSource run("`pragma protect BEGIN_PROTECTED\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
}

// The same at the encrypting half, which compares the name it scanned against
// the word rather than folding either one's case first.
TEST(ProtectBeginProtectedSyntax, TheWordInAnotherCaseMarksNoSealedModel) {
  EncryptionRun run(
      RegionAroundSealedModel("`pragma protect BEGIN_PROTECTED\n"));
  EXPECT_TRUE(run.report.data_block_outside_protected_block);
}

// The reserved word that this one's opening letters spell is the one §34.5.1.1
// defines, and it opens an envelope of the other mode of processing. Reading a
// name by its opening letters rather than as a whole word would have this word
// open that mode's envelope, or that word open this mode's.
TEST(ProtectBeginProtectedSyntax,
     AShorterReservedNameSharingItsLettersOpensTheOtherMode) {
  ReadSource run("`pragma protect begin\n");
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
  EXPECT_EQ(run.OpenEncryptionEnvelopes(), 1U);
}

// The same at the encrypting half, whose walk collects a name by running to the
// end of its letters. Stopping that walk at the length of the shorter word
// would leave this one looking exactly like it, and a model somebody sealed
// already would be read as the start of a region to seal now.
TEST(ProtectBeginProtectedSyntax,
     AShorterReservedNameSharingItsLettersMarksNoSealedModel) {
  EncryptionRun run(RegionAroundSealedModel("`pragma protect begin\n"));
  EXPECT_TRUE(run.report.data_block_outside_protected_block);
}

// The other direction of the same confusion, and the one no reserved word
// supplies: a name this word's whole spelling is the opening of. §34.5 sets
// aside no such name, so it is written here as an ordinary one, and it is a
// name of its own like any other identifier that happens to start this way.
//
// The shorter reserved word above cannot stand in for this. A reading that
// stopped at the end of the word it was looking for -- rather than at the end
// of the name the line wrote -- would answer that case correctly and this one
// wrongly, taking this line for the word and opening a region on a name the
// standard gives no meaning to.
TEST(ProtectBeginProtectedSyntax, ALongerNameStartingWithTheWordIsNotTheWord) {
  ReadSource run("`pragma protect begin_protected_v2\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
}

// The same at the encrypting half, whose walk collects a name by running to the
// end of its identifier characters and then compares the whole of it. Comparing
// only as far as the word's own length would leave this name looking exactly
// like the word.
TEST(ProtectBeginProtectedSyntax,
     ALongerNameStartingWithTheWordMarksNoSealedModel) {
  EncryptionRun run(
      RegionAroundSealedModel("`pragma protect begin_protected_v2\n"));
  EXPECT_TRUE(run.report.data_block_outside_protected_block);
}

// The letters standing on the right of an '=' are a pragma_value of the keyword
// written on its left, not a pragma_keyword of the list. The word only opens an
// envelope where it names an expression of its own.
TEST(ProtectBeginProtectedSyntax, TheWordWrittenAsAValueOpensNothing) {
  ReadSource run("`pragma protect comment=begin_protected\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
}

// The same at the encrypting half. Its walk meets the two names one after the
// other and has to carry, from the '=' to the letters after it, the fact that
// what it is reading is a value; a walk that forgot would find this word here.
TEST(ProtectBeginProtectedSyntax, TheWordWrittenAsAValueMarksNoSealedModel) {
  EncryptionRun run(
      RegionAroundSealedModel("`pragma protect comment=begin_protected\n"));
  EXPECT_TRUE(run.report.data_block_outside_protected_block);
}

// The word is a keyword of the protect pragma, which is the specification the
// pragma_name selects. Written under another pragma_name it asks a
// specification this implementation does not recognize for something, and
// leaves the protected envelopes of the text alone.
TEST(ProtectBeginProtectedSyntax, TheWordUnderAnotherPragmaNameOpensNothing) {
  ReadSource run("`pragma acme begin_protected\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
}

// The same at the encrypting half, which decides whether a line is worth
// reading for names at all by the pragma_name on it. A half that searched every
// directive for the word would take this one as the start of a sealed model.
//
// The word standing in the pragma_name slot instead is turned away by this very
// check, before any name is looked for, so this reader answers that spelling
// here rather than in a case of its own. The word is written in the body
// position on purpose: that is where this reader does look, which makes it the
// spelling that would slip through.
TEST(ProtectBeginProtectedSyntax,
     TheWordUnderAnotherPragmaNameMarksNoSealedModel) {
  EncryptionRun run(RegionAroundSealedModel("`pragma acme begin_protected\n"));
  EXPECT_TRUE(run.report.data_block_outside_protected_block);
}

// The other position the word can be written in on a directive of this shape:
// the pragma_name itself. There it names a specification rather than asking one
// for something, and the specification it names is not the one protected
// envelopes belong to, so nothing opens and nothing is wrong.
TEST(ProtectBeginProtectedSyntax, TheWordAsThePragmaNameOpensNothing) {
  ReadSource run("`pragma begin_protected\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
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
TEST(ProtectBeginProtectedSyntax, TheWordAsThePragmaNameMarksNoSealedModel) {
  EncryptionRun run(RegionAroundSealedModel("`pragma begin_protected\n"));
  EXPECT_TRUE(run.report.data_block_outside_protected_block);
}

// A pragma_value may itself be a list of pragma expressions, and the word
// written inside one belongs to that list rather than to the directive's own.
// It qualifies the value of the keyword carrying it, so it names no expression
// of the directive and opens nothing -- the same conclusion as the word
// standing on the right of an '=', reached by a different reading.
TEST(ProtectBeginProtectedSyntax,
     TheWordInsideAParenthesizedValueOpensNothing) {
  ReadSource run("`pragma protect encoding=(begin_protected)\n");
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
}

// The same nesting read by the encrypting half, which steps over a
// parenthesized value whole rather than walking into it. Two separate readings
// have to reach the same conclusion about where the word counts, and either one
// could come to it alone.
TEST(ProtectBeginProtectedSyntax,
     TheWordInsideAParenthesizedValueMarksNoSealedModel) {
  EncryptionRun run(
      RegionAroundSealedModel("`pragma protect encoding=(begin_protected)\n"));
  EXPECT_TRUE(run.report.data_block_outside_protected_block);
}

}  // namespace
