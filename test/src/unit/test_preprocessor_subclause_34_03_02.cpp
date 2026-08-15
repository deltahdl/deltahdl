// §34.3.2 Decryption.
//
// The subclause states one obligation and then two things about the text that
// obligation puts into the source.
//
//   A tool that supports decrypting compilation replaces each decryption
//   envelope of a source text with the source text recovered from that
//   envelope's data_block, read according to the pragma expressions specifying
//   the envelope.
//
//   The recovered text may hold usages of text macros. Those are substituted
//   once the envelope has been replaced, not before it.
//
//   The recovered text may hold decryption envelopes of its own. Those are
//   decrypted and substituted once the envelope enclosing them has been
//   replaced, not before it.
//
// The latter two are statements about order, and order is only observable
// where the thing being ordered is invisible until the step ahead of it has
// run. A macro usage sealed inside a data_block cannot be substituted until
// the block is opened, and an envelope sealed inside one cannot be recognized
// until the same. So each test here hides the construct at issue inside a
// region and then looks for its effect in the text the preprocessor produced.
//
// All of it is preprocessor-stage. The replacement is wired into the protect
// pragma handler in src/preprocessor/preprocessor_lines.cpp, which hands the
// recovered text back to the preprocessor's own source loop -- so macro
// substitution and envelope recognition reach it exactly as they reach text
// that was written in the file, and reach it only once the envelope it was
// sealed in is gone.
//
// Every envelope below is a real one. The regions come out of the encrypting
// half of §34.3.1 and the expressions carrying them are the `pragma directive
// syntax of §22.11, so a region recovered here stands for text that was really
// encrypted rather than for a string a helper arranged to look like one; the
// macros sealed inside those regions are the `define and text-macro usage
// syntax of §22.5. What a recovered design goes on to compute is observed at
// the simulator stage instead.

#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

// The key an IP author encrypted under, and a key that is not it. Every rule
// here acts on a region that was opened, so the second key is what an input
// that cannot be opened is built from.
constexpr std::string_view kAuthorKey = "acme-exchange-key";
constexpr std::string_view kOtherKey = "not-the-authors-key";

// The text a reading of `src` under `key` produced, with the diagnostics that
// reading raised.
//
// The produced text is the text the compilation step after the preprocessor
// reads, so it is where a replacement, a substituted macro and a recovered
// inner envelope are all observed. The diagnostics ride beside it because each
// of these rules has a reporting side wherever a region will not open.
struct ProducedText {
  SourceManager mgr;
  DiagEngine diag{mgr};
  std::string text;

  ProducedText(const std::string& src, std::string_view key) {
    PreprocConfig config;
    config.protect_key = key;
    Preprocessor pp(mgr, diag, config);
    text = pp.Preprocess(mgr.AddFile("<test>", src));
  }

  // Whether the produced text holds `needle` anywhere.
  bool Holds(std::string_view needle) const {
    return text.find(needle) != std::string_view::npos;
  }

  // Where it holds it. Several of these rules are about position rather than
  // presence, and comparing two of these is how a test asks which of two
  // pieces of recovered text came first.
  size_t At(std::string_view needle) const { return text.find(needle); }
};

// A whole decryption envelope standing for `body`, formed by putting `body`
// through the encrypting half under `key`.
//
// Nothing here composes an envelope by hand, because the rules act on what a
// data_block records rather than on how one is spelled: a value that merely
// looked like a block would be turned away before any of these rules was
// reached. Building the envelope this way also means it arrives carrying the
// expressions the encrypting half writes onto one -- who made it, what its
// data are under, how its block is spelled -- so the replacement is read
// according to a real description of a real envelope.
std::string EnvelopeOf(const std::string& body,
                       std::string_view key = kAuthorKey) {
  std::string region = "`pragma protect begin\n";
  region += body;
  region += "`pragma protect end\n";
  return EncryptEnvelopes(region, key);
}

// ---------------------------------------------------------------------------
// Replacing an envelope with the source text its data_block records.
// ---------------------------------------------------------------------------

// The replacement, read where the compilation step reads it. The recovered
// text is in the produced text and it is at the envelope's own position, so
// what the step after this one gets is a file with design source where the
// envelope stood rather than one with the design appended somewhere else.
TEST(EnvelopeDecryption, TheRecoveredTextStandsWhereTheEnvelopeWas) {
  std::string src = "initial before_value = 1;\n";
  src += EnvelopeOf("initial sealed_value = 2;\n");
  src += "initial after_value = 3;\n";
  ProducedText run(src, kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.Holds("initial sealed_value = 2;"));
  EXPECT_LT(run.At("initial before_value = 1;"),
            run.At("initial sealed_value = 2;"));
  EXPECT_LT(run.At("initial sealed_value = 2;"),
            run.At("initial after_value = 3;"));
}

// The envelope is replaced, not merely added to. None of the three expressions
// that delimited it and recorded its region is in the text the compilation
// step reads, so nothing of the envelope survives beside the source it stood
// for.
TEST(EnvelopeDecryption, TheEnvelopeIsGoneFromTheProducedText) {
  ProducedText run(EnvelopeOf("initial sealed_value = 2;\n"), kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(run.Holds("begin_protected"));
  EXPECT_FALSE(run.Holds("data_block"));
  EXPECT_FALSE(run.Holds("end_protected"));
}

// Each envelope is replaced by the text its own block records. A text carrying
// one envelope cannot tell that apart from a rule replacing whichever envelope
// it met first, so this one carries two and keeps a marker between them: each
// recovered text lands on its own envelope's side of it.
TEST(EnvelopeDecryption, EachEnvelopeIsReplacedByItsOwnRecordedText) {
  std::string src = EnvelopeOf("initial first_value = 1;\n");
  src += "initial between_value = 2;\n";
  src += EnvelopeOf("initial third_value = 3;\n");
  ProducedText run(src, kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_LT(run.At("initial first_value = 1;"),
            run.At("initial between_value = 2;"));
  EXPECT_LT(run.At("initial between_value = 2;"),
            run.At("initial third_value = 3;"));
  EXPECT_NE(run.At("initial third_value = 3;"), std::string::npos);
}

// The envelope an IP author really specifies carries expressions of its own,
// and the replacement is read according to them. The description the author
// wrote is carried onto the envelope by the encrypting half and stands ahead
// of the block it describes, so the block is opened with that description in
// effect -- and the description itself, being pragma directives, is no part of
// what the compilation step goes on to read.
TEST(EnvelopeDecryption, AnEnvelopeCarryingItsDescriptionIsStillReplaced) {
  std::string authored = "`pragma protect author=\"Acme Corp\"\n";
  authored += "`pragma protect data_method=\"x-caesar\", ";
  authored += "data_keyname=\"rot13\", begin\n";
  authored += "initial sealed_value = 2;\n";
  authored += "`pragma protect end\n";
  ProducedText run(EncryptEnvelopes(authored, kAuthorKey), kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.Holds("initial sealed_value = 2;"));
  EXPECT_FALSE(run.Holds("Acme Corp"));
  EXPECT_FALSE(run.Holds("rot13"));
}

// The smallest text a block can record. A block recording nothing still
// records something, so the envelope is replaced -- by no text at all -- and
// the lines that stood around it close up with nothing reported. Every other
// test here would pass on a rule that acted only where there was something to
// put back, which is what this input rules out.
TEST(EnvelopeDecryption, AnEnvelopeRecordingEmptyTextIsReplacedByNothing) {
  std::string src = "initial before_value = 1;\n";
  src += EnvelopeOf("");
  src += "initial after_value = 3;\n";
  ProducedText run(src, kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.Holds("initial before_value = 1;"));
  EXPECT_TRUE(run.Holds("initial after_value = 3;"));
  EXPECT_FALSE(run.Holds("data_block"));
}

// The closest text the rule has to leave alone: one holding no decryption
// envelope at all. There is nothing to replace, so every line of it reaches
// the compilation step as the line that was written.
TEST(EnvelopeDecryption, TextHoldingNoEnvelopeIsLeftAsItStands) {
  std::string src = "initial before_value = 1;\n";
  src += "initial after_value = 3;\n";
  ProducedText run(src, kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.Holds("initial before_value = 1;"));
  EXPECT_TRUE(run.Holds("initial after_value = 3;"));
}

// ---------------------------------------------------------------------------
// Text macros in the recovered text, substituted once the envelope is gone.
// ---------------------------------------------------------------------------

// A macro defined in the open and used inside the region. The usage is sealed
// in the block, so there is nowhere for a substitution to reach it until the
// block has been opened; finding the macro's text in what the compilation step
// reads -- and the usage nowhere in it -- is the order the rule asks for. A
// tool substituting before replacing would hand the usage on untouched.
TEST(EnvelopeDecryption, AMacroUsedInTheRecoveredTextIsSubstituted) {
  std::string src = "`define WIDTH 8\n";
  src += EnvelopeOf("logic [`WIDTH-1:0] sealed_bus;\n");
  ProducedText run(src, kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.Holds("logic [8-1:0] sealed_bus;"));
  EXPECT_FALSE(run.Holds("`WIDTH"));
}

// The definition sealed inside the region instead. A definition not yet in the
// text cannot be found by a substitution, so the usage written after the
// envelope resolving to it says the region was put back into the source first
// and read for macros afterwards.
TEST(EnvelopeDecryption, AMacroDefinedInTheRecoveredTextIsInEffectAfterIt) {
  std::string src = EnvelopeOf("`define WIDTH 8\n");
  src += "logic [`WIDTH-1:0] open_bus;\n";
  ProducedText run(src, kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.Holds("logic [8-1:0] open_bus;"));
  EXPECT_FALSE(run.Holds("`WIDTH"));
}

// Definition and usage both sealed in the same region, which is how an IP
// author's own protected source is written. Neither is in the text until the
// envelope is replaced, and the substitution still happens.
TEST(EnvelopeDecryption, AMacroDefinedAndUsedInTheRecoveredTextIsSubstituted) {
  std::string body = "`define WIDTH 8\n";
  body += "logic [`WIDTH-1:0] sealed_bus;\n";
  ProducedText run(EnvelopeOf(body), kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.Holds("logic [8-1:0] sealed_bus;"));
  EXPECT_FALSE(run.Holds("`WIDTH"));
}

// The other form a text macro usage takes: one with arguments. The whole
// usage, its name and its actual arguments alike, is recovered out of the
// block before anything reads it as a usage, so the substitution is the one
// the arguments call for rather than the body with its formals left standing.
TEST(EnvelopeDecryption, AMacroWithArgumentsInTheRecoveredTextIsSubstituted) {
  std::string src = "`define MSB(w) ((w)-1)\n";
  src += EnvelopeOf("logic [`MSB(8):0] sealed_bus;\n");
  ProducedText run(src, kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.Holds("logic [((8)-1):0] sealed_bus;"));
  EXPECT_FALSE(run.Holds("`MSB"));
}

// The closest recovered text the rule has to turn away: one whose usage names
// no macro. Substitution really is applied to what came out of the block, so a
// usage that cannot be substituted is reported exactly as it would have been
// had it been written in the file -- rather than passing quietly as though the
// recovered text were something other than source.
TEST(EnvelopeDecryption, AnUndefinedMacroInTheRecoveredTextIsReported) {
  ProducedText run(EnvelopeOf("logic [`WIDTH-1:0] sealed_bus;\n"), kAuthorKey);
  // The recovered text is read through as a source of its own, counting from
  // its first line, so the usage stands on line 1 of what the block held.
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(), "undefined macro 'WIDTH'",
                            1, "22.5.1"));
}

// ---------------------------------------------------------------------------
// Decryption envelopes in the recovered text, decrypted once the envelope
// enclosing them is gone.
// ---------------------------------------------------------------------------

// An envelope sealed inside another envelope's block. It is not in the source
// text at all until the enclosing envelope is replaced, and once it is, it is
// recognized and replaced in its turn: the innermost design reaches the
// compilation step, and no envelope of either level is left beside it.
TEST(EnvelopeDecryption, AnEnvelopeInTheRecoveredTextIsDecryptedToo) {
  std::string sealed = EnvelopeOf("initial sealed_value = 2;\n");
  ProducedText run(EnvelopeOf(sealed), kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.Holds("initial sealed_value = 2;"));
  EXPECT_FALSE(run.Holds("data_block"));
}

// The recovered text is source like any other, so an envelope of it may seal
// text of its own beside a further envelope. Each level is put back before the
// level inside it is so much as visible, and the whole chain arrives in the
// order the levels enclose one another.
TEST(EnvelopeDecryption, EveryLevelOfEnclosedEnvelopeIsDecrypted) {
  std::string innermost = EnvelopeOf("initial third_value = 3;\n");
  std::string middle = "initial second_value = 2;\n";
  middle += innermost;
  std::string outer = "initial first_value = 1;\n";
  outer += EnvelopeOf(middle);
  ProducedText run(EnvelopeOf(outer), kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_LT(run.At("initial first_value = 1;"),
            run.At("initial second_value = 2;"));
  EXPECT_LT(run.At("initial second_value = 2;"),
            run.At("initial third_value = 3;"));
  EXPECT_NE(run.At("initial third_value = 3;"), std::string::npos);
}

// Two envelopes sealed side by side in one block rather than one inside the
// other. Both are in the text the replacement produced, so both are decrypted
// and substituted, in the order the recovered text writes them.
TEST(EnvelopeDecryption, EveryEnclosedEnvelopeOfOneRecoveredTextIsDecrypted) {
  std::string body = EnvelopeOf("initial first_value = 1;\n");
  body += EnvelopeOf("initial second_value = 2;\n");
  ProducedText run(EnvelopeOf(body), kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.Holds("initial first_value = 1;"));
  EXPECT_LT(run.At("initial first_value = 1;"),
            run.At("initial second_value = 2;"));
}

// The closest enclosed envelope the rule has to turn away: one whose block was
// encrypted under a key that is not the one this reading supplies. The
// enclosing envelope opens and its own text arrives; the enclosed one is
// decrypted on its own account, fails on its own account and is reported, and
// the design it sealed does not reach the compilation step. Without this pair
// of outcomes the enclosed envelope could have been carried across as text
// rather than decrypted.
TEST(EnvelopeDecryption, AnEnclosedEnvelopeUnderAnotherKeyIsReported) {
  std::string body = "initial outer_value = 1;\n";
  body += EnvelopeOf("initial inner_value = 2;\n", kOtherKey);
  ProducedText run(EnvelopeOf(body), kAuthorKey);
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma data block cannot be decrypted with the key supplied",
      LineHolding(body, "data_block="), "34.3.2"));
  EXPECT_TRUE(run.Holds("initial outer_value = 1;"));
  EXPECT_FALSE(run.Holds("initial inner_value = 2;"));
}

// The two rules meeting: a macro usage sealed two envelopes deep. It waits on
// both replacements -- the outer one to put the enclosed envelope into the
// text, the enclosed one to put the usage there -- and is substituted after
// them.
TEST(EnvelopeDecryption, AMacroInAnEnclosedEnvelopeIsSubstitutedAfterBoth) {
  std::string body = "`define WIDTH 8\n";
  body += EnvelopeOf("logic [`WIDTH-1:0] sealed_bus;\n");
  ProducedText run(EnvelopeOf(body), kAuthorKey);
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(run.Holds("logic [8-1:0] sealed_bus;"));
  EXPECT_FALSE(run.Holds("`WIDTH"));
}

}  // namespace
