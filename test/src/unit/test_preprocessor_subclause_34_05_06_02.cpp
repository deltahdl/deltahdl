// §34.5.6.2 Description, for the protect pragma keyword that carries whatever
// further the author of an envelope's IP offered about themselves. The syntax
// block above it settles how the expression is spelled; this one settles what
// a tool does with one, under each of the three headings the subclause writes
// its rules under.
//
// ENCRYPTION INPUT. The value written against the keyword is a string holding
// information the IP author supplied beyond a name. The subclause states why
// the keyword is tabulated at all: it is a keyword of its own rather than one
// reading of the keyword carrying uninterpreted documentation, so whatever
// wants what the author said looks at this name instead of parsing a
// documentation string for it.
//
// ENCRYPTION OUTPUT. Two rules, and a third for the text the first two do not
// reach. An expression the encryption envelope holds is placed in a pragma
// directive the protected envelope encloses; it is kept out of the data_block;
// and an expression the encryption envelope does not hold is copied into the
// output stream without change.
//
// DECRYPTION INPUT: none. A tool reading a protected envelope draws nothing
// from the expression -- neither design text nor any part of what opens the
// block -- so an envelope carrying one is read exactly as far as an envelope
// carrying none.
//
// All of it is preprocessor-stage. src/preprocessor/protect_processing.cpp
// carries the encrypting half: it reads each line an encryption envelope
// encloses for the expression, keeps what it says beside the region rather
// than among the lines that are about to stop being readable, and holds the
// line carrying it back from the text the block records.
// src/preprocessor/protect_envelope_output.cpp writes it into the envelope
// taking that region's place, through the directive
// src/preprocessor/protect_keywords.cpp spells, and
// src/preprocessor/protect_pragma_line.cpp is the reading of a line that
// settles which keyword a directive named and what was written against it.
// The decrypting half is src/preprocessor/preprocessor.cpp, which consumes the
// directive like any other protect pragma and takes nothing from it.
//
// The inputs are the real syntax of the dependencies this rule consumes.
// §34.5.3.1's word opens each model an earlier encryption sealed already and
// §34.5.4.1's word closes it, and those models are the position the rule is
// hardest in: a word written inside one belongs to a design somebody else
// sealed, so it is neither placed on the new envelope nor lifted out of the
// bytes travelling into its block. The models below are written by running the
// encrypting half over a region of its own rather than spelled by hand, so the
// words delimiting them and the stating directive inside them are a tool's.
// §34.5.1.1 and §34.5.2.1 delimit the regions being encrypted, §34.5.10's
// data_keyowner and §34.5.12's data_keyname are the names a region reaches its
// key through, and §34.5.15's data_block is where the text a region sealed is
// carried. Every text below is written as directive syntax and driven through
// the encrypting half, the preprocessor, or both in turn, rather than handed
// to the envelope state by hand.

#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_protect_region.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_envelope.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

// What a region offers further about its author, and a second such offering
// for the inputs that write one region against another. Both hold spaces and
// punctuation, so either standing in a produced text can only have arrived
// there as the value of an expression rather than as a stray word of the
// source.
constexpr std::string_view kFurtherWord = "Analytical Society, London";
constexpr std::string_view kOtherFurtherWord = "Harvard Computation Lab";

// The name of an author, for the readings that hold this subclause's keyword
// against the one §34.5.5 defines. It is a value neither expression here would
// carry by accident.
constexpr std::string_view kAuthorName = "Ada Lovelace";

// The opening of any directive carrying this subclause's expression, for the
// readings that ask whether an envelope offers anything further at all rather
// than what.
//
// It carries the equals sign because the keyword §34.5.5 defines is spelled
// with the characters this one opens with: a search for the shorter name alone
// would answer yes to a directive carrying only the longer.
constexpr std::string_view kAnyStating = "`pragma protect author_info=";

// The same for §34.5.5's keyword, spelled so that this subclause's directive
// does not answer to it.
constexpr std::string_view kAnyNaming = "`pragma protect author=";

// The expression this subclause is about, carrying `word` as the string it
// specifies.
//
// It serves both sides. A source text offers something further about its
// author by writing this, and an encrypting tool placing the expression inside
// the envelope writes the same thing, so what a tool produced is compared
// against the spelling an input was built from.
std::string StatesFurther(std::string_view word) {
  std::string written = "`pragma protect author_info=\"";
  written.append(word).append("\"\n");
  return written;
}

// §34.5.5's expression, for the readings that write the two keywords against
// one another. Nothing here is a claim about that subclause: it is the nearest
// neighbour this one's keyword has, and a value belonging to it is the value
// this one must not be found carrying.
std::string NamesTheAuthor(std::string_view name) {
  std::string written = "`pragma protect author=\"";
  written.append(name).append("\"\n");
  return written;
}

// A model an earlier encryption sealed already, offering `word` further about
// the author of the design it holds.
//
// Nothing of it is spelled by hand: it is what the encrypting half writes from
// a region of its own, so the words §34.5.3.1 and §34.5.4.1 define delimit it
// because a tool put them there, and the stating directive standing in the
// clear inside it is one this very rule placed on an earlier run.
std::string SealedModelStating(std::string_view word) {
  return Encrypted(RegionWriting(StatesFurther(word)));
}

// `envelope` with the directive stating what the author offered taken out of
// its description and written again just past the block, on the line before
// the word that closes it.
//
// An envelope cannot be spelled by hand for this -- what its block holds
// depends on the key the region was sealed under -- so an envelope whose
// statement stands somewhere else is made by moving that directive inside a
// real produced one. A text the directive was not found in comes back as it
// stands, and the expectations of the test that asked for the move then fail
// on the envelope that was never altered.
std::string WithTheStatementMovedPastTheBlock(const std::string& envelope) {
  std::string stating = StatesFurther(kFurtherWord);
  size_t stands = envelope.find(stating);
  if (stands == std::string::npos) return envelope;
  std::string moved(envelope);
  moved.erase(stands, stating.size());
  size_t closes = moved.find(kEndProtected);
  if (closes == std::string::npos) return envelope;
  moved.insert(closes, stating);
  return moved;
}

// `envelope` with the directive naming the key its block is under replaced by
// this subclause's expression carrying that very name.
//
// The characters a reader would have drawn the key from are still in the
// envelope, and the only thing that changed is which keyword they were written
// against. It is the closest input the decryption rule has to turn away: an
// expression that looks in every respect like the one thing a reader does take
// from an envelope's description, and that a reader takes nothing from.
std::string WithTheKeyNameWrittenAsTheStatement(const std::string& envelope) {
  std::string designation = DesignatesTheKey();
  size_t stands = envelope.find(designation);
  if (stands == std::string::npos) return envelope;
  std::string replaced(envelope);
  replaced.replace(stands, designation.size(), StatesFurther(kKeyName));
  return replaced;
}

// ---------------------------------------------------------------------------
// ENCRYPTION INPUT: the expression specifies a string of further information
// supplied by the IP author.
// ---------------------------------------------------------------------------

// The rule at its plainest. The string a region wrote against the keyword is
// what the envelope taking that region's place offers about the design's
// author, and the design the region held is sealed rather than standing in the
// clear beside it.
TEST(ProtectAuthorInfoDescription, TheStringAgainstTheKeywordIsWhatIsOffered) {
  std::string written = Encrypted(RegionWriting(StatesFurther(kFurtherWord)));
  EXPECT_FALSE(Holds(written, kSealedDesign));
  EXPECT_TRUE(Holds(written, StatesFurther(kFurtherWord)));
}

// §22.5.1 gives a pragma_value more than one spelling, and a keyword whose
// value is further information is not thereby barred from being written with
// an identifier against it. What the subclause asks for is whatever more the
// author had to say, so a region that answered in that spelling has answered.
//
// The identifier stands here for every spelling that is one written thing
// carrying no quotation marks. This subclause draws its line at whether one
// thing was written against the keyword rather than at what the characters of
// it look like, so a run of digits written here is the same input to this rule
// as a run of letters, and a case for each would be one case twice. Which
// spellings §22.5.1 tells apart from one another is that subclause's question.
TEST(ProtectAuthorInfoDescription, AnIdentifierAgainstTheKeywordIsOffered) {
  std::string named = "`pragma protect author_info=analytical_society\n";
  std::string written = Encrypted(RegionWriting(named));
  EXPECT_FALSE(Holds(written, kSealedDesign));
  EXPECT_TRUE(Holds(written, named));
}

// The value form where two quantities part company: a string with nothing
// between its quotation marks was written, and what it holds is nothing at
// all. A reading that asked whether the region offered anything, rather than
// whether it wrote the expression, would take this for a region that offered
// nothing -- and every other value here would let that reading pass. What the
// region specified is a design whose author had nothing further to say, which
// is a thing it specified, so the envelope states it.
TEST(ProtectAuthorInfoDescription, AnEmptyStringAgainstTheKeywordIsPlaced) {
  std::string written = Encrypted(RegionWriting(StatesFurther("")));
  EXPECT_FALSE(Holds(written, kSealedDesign));
  EXPECT_TRUE(Holds(written, StatesFurther("")));
}

// The negative of the same rule, and the closest input it has to turn away:
// the other pragma_value spelling §22.5.1 admits, a parenthesized list of
// further expressions written where the string belongs. A list is not one
// written thing, so it specifies no information -- what it holds are
// subkeywords of somebody's own devising -- and a reading that took it would
// publish that list in the clear as what the design's author offered.
TEST(ProtectAuthorInfoDescription, AParenthesizedListSpecifiesNothing) {
  std::string listed =
      "`pragma protect author_info=(city=\"London\", year=1843)\n";
  std::string written = Encrypted(RegionWriting(listed));
  EXPECT_TRUE(Holds(written, kBeginProtected));
  EXPECT_FALSE(Holds(written, kAnyStating));
  EXPECT_TRUE(Holds(OpenedBlockWriting(listed), listed));
}

// What the keyword being tabulated apart from the one carrying uninterpreted
// documentation is worth. The whole of this expression is written inside a
// documentation string here, so a tool that went looking for what an author
// offered by reading such a string would find this -- something to publish,
// and the keyword spelled out beside it. What the author offered is recognized
// by the keyword the directive named instead, and this directive named the
// other one, so what a documentation string holds settles nothing either way.
TEST(ProtectAuthorInfoDescription, WordsInsideADocumentationStringAreNotTaken) {
  std::string documented =
      "`pragma protect comment=\"author_info=\\\"Analytical Society\\\"\"\n";
  std::string written = Encrypted(RegionWriting(documented));
  EXPECT_TRUE(Holds(written, kBeginProtected));
  EXPECT_FALSE(Holds(written, kAnyStating));
  EXPECT_TRUE(Holds(OpenedBlockWriting(documented), documented));
}

// The two keywords side by side on one directive, which is the position that
// tells them apart: §22.5.1 lets one directive carry a list of expressions,
// and what the envelope offers is the value written against this keyword
// rather than the documentation written beside it.
TEST(ProtectAuthorInfoDescription, TheValueBesideADocumentationStringIsTaken) {
  std::string beside = "`pragma protect comment=\"Harvard Computation Lab\", ";
  beside.append("author_info=\"Analytical Society, London\"\n");
  std::string written = Encrypted(RegionWriting(beside));
  EXPECT_TRUE(Holds(written, StatesFurther(kFurtherWord)));
  EXPECT_FALSE(Holds(written, kOtherFurtherWord));
}

// This keyword is a name of its own rather than §34.5.5's name with something
// written after it. A region that offered further information and named nobody
// has its offering placed as an offering: the envelope carries this expression
// and states no author, so nothing of what was said about the author was taken
// for the author.
TEST(ProtectAuthorInfoDescription, TheOfferingIsNotTakenForTheAuthorsName) {
  std::string written = Encrypted(RegionWriting(StatesFurther(kFurtherWord)));
  EXPECT_TRUE(Holds(written, StatesFurther(kFurtherWord)));
  EXPECT_FALSE(Holds(written, kAnyNaming));
}

// And the other way about, which is the reading the shared characters really
// threaten: a region naming its author and offering nothing further has no
// value for this keyword to carry, so the envelope states none. A reading that
// matched this keyword against a directive naming the author would publish
// that name twice and call one of them information.
TEST(ProtectAuthorInfoDescription, TheAuthorsNameIsNotTakenAsTheOffering) {
  std::string written = Encrypted(RegionWriting(NamesTheAuthor(kAuthorName)));
  EXPECT_TRUE(Holds(written, kAnyNaming));
  EXPECT_FALSE(Holds(written, kAnyStating));
}

// ---------------------------------------------------------------------------
// ENCRYPTION OUTPUT: the expression is placed in a directive the protected
// envelope encloses.
// ---------------------------------------------------------------------------

// Enclosed within the envelope, read as the position it is: the directive
// stands between the two expressions delimiting the envelope, so a reader that
// reached the envelope reached what the author offered. It is written once,
// the expression the region wrote having been placed here rather than written
// out beside a copy of itself.
TEST(ProtectAuthorInfoDescription, ThePlacedDirectiveStandsInsideTheEnvelope) {
  std::string written = Encrypted(RegionWriting(StatesFurther(kFurtherWord)));
  EXPECT_EQ(TimesWritten(written, StatesFurther(kFurtherWord)), 1U);
  EXPECT_LT(written.find(kBeginProtected),
            written.find(StatesFurther(kFurtherWord)));
  EXPECT_LT(written.find(StatesFurther(kFurtherWord)),
            written.find(kEndProtected));
}

// The negative: a region whose text offers nothing further has no expression
// to place, so the envelope taking its place carries no such directive. What
// is placed is the expression the region held rather than the keyword as a
// matter of course.
TEST(ProtectAuthorInfoDescription, ARegionOfferingNothingPlacesNoDirective) {
  std::string inside = ReachesTheKey();
  inside.append(kSealedDesign);
  std::string written = Encrypted(RegionAround(inside));
  EXPECT_TRUE(Holds(written, kBeginProtected));
  EXPECT_FALSE(Holds(written, kAnyStating));
}

// The expression the envelope holds is the one its own region wrote. A model
// §34.5.3.1's and §34.5.4.1's words delimit travels into the enclosing block
// as the bytes it is written with, so what it offers was offered by some
// earlier encryption for a design of its own: this envelope offers what its
// region wrote, once, and says nothing about the other.
TEST(ProtectAuthorInfoDescription, AnEnclosedSealedModelsWordIsNotPlacedAgain) {
  std::string inside = ReachesTheKey();
  inside.append(StatesFurther(kFurtherWord));
  inside.append(SealedModelStating(kOtherFurtherWord));
  inside.append(kSealedDesign);
  std::string written = Encrypted(RegionAround(inside));
  EXPECT_EQ(TimesWritten(written, StatesFurther(kFurtherWord)), 1U);
  EXPECT_FALSE(Holds(written, kOtherFurtherWord));
}

// Where that offering went instead, which no absence from the produced text
// can show: the sealed model is inside the new block whole, its own delimiters
// and the stating directive an earlier run placed inside it included. It was
// carried across rather than dropped, and this rule reached none of it.
TEST(ProtectAuthorInfoDescription, AnEnclosedSealedModelsOfferingIsCarriedIn) {
  std::string inside = ReachesTheKey();
  inside.append(StatesFurther(kFurtherWord));
  inside.append(SealedModelStating(kOtherFurtherWord));
  inside.append(kSealedDesign);
  std::string opened = OpenedBlockOf(Encrypted(RegionAround(inside)));
  EXPECT_TRUE(Holds(opened, kBeginProtected));
  EXPECT_TRUE(Holds(opened, StatesFurther(kOtherFurtherWord)));
}

// Each envelope carries what its own region held. The second region here
// offers nothing, so the envelope standing in its place offers nothing -- what
// the first region wrote describes the first envelope, and an envelope
// separated from the one before it says exactly what it said where it stood.
TEST(ProtectAuthorInfoDescription, AnEnvelopePlacesOnlyItsOwnRegionsOffering) {
  std::string second = ReachesTheKey();
  second.append("module other_m; endmodule\n");
  std::string first = RegionWriting(StatesFurther(kFurtherWord));
  std::string written = Encrypted(first + RegionAround(second));
  EXPECT_EQ(TimesWritten(written, kBeginProtected), 2U);
  EXPECT_EQ(TimesWritten(written, kAnyStating), 1U);
  size_t opens_first = written.find(kBeginProtected);
  size_t opens_second = written.find(kBeginProtected, opens_first + 1);
  EXPECT_LT(written.find(kAnyStating), opens_second);
}

// ---------------------------------------------------------------------------
// ENCRYPTION OUTPUT: the expression is not encrypted into the data block.
// ---------------------------------------------------------------------------

// The rule observed where it is decided: the block is opened with the key the
// region was sealed under and read. The design the region held is in there,
// and the expression offering something about its author is not -- which is
// what leaves that offering readable to somebody holding no key.
TEST(ProtectAuthorInfoDescription, TheOpenedBlockHoldsNoStatingDirective) {
  std::string opened = OpenedBlockWriting(StatesFurther(kFurtherWord));
  EXPECT_TRUE(Holds(opened, kSealedDesign));
  EXPECT_FALSE(Holds(opened, kAnyStating));
}

// The same of an offering written without quotation marks, which is the
// unquoted spelling's second half: it is taken as the value above, and it is
// kept out of the block here. What is withheld is the expression, however the
// value against the keyword was spelled, so the two readings of a line -- the
// one that holds it back and the one that takes the value -- admit the same
// spellings, and one unquoted case answers for the rest of them here as it
// does there.
TEST(ProtectAuthorInfoDescription, AnOfferingWrittenAsAnIdentifierIsKeptOut) {
  std::string named = "`pragma protect author_info=analytical_society\n";
  std::string opened = OpenedBlockWriting(named);
  EXPECT_TRUE(Holds(opened, kSealedDesign));
  EXPECT_FALSE(Holds(opened, kAnyStating));
}

// The value form that keeps the two halves of this rule honest. A string with
// nothing between its quotation marks is the expression, so the line carrying
// it is held back from the block like any other -- and a reading that decided
// what to withhold by looking at the value rather than at the expression would
// seal this line with the design while the envelope went on offering nothing
// in the clear.
TEST(ProtectAuthorInfoDescription, AnEmptyStringOfferingIsKeptOutOfTheBlock) {
  std::string opened = OpenedBlockWriting(StatesFurther(""));
  EXPECT_TRUE(Holds(opened, kSealedDesign));
  EXPECT_FALSE(Holds(opened, kAnyStating));
}

// The complement of what opening the block shows: the block a region offering
// something about its author is written into is the block written from that
// same region with the offering struck out. The cipher is a function of the
// text and the key, so two blocks written alike were written from the same
// text -- which says the stating line was the whole of what this rule
// withheld, rather than one of several lines that quietly failed to reach the
// block.
TEST(ProtectAuthorInfoDescription, TheBlockIsTheOneTheSilentRegionProduces) {
  std::string offered = Encrypted(RegionWriting(StatesFurther(kFurtherWord)));
  std::string silent = Encrypted(RegionWriting(""));
  EXPECT_FALSE(DataBlockOf(silent).empty());
  EXPECT_EQ(DataBlockOf(offered), DataBlockOf(silent));
}

// The negative, and the pairing that says the spelling rather than the keyword
// did the work: the keyword standing alone offers nothing, so it is not the
// expression this rule keeps out of the block. §34.5.1's rule for the rest of
// the enclosed text governs instead, and the line is sealed with the design.
TEST(ProtectAuthorInfoDescription, TheKeywordStandingAloneIsLeftInTheBlock) {
  std::string bare = "`pragma protect author_info\n";
  EXPECT_FALSE(Holds(Encrypted(RegionWriting(bare)), kAnyStating));
  EXPECT_TRUE(Holds(OpenedBlockWriting(bare), bare));
}

// ---------------------------------------------------------------------------
// ENCRYPTION OUTPUT: otherwise, the expression is copied without change.
// ---------------------------------------------------------------------------

// A text no encryption envelope encloses holds the expression where it was
// written, character for character. Without change is meant of the characters,
// so the spacing positioning the parts of the directive and the comment
// written after them come back as they went in: there is no envelope for the
// expression to be placed inside, and nothing here rewrites it.
TEST(ProtectAuthorInfoDescription, AnExpressionOutsideEveryEnvelopeIsCopied) {
  std::string spaced = "`pragma  protect   author_info  =  ";
  spaced.append("\"Analytical Society, London\" // more\n");
  std::string src = "module m;\n";
  src.append(spaced).append("endmodule\n");
  EXPECT_EQ(Encrypted(src), src);
}

// The position that tells the two halves of the rule apart. The expression
// stands between two regions, so it is inside neither: it is copied where it
// was written rather than lifted into the envelope on either side of it, and
// neither envelope offers anything.
TEST(ProtectAuthorInfoDescription, AnExpressionBetweenTwoRegionsStaysInPlace) {
  std::string inside = ReachesTheKey();
  inside.append(kSealedDesign);
  std::string src = RegionAround(inside);
  src.append(StatesFurther(kFurtherWord));
  src.append(RegionAround(inside));
  std::string written = Encrypted(src);
  EXPECT_EQ(TimesWritten(written, kAnyStating), 1U);
  EXPECT_LT(written.find(kEndProtected), written.find(kAnyStating));
  size_t opens_first = written.find(kBeginProtected);
  size_t opens_second = written.find(kBeginProtected, opens_first + 1);
  EXPECT_LT(written.find(kAnyStating), opens_second);
}

// The same for an expression inside a model an earlier encryption sealed,
// where that model stands outside every encryption envelope. The words
// §34.5.3.1 and §34.5.4.1 define delimit a model rather than a region to be
// encrypted, so there is nothing here for a tool to transform and the whole
// text -- the stating directive an earlier run placed among its description
// included -- goes out exactly as it came in.
TEST(ProtectAuthorInfoDescription, AnExpressionInAPassingSealedModelIsCopied) {
  std::string src = "module m;\n";
  src.append(SealedModelStating(kFurtherWord));
  src.append("endmodule\n");
  EXPECT_EQ(Encrypted(src), src);
}

// A region no key of the tool's reaches is not transformed at all, so the
// expression written inside it is text of the source like everything else
// there and goes back where it stands. There is no envelope for it to be
// placed in and no block for it to be kept out of, so what is left is the
// copying.
TEST(ProtectAuthorInfoDescription, ARegionReachingNoKeyKeepsItsOfferingAsIs) {
  std::string src = RegionWriting(StatesFurther(kFurtherWord));
  EXPECT_EQ(EncryptedWithoutTheKey(src), src);
}

// ---------------------------------------------------------------------------
// DECRYPTION INPUT: none.
// ---------------------------------------------------------------------------

// The round trip. A region offering something about its author comes back as
// the design it was written from, and that offering reaches none of the text
// the compilation step after the preprocessor reads: the expression describes
// the envelope rather than the design, so nothing of it is design text.
TEST(ProtectAuthorInfoDescription, TheOfferingReachesNoneOfTheRecoveredDesign) {
  ReadWithTheKeys read(Encrypted(RegionWriting(StatesFurther(kFurtherWord))));
  EXPECT_FALSE(read.diags.HasErrors());
  EXPECT_TRUE(read.Produced("module sealed_m"));
  EXPECT_FALSE(read.Produced(kFurtherWord));
}

// Drawing nothing from the expression, read as a comparison rather than as an
// absence: two envelopes whose regions differ in nothing but what they offered
// are read to the same text. The offering changed and the reading did not, so
// there is no part of what the reading produces that the offering reached.
TEST(ProtectAuthorInfoDescription, TwoEnvelopesDifferingOnlyInTheOfferingRead) {
  std::string offered = Encrypted(RegionWriting(StatesFurther(kFurtherWord)));
  std::string other =
      Encrypted(RegionWriting(StatesFurther(kOtherFurtherWord)));
  ASSERT_NE(offered, other);
  ReadWithTheKeys read(offered);
  ReadWithTheKeys read_other(other);
  EXPECT_FALSE(read.diags.HasErrors());
  EXPECT_FALSE(read_other.diags.HasErrors());
  EXPECT_EQ(read.produced, read_other.produced);
}

// Where the directive stands among an envelope's description is not something
// a reader gets to settle, another producer having written its expressions in
// whatever order it chose. This is a real produced envelope with the offering
// moved to stand past the block, and the reading takes as much from it there
// as it took from it before: nothing, and the design still comes back.
TEST(ProtectAuthorInfoDescription, AnOfferingPastTheBlockCostsTheReadingNone) {
  std::string moved = WithTheStatementMovedPastTheBlock(
      Encrypted(RegionWriting(StatesFurther(kFurtherWord))));
  ASSERT_LT(moved.find("`pragma protect data_block=\""),
            moved.find(StatesFurther(kFurtherWord)));
  ReadWithTheKeys read(moved);
  EXPECT_FALSE(read.diags.HasErrors());
  EXPECT_TRUE(read.Produced("module sealed_m"));
  EXPECT_FALSE(read.Produced(kFurtherWord));
}

// An envelope written by hand in §34.5.3.1's and §34.5.4.1's words, carrying
// this expression and nothing else. There is nothing here to draw on and
// nothing missed by not drawing on it: the envelope is opened and closed, the
// offering reaches none of the design text, and the source standing on either
// side of the envelope arrives at the step after the preprocessor as it was
// written.
TEST(ProtectAuthorInfoDescription, AnEnvelopeStatingOnlyAnOfferingIsClosed) {
  std::string envelope(kBeginProtected);
  envelope.append(StatesFurther(kFurtherWord)).append(kEndProtected);
  ReadWithTheKeys read("module m;\n" + envelope + "endmodule\n");
  EXPECT_FALSE(read.diags.HasErrors());
  EXPECT_EQ(read.Closed(), 1U);
  EXPECT_EQ(read.StillOpen(), 0U);
  EXPECT_FALSE(read.Produced(kFurtherWord));
  EXPECT_TRUE(read.Produced("endmodule"));
}

// The closest input this heading has to turn away. §34.5.12's expression is
// one a reading really does draw on -- it is how the key that opens the block
// is picked out -- and here the very characters it carried are written against
// this keyword instead. Drawing nothing from the expression, the reading is
// left with no key for the block, and the design stays sealed.
//
// The envelope the characters were moved in is the one read above, where the
// key stands under §34.5.12's own keyword and the design comes back. That
// reading is this one's control: the two differ in which keyword the
// characters were written against and in nothing else, so it is the keyword
// that kept the design sealed here rather than anything about the envelope.
TEST(ProtectAuthorInfoDescription, AnOfferingSpellingAKeyNameOpensNothing) {
  std::string replaced = WithTheKeyNameWrittenAsTheStatement(
      Encrypted(RegionWriting(StatesFurther(kFurtherWord))));
  ASSERT_TRUE(Holds(replaced, StatesFurther(kKeyName)));
  ReadWithTheKeys read(replaced);
  EXPECT_TRUE(read.diags.HasErrors());
  EXPECT_FALSE(read.Produced("module sealed_m"));
}

}  // namespace
