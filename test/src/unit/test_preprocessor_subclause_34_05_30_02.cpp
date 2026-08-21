// §34.5.30.2 Description, for the protect pragma keyword carrying
// documentation nothing goes on to interpret. The syntax block above it settles
// how the expression is spelled; this one settles what a tool does with one,
// under each of the two headings the subclause writes rules under.
//
// ENCRYPTION INPUT. The expression can be found anywhere in an input file, and
// even where it is found inside a begin-end block the value is output as a
// comment in cleartext immediately prior to the data_block. The subclause
// states what that is for: a copyright notice included from another file into a
// region would otherwise be sealed with the design, and unreadable to everybody
// it was written for. It gives a second reason of its own -- the value would be
// known cleartext inside the data_block -- and concludes that the pragma itself
// and the value should not be included in the encrypted text.
//
// ENCRYPTION OUTPUT. The entire comment including the beginning pragma is
// output in cleartext immediately prior to the data_block corresponding to the
// begin-end in which the comment was found. Two claims stand in that sentence
// and this file separates them: what is output is the directive rather than the
// bare value, and where it is output is ahead of the data_block rather than
// anywhere in the clear.
//
// DECRYPTION INPUT: none. A tool reading a protected envelope draws nothing
// from the expression, so an envelope carrying one is read exactly as far as an
// envelope carrying none.
//
// All of it is preprocessor-stage. src/preprocessor/protect_processing.cpp
// carries the encrypting half: it reads each line an encryption envelope
// encloses for the expression, keeps the directive beside the region rather
// than among the lines that are about to stop being readable, and holds the
// line carrying it back from the text the block records.
// src/preprocessor/protect_envelope_output.cpp writes the directive into the
// envelope taking that region's place, at the position this subclause names,
// and src/preprocessor/protect_keywords.cpp spells the directive.
// src/preprocessor/protect_pragma_line.cpp is the reading of a line that
// settles which keyword a directive named and what was written against it. The
// decrypting half is src/preprocessor/preprocessor.cpp, which consumes the
// directive like any other protect pragma and takes nothing from it.
//
// The inputs are the real syntax of the dependencies this rule consumes.
// §34.5.1.1 and §34.5.2.1 delimit the regions being encrypted, §34.5.10's
// data_keyowner and §34.5.12's data_keyname are the names a region reaches its
// key through, §34.5.15's data_block is where the text a region sealed is
// carried, §34.5.9's encoding states the count of what that block holds, and
// §34.5.27's key_block carries the key an envelope's own reader opens it with.
// §34.5.3.1's word opens each model an earlier encryption sealed already and
// §34.5.4.1's word closes it; §34.5.3 leaves the expressions inside such a
// model uninterpreted, which is the position this rule is hardest in. The
// models below are written by running the encrypting half over a region of
// their own rather than spelled by hand, so the words delimiting them and the
// documenting directive inside them are a tool's.

#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>

#include "helpers_protect_region.h"
#include "helpers_text_lines.h"

using namespace delta;

namespace {

// The documentation a region writes against the keyword, and a second notice
// for the inputs that write one region against another. Both hold spaces, so a
// notice standing in a produced text can only have arrived there as the value
// of an expression rather than as a stray word of the source.
constexpr std::string_view kNotice = "Copyright 2026 Acme Corp";
constexpr std::string_view kOtherNotice = "Patent pending, Acme Corp";

// The opening of any directive carrying the expression, for the readings that
// ask whether an envelope documents anything at all rather than what.
constexpr std::string_view kAnyDocumenting = "`pragma protect comment";

// The opening of §34.5.9's expression, which is the one directive this
// subclause allows between the comment and the block: that subclause states the
// count against the block it counts, so the comment stands ahead of the count
// rather than between the count and the block.
constexpr std::string_view kBlockCounting = "`pragma protect encoding=";

// The opening of any protect pragma directive at all, for the reading that asks
// what stands between the comment and the block rather than whether one named
// expression does.
constexpr std::string_view kAnyDirective = "`pragma protect ";

// A data key name this tool holds no key under, which is what sends a region to
// §34.5.27's key blocks rather than to a key of its author's.
constexpr std::string_view kUnheldDataKeyName = "design-2027";

// The expression this subclause is about, carrying `notice` as the string
// §34.5.30.1 spells the value as.
//
// It serves both sides. A source text documents itself by writing this, and an
// encrypting tool outputting the entire comment including the beginning pragma
// writes the same thing, so what a tool produced is compared against the
// spelling an input was built from.
std::string Documents(std::string_view notice) {
  std::string text = "`pragma protect comment=\"";
  text.append(notice).append("\"\n");
  return text;
}

// A model an earlier encryption sealed already, documenting itself with
// `notice`.
//
// Nothing of it is spelled by hand: it is what the encrypting half writes from
// a region of its own, so the words §34.5.3.1 and §34.5.4.1 define delimit it
// because a tool put them there, and the documenting directive standing in the
// clear inside it is one this very rule placed on an earlier run.
std::string SealedModelDocumenting(std::string_view notice) {
  return Encrypted(RegionWriting(Documents(notice)));
}

// The characters of `written` standing between the end of the directive
// carrying `notice` and the beginning of §34.5.15's expression.
//
// This is how "immediately prior to the data_block" is read: not as the comment
// standing somewhere earlier in the envelope, but as nothing of the envelope's
// description standing between the two beyond the count §34.5.9 owes the block.
// A text the directive was not found in comes back whole, so a test asking what
// separates the two fails on the envelope that never carried the comment at
// all.
std::string BetweenTheCommentAndTheBlock(const std::string& written,
                                         std::string_view notice) {
  std::string documenting = Documents(notice);
  size_t at = written.find(documenting);
  if (at == std::string::npos) return written;
  size_t from = at + documenting.size();
  size_t to = written.find(kBlockOpening, from);
  if (to == std::string::npos) return written;
  return written.substr(from, to - from);
}

// A region whose data are sealed behind §34.5.27's key blocks, writing
// `written` inside itself.
//
// It names its data key by a name this tool holds nothing under, so there is no
// key of the author's for the block to stay under, and it designates a reader
// whose key the tool does hold, so a key block is written for that reader. The
// envelope it produces is the one that puts something between the description
// and the data_block, which is the position where a comment placed merely
// somewhere in the clear parts company with a comment placed immediately prior
// to the block.
std::string RegionBehindAKeyBlock(std::string_view written) {
  std::string inside = "`pragma protect data_keyowner=\"";
  inside.append(kKeyOwner).append("\"\n");
  inside.append("`pragma protect data_keyname=\"");
  inside.append(kUnheldDataKeyName).append("\"\n");
  inside.append("`pragma protect key_keyowner=\"");
  inside.append(kKeyOwner).append("\"\n");
  inside.append("`pragma protect key_keyname=\"");
  inside.append(kKeyName).append("\"\n");
  inside.append(written).append(kSealedDesign);
  return RegionAround(inside);
}

// ---------------------------------------------------------------------------
// ENCRYPTION OUTPUT: the entire comment including the beginning pragma is
// output in cleartext.
// ---------------------------------------------------------------------------

// The rule at its plainest. A region documenting itself and sealing a design
// produces an envelope carrying the whole directive in the clear, once, while
// the design it enclosed is sealed. It is the entire comment rather than the
// value alone: the beginning pragma stands in front of the notice, so a reader
// holding no key learns what the notice was written against.
TEST(ProtectCommentDescription, TheEntireCommentIncludingThePragmaIsOutput) {
  std::string written = Encrypted(RegionWriting(Documents(kNotice)));
  EXPECT_FALSE(Holds(written, kSealedDesign));
  EXPECT_EQ(TimesWritten(written, Documents(kNotice)), 1U);
}

// Where in the produced text it stands: between the two expressions delimiting
// the protected envelope, so a reader that reached the envelope reached the
// comment inside it rather than finding it loose in the file.
TEST(ProtectCommentDescription, TheOutputCommentStandsInsideTheEnvelope) {
  std::string written = Encrypted(RegionWriting(Documents(kNotice)));
  EXPECT_LT(written.find(kBeginProtected), written.find(kAnyDocumenting));
  EXPECT_LT(written.find(kAnyDocumenting), written.find(kEndProtected));
}

// The negative, which says the expression rather than the keyword is what is
// output: a region whose text documents nothing has no comment to output, and
// the envelope taking its place carries no such directive.
TEST(ProtectCommentDescription, ARegionDocumentingNothingOutputsNoComment) {
  std::string written = Encrypted(RegionWriting(""));
  EXPECT_TRUE(Holds(written, kBeginProtected));
  EXPECT_FALSE(Holds(written, kAnyDocumenting));
}

// The value form where two quantities part company: a string with nothing
// between its quotation marks was written, and what it holds is nothing at all.
// A reading that asked whether the region documented anything, rather than
// whether it wrote the expression, would take this for a region that wrote no
// comment -- and every other value here would let that reading pass. §34.5.30.2
// asks for the entire comment, and a comment whose value is empty is a comment
// the region wrote.
TEST(ProtectCommentDescription, AnEmptyStringAgainstTheKeywordIsOutput) {
  std::string written = Encrypted(RegionWriting(Documents("")));
  EXPECT_FALSE(Holds(written, kSealedDesign));
  EXPECT_TRUE(Holds(written, Documents("")));
}

// The verbatim half of "the entire comment". §22.5.1 gives a pragma_value more
// than one spelling, and §22.11 makes a bare value a legal identifier or number
// rather than anything a hyphen may sit in. A notice written as an identifier
// is output as that identifier: rewriting it in quotation marks would output a
// different pragma_value from the one the input file wrote, and the subclause
// asks for the comment the input held.
TEST(ProtectCommentDescription, ANoticeWrittenBareIsOutputBare) {
  std::string bare = "`pragma protect comment=copyright_acme_2026\n";
  std::string written = Encrypted(RegionWriting(bare));
  EXPECT_TRUE(Holds(written, bare));
  EXPECT_FALSE(Holds(written, "comment=\"copyright_acme_2026\""));
}

// The negative of the spelling, and the pairing that says the expression did
// the work: §22.5.1's other pragma_value spelling is a parenthesized list of
// further expressions, which is not the one written thing §34.5.30.1 defines
// the value as. A reading that took it would output somebody's subkeywords in
// the clear where a copyright notice belongs, so the line is left to §34.5.1's
// rule for the rest of the enclosed text and sealed with the design.
TEST(ProtectCommentDescription, AParenthesizedListDocumentsNothing) {
  std::string listed = "`pragma protect comment=(notice=\"acme\")\n";
  std::string written = Encrypted(RegionWriting(listed));
  EXPECT_TRUE(Holds(written, kBeginProtected));
  EXPECT_FALSE(Holds(written, kAnyDocumenting));
  EXPECT_TRUE(Holds(OpenedBlockWriting(listed), listed));
}

// ---------------------------------------------------------------------------
// ENCRYPTION OUTPUT: immediately prior to the data_block.
// ---------------------------------------------------------------------------

// The position the subclause names, read as the position it is. The comment
// stands ahead of §34.5.15's expression, and the only thing the envelope writes
// between the two is the count §34.5.9 owes that block -- a count that
// subclause states against the block it counts, so it cannot be lifted over the
// comment.
TEST(ProtectCommentDescription, TheCommentStandsImmediatelyPriorToTheBlock) {
  std::string written = Encrypted(RegionWriting(Documents(kNotice)));
  EXPECT_LT(written.find(Documents(kNotice)), written.find(kBlockOpening));
  std::string between = BetweenTheCommentAndTheBlock(written, kNotice);
  EXPECT_EQ(TimesWritten(between, kAnyDirective), 1U);
  EXPECT_TRUE(Holds(between, kBlockCounting));
}

// The same position in the envelope that has something to place wrongly.
// §34.5.27 has a key block written into the envelope ahead of the block its key
// opens, so this envelope carries a description, then a key block, then the
// data_block. A comment written merely somewhere in the clear could stand ahead
// of the key block and satisfy every reading above; immediately prior to the
// data_block puts it after.
TEST(ProtectCommentDescription, TheCommentFollowsTheKeyBlockOfItsEnvelope) {
  std::string written = Encrypted(RegionBehindAKeyBlock(Documents(kNotice)));
  ASSERT_TRUE(Holds(written, "`pragma protect key_block\n")) << written;
  EXPECT_LT(written.find("`pragma protect key_block\n"),
            written.find(Documents(kNotice)));
  std::string between = BetweenTheCommentAndTheBlock(written, kNotice);
  EXPECT_EQ(TimesWritten(between, kAnyDirective), 1U);
}

// Several comments in one region, each owed its own line. §34.5.30.2 asks for
// the entire comment of each begin-end the comment was found in, and this
// region wrote two: both are output, in the order the region wrote them, and
// both ahead of the block. A tool keeping one value per region would output the
// second and seal the first, which is the fate the subclause exists to spare a
// notice.
TEST(ProtectCommentDescription, TwoCommentsAreOutputInTheOrderWritten) {
  std::string both = Documents(kNotice);
  both.append(Documents(kOtherNotice));
  std::string written = Encrypted(RegionWriting(both));
  EXPECT_LT(written.find(Documents(kNotice)),
            written.find(Documents(kOtherNotice)));
  EXPECT_LT(written.find(Documents(kOtherNotice)), written.find(kBlockOpening));
}

// One directive carrying this subclause's expression beside §34.5.5's, which is
// the position that tells the two apart: §22.5.1 lets one directive carry a
// list of expressions, and each keyword is output through the directive its own
// subclause defines. The line went into neither block and came back as two
// directives, so the comment was read off the line rather than the line copied.
TEST(ProtectCommentDescription, ACommentBesideAnAuthorIsOutputOnItsOwnLine) {
  std::string listed = "`pragma protect author=\"Ada Lovelace\", comment=\"";
  listed.append(kNotice).append("\"\n");
  std::string written = Encrypted(RegionWriting(listed));
  EXPECT_TRUE(Holds(written, Documents(kNotice)));
  EXPECT_TRUE(Holds(written, "`pragma protect author=\"Ada Lovelace\"\n"));
}

// ---------------------------------------------------------------------------
// ENCRYPTION INPUT: the pragma itself and the value are not included in the
// encrypted text, because they would be known cleartext inside the data_block.
// ---------------------------------------------------------------------------

// The rule observed where it is decided: the block is opened with the key the
// region was sealed under and read. The design the region held is in there, and
// neither the keyword nor the notice written against it is -- so there is no
// stretch of the block an attacker knows the plaintext of.
TEST(ProtectCommentDescription, TheOpenedBlockHoldsNeitherPragmaNorValue) {
  std::string recovered = OpenedBlockWriting(Documents(kNotice));
  EXPECT_TRUE(Holds(recovered, kSealedDesign));
  EXPECT_FALSE(Holds(recovered, kAnyDocumenting));
  EXPECT_FALSE(Holds(recovered, kNotice));
}

// The same for the value form that keeps the two halves of this rule honest. A
// string with nothing between its quotation marks is the expression, so the
// line carrying it is held back from the block like any other -- and a reading
// that decided what to withhold by looking at the value rather than at the
// expression would seal this line while the envelope went on documenting
// nothing in the clear.
TEST(ProtectCommentDescription, AnEmptyStringCommentIsKeptOutOfTheBlock) {
  std::string recovered = OpenedBlockWriting(Documents(""));
  EXPECT_TRUE(Holds(recovered, kSealedDesign));
  EXPECT_FALSE(Holds(recovered, kAnyDocumenting));
}

// The complement of what opening the block shows: the block a documented region
// is written into is the block written from that same region with the comment
// struck out. The cipher is a function of the text and the key, so two blocks
// written alike were written from the same text -- which says the comment line
// was the whole of what this rule withheld, rather than one of several lines
// that quietly failed to reach the block.
TEST(ProtectCommentDescription, TheBlockIsTheOneTheSilentRegionProduces) {
  std::string documented = Encrypted(RegionWriting(Documents(kNotice)));
  std::string silent = Encrypted(RegionWriting(""));
  EXPECT_FALSE(DataBlockOf(silent).empty());
  EXPECT_EQ(DataBlockOf(documented), DataBlockOf(silent));
}

// The negative, and the pairing that says the spelling rather than the keyword
// did the work: the keyword standing alone writes no value, so it is not the
// expression this rule keeps out of the block. §34.5.1's rule for the rest of
// the enclosed text governs instead, and the line is sealed with the design.
TEST(ProtectCommentDescription, TheKeywordStandingAloneIsLeftInTheBlock) {
  std::string alone = "`pragma protect comment\n";
  EXPECT_FALSE(Holds(Encrypted(RegionWriting(alone)), kAnyDocumenting));
  EXPECT_TRUE(Holds(OpenedBlockWriting(alone), alone));
}

// ---------------------------------------------------------------------------
// The comment found in the begin-end, and no other.
// ---------------------------------------------------------------------------

// The control for everything above. A comment written outside every encryption
// envelope is not lifted onto either envelope beside it: there is no begin-end
// it was found in, so it is copied where it stands. Without this, every case
// above would be satisfied by a tool that copied the keyword onto every
// envelope it wrote.
TEST(ProtectCommentDescription, ACommentOutsideEveryRegionIsCopiedInPlace) {
  std::string src = RegionWriting("");
  src.append(Documents(kNotice));
  src.append(RegionWriting(""));
  std::string written = Encrypted(src);
  EXPECT_EQ(TimesWritten(written, kAnyDocumenting), 1U);
  EXPECT_LT(written.find(kEndProtected), written.find(kAnyDocumenting));
  size_t first = written.find(kBeginProtected);
  EXPECT_LT(written.find(kAnyDocumenting),
            written.find(kBeginProtected, first + 1));
}

// A text no encryption envelope encloses at all comes back character for
// character. There is no data_block for the comment to be placed prior to, so
// nothing here rewrites it.
TEST(ProtectCommentDescription, ACommentInAnUnencryptedFileIsUnchanged) {
  std::string src = "module m;\n";
  src.append(Documents(kNotice));
  src.append("endmodule\n");
  EXPECT_EQ(Encrypted(src), src);
}

// A region no key of the tool's reaches is not transformed at all, so the
// comment written inside it is text of the source like everything else there.
// There is no envelope for it to be output on and no block for it to be kept
// out of, so what is left is the copying.
TEST(ProtectCommentDescription, ARegionReachingNoKeyKeepsItsCommentAsWritten) {
  std::string src = RegionWriting(Documents(kNotice));
  EXPECT_EQ(EncryptedWithoutTheKey(src), src);
}

// The comment output is the one this envelope's own begin-end held. §34.5.3
// leaves the expressions of a previously generated protected block
// uninterpreted, so a comment written inside one documents a design some
// earlier encryption sealed: this envelope outputs the notice its own region
// wrote, once, and says nothing about the other.
TEST(ProtectCommentDescription, ACommentInAnEnclosedSealedModelIsNotOutput) {
  std::string enclosed = ReachesTheKey();
  enclosed.append(Documents(kNotice));
  enclosed.append(SealedModelDocumenting(kOtherNotice));
  enclosed.append(kSealedDesign);
  std::string written = Encrypted(RegionAround(enclosed));
  EXPECT_EQ(TimesWritten(written, Documents(kNotice)), 1U);
  EXPECT_FALSE(Holds(written, kOtherNotice));
}

// Where that notice went instead, which no absence from the produced text can
// show: §34.5.1 has the sealed model travel into the enclosing block as the
// bytes it is written with, its own delimiters and the documenting directive an
// earlier run output inside it included. It was carried across rather than
// dropped, and this rule reached none of it.
TEST(ProtectCommentDescription,
     ACommentInAnEnclosedSealedModelReachesTheBlock) {
  std::string enclosed = ReachesTheKey();
  enclosed.append(SealedModelDocumenting(kOtherNotice));
  enclosed.append(kSealedDesign);
  std::string recovered = OpenedBlockOf(Encrypted(RegionAround(enclosed)));
  EXPECT_TRUE(Holds(recovered, kBeginProtected));
  EXPECT_TRUE(Holds(recovered, Documents(kOtherNotice)));
}

// Each envelope outputs the comment of its own begin-end. The second region
// here documents nothing, so the envelope standing in its place documents
// nothing -- the notice the first region wrote belongs to the first block, and
// an envelope separated from the one before it says exactly what it said where
// it stood.
TEST(ProtectCommentDescription, AnEnvelopeOutputsOnlyItsOwnRegionsComment) {
  std::string second = ReachesTheKey();
  second.append("module other_m; endmodule\n");
  std::string written =
      Encrypted(RegionWriting(Documents(kNotice)) + RegionAround(second));
  EXPECT_EQ(TimesWritten(written, kBeginProtected), 2U);
  EXPECT_EQ(TimesWritten(written, kAnyDocumenting), 1U);
  size_t opened = written.find(kBeginProtected);
  EXPECT_LT(written.find(kAnyDocumenting),
            written.find(kBeginProtected, opened + 1));
}

// ---------------------------------------------------------------------------
// DECRYPTION INPUT: none.
// ---------------------------------------------------------------------------

// The round trip. A documented region comes back as the design it was written
// from, and the notice reaches none of the text the compilation step after the
// preprocessor reads: the comment describes the envelope rather than the
// design, so nothing of it is design text.
TEST(ProtectCommentDescription, TheNoticeReachesNoneOfTheRecoveredDesign) {
  ReadWithTheKeys read(Encrypted(RegionWriting(Documents(kNotice))));
  EXPECT_FALSE(read.diags.HasErrors());
  EXPECT_TRUE(read.Produced("module sealed_m"));
  EXPECT_FALSE(read.Produced(kNotice));
}

// Drawing nothing from the expression, read as a comparison rather than as an
// absence: two envelopes whose regions differ in nothing but the notice they
// documented are read to the same text. The notice changed and the reading did
// not, so there is no part of what the reading produces that the notice
// reached.
TEST(ProtectCommentDescription, TwoEnvelopesDifferingOnlyInTheNoticeReadAlike) {
  std::string one = Encrypted(RegionWriting(Documents(kNotice)));
  std::string other = Encrypted(RegionWriting(Documents(kOtherNotice)));
  ASSERT_NE(one, other);
  ReadWithTheKeys read_one(one);
  ReadWithTheKeys read_other(other);
  EXPECT_FALSE(read_one.diags.HasErrors());
  EXPECT_FALSE(read_other.diags.HasErrors());
  EXPECT_EQ(read_one.produced, read_other.produced);
}

// An envelope written by hand in §34.5.3.1's and §34.5.4.1's words, carrying
// this expression and nothing else. There is nothing here to draw on and
// nothing missed by not drawing on it: the envelope is opened and closed, the
// notice reaches none of the design text, and the source standing on either
// side of the envelope arrives at the step after the preprocessor as it was
// written.
TEST(ProtectCommentDescription, AnEnvelopeCarryingOnlyACommentIsReadAndClosed) {
  std::string envelope(kBeginProtected);
  envelope.append(Documents(kNotice)).append(kEndProtected);
  ReadWithTheKeys read("module m;\n" + envelope + "endmodule\n");
  EXPECT_FALSE(read.diags.HasErrors());
  EXPECT_EQ(read.Closed(), 1U);
  EXPECT_EQ(read.StillOpen(), 0U);
  EXPECT_FALSE(read.Produced(kNotice));
  EXPECT_TRUE(read.Produced("endmodule"));
}

}  // namespace
