// §34.5.5.2 Description, for the protect pragma keyword that names whoever
// wrote the IP an envelope carries. The syntax block above it settles how the
// expression is spelled; this one settles what a tool does with one, under each
// of the three headings the subclause writes its rules under.
//
// ENCRYPTION INPUT. The value written against the keyword is a string
// identifying the IP author by name. The subclause states why the keyword is
// tabulated at all: it is a keyword of its own rather than one reading of the
// keyword carrying uninterpreted documentation, so whatever wants the author
// looks at this name instead of parsing a documentation string for one.
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
// encloses for the expression, keeps the name beside the region rather than
// among the lines that are about to stop being readable, and holds the line
// carrying it back from the text the block records.
// src/preprocessor/protect_envelope_output.cpp writes the name into the
// envelope taking that region's place, through the directive
// src/preprocessor/protect_keywords.cpp spells, and
// src/preprocessor/protect_pragma_line.cpp is the reading of a line that
// settles which keyword a directive named and what was written against it. The
// decrypting half is src/preprocessor/preprocessor.cpp, which consumes the
// directive like any other protect pragma and takes nothing from it.
//
// The inputs are the real syntax of the dependencies this rule consumes.
// §34.5.3.1's word opens each model an earlier encryption sealed already and
// §34.5.4.1's word closes it, and those models are the position the rule is
// hardest in: a name written inside one belongs to a design somebody else
// sealed, so it is neither placed on the new envelope nor lifted out of the
// bytes travelling into its block. The models below are written by running the
// encrypting half over a region of its own rather than spelled by hand, so the
// words delimiting them and the naming directive inside them are a tool's.
// §34.5.1.1 and §34.5.2.1 delimit the regions being encrypted, §34.5.10's
// data_keyowner and §34.5.12's data_keyname are the names a region reaches its
// key through, and §34.5.15's data_block is where the text a region sealed is
// carried. Every text below is written as directive syntax and driven through
// the encrypting half, the preprocessor, or both in turn, rather than handed to
// the envelope state by hand.

#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_envelope.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

// The entity every region below names as having provided the key its data are
// under, the name that picks that key out of the entity's list, and the key
// itself. A region that came back sealed came back sealed because the first two
// really reached the third.
constexpr std::string_view kKeyOwner = "acme";
constexpr std::string_view kKeyName = "acme-2026";
constexpr std::string_view kRegionKey = "acme-region-exchange-key";

// The name a region writes against the keyword, and a second name for the
// inputs that write one region against another. Both hold a space, so a name
// standing in a produced text can only have arrived there as the value of an
// expression rather than as a stray word of the source.
constexpr std::string_view kAuthorName = "Ada Lovelace";
constexpr std::string_view kOtherAuthorName = "Grace Hopper";

// The opening of any directive carrying the expression, for the readings that
// ask whether an envelope names an author at all rather than which one.
constexpr std::string_view kAnyNaming = "`pragma protect author";

// The design a region seals. Nothing of it survives the alphabet an encrypted
// block is written in, so finding it outside a block is finding a region that
// was never sealed, and finding it in what a reading produced is finding a
// block that opened.
constexpr std::string_view kSealedDesign = "module sealed_m; endmodule\n";

// The two words §34.5.3.1 and §34.5.4.1 define, which delimit a model an
// encryption sealed already -- as the encrypting half writes them, and as a
// text carrying somebody else's sealed model writes them.
constexpr std::string_view kBeginProtected =
    "`pragma protect begin_protected\n";
constexpr std::string_view kEndProtected = "`pragma protect end_protected\n";

// The directive a produced envelope states the name of its key on, as
// §34.5.12's keyword spells it. It is the line the reading really does draw on,
// which is what makes it the thing to write this subclause's expression in the
// place of.
constexpr std::string_view kKeyNameDirective =
    "`pragma protect data_keyname=\"acme-2026\"\n";

bool Holds(std::string_view text, std::string_view needle) {
  return text.find(needle) != std::string_view::npos;
}

// How many times `needle` is written in `text`.
size_t Occurrences(std::string_view text, std::string_view needle) {
  size_t count = 0;
  size_t pos = text.find(needle);
  while (pos != std::string_view::npos) {
    ++count;
    pos = text.find(needle, pos + 1);
  }
  return count;
}

// The one key every region below reaches, held under the names that select it.
ProtectKeyList RegionKeys() {
  ProtectKeyList keys;
  keys.Add(
      {std::string(kKeyOwner), std::string(kKeyName), std::string(kRegionKey)});
  return keys;
}

// A key of the same entity held under some other name, for the region that
// reaches no key at all. A tool holding this has keys, and none of them is the
// one the region asked for, so a region left untransformed was left so for want
// of its own key rather than for want of any.
ProtectKeyList KeysReachingNothing() {
  ProtectKeyList keys;
  keys.Add(
      {std::string(kKeyOwner), "some-other-key-name", std::string(kRegionKey)});
  return keys;
}

// The two expressions naming that key, as §34.5.10 and §34.5.12 write them.
std::string NamesTheKey() {
  std::string text = "`pragma protect data_keyowner=\"";
  text.append(kKeyOwner).append("\"\n");
  text.append("`pragma protect data_keyname=\"");
  text.append(kKeyName).append("\"\n");
  return text;
}

// The expression this subclause is about, carrying `name` as the string it
// specifies.
//
// It serves both sides. A source text names its author by writing this, and an
// encrypting tool placing the expression inside the envelope writes the same
// thing, so what a tool produced is compared against the spelling an input was
// built from.
std::string NamesAuthor(std::string_view name) {
  std::string text = "`pragma protect author=\"";
  text.append(name).append("\"\n");
  return text;
}

// One encryption envelope: §34.5.1.1's and §34.5.2.1's words with `enclosed`
// between them.
std::string Region(const std::string& enclosed) {
  std::string text = "`pragma protect begin\n";
  text.append(enclosed);
  text.append("`pragma protect end\n");
  return text;
}

// One such region carrying `written` between the naming of its key and the
// design it seals.
//
// The key naming comes first so that every region here is one there is
// something to encrypt in, and the design comes last so that a `written` the
// reading passed over is a `written` that went into the block ahead of it.
std::string RegionWriting(std::string_view written) {
  std::string enclosed = NamesTheKey();
  enclosed.append(written).append(kSealedDesign);
  return Region(enclosed);
}

// The text standing where the encryption envelopes of `src` were written, for a
// tool holding the key those regions name.
std::string Encrypted(const std::string& src) {
  return EncryptEnvelopes(src, "", RegionKeys());
}

// The same, for a tool holding a key of that entity under another name.
std::string EncryptedWithoutTheirKey(const std::string& src) {
  return EncryptEnvelopes(src, "", KeysReachingNothing());
}

// The characters recording one envelope's sealed region: what stands between
// the quotation marks of its data_block expression, and empty where the text
// carries no such expression.
std::string DataBlockOf(const std::string& text) {
  constexpr std::string_view kOpening = "`pragma protect data_block=\"";
  size_t at = text.find(kOpening);
  if (at == std::string::npos) return {};
  size_t start = at + kOpening.size();
  size_t end = text.find('"', start);
  if (end == std::string::npos) return {};
  return text.substr(start, end - start);
}

// The text that block records, recovered under the key the region was sealed
// with, and empty where the block does not open.
//
// A rule about what a block shall not hold is settled by opening the block and
// looking. The characters a block is written as say nothing about what went
// into it, so a reading that only searched the produced text could not tell a
// line that was kept out of the block from one that is in there unreadably.
std::string OpenedBlockOf(const std::string& envelope) {
  std::string cleartext;
  if (!DecryptProtectedRegion(DataBlockOf(envelope), kRegionKey, &cleartext)) {
    return {};
  }
  return cleartext;
}

// The same, over a region writing `written` inside itself.
std::string OpenedBlockWriting(std::string_view written) {
  return OpenedBlockOf(Encrypted(RegionWriting(written)));
}

// A model an earlier encryption sealed already, naming `name` as the author of
// the design it holds.
//
// Nothing of it is spelled by hand: it is what the encrypting half writes from
// a region of its own, so the words §34.5.3.1 and §34.5.4.1 define delimit it
// because a tool put them there, and the naming directive standing in the clear
// inside it is one this very rule placed on an earlier run.
std::string SealedModelNaming(std::string_view name) {
  return Encrypted(RegionWriting(NamesAuthor(name)));
}

// A source text read through the preprocessor by a tool holding the region
// keys, with the text the reading produced and what the reading left behind.
//
// Which envelopes the reading opened and closed is state the preprocessor
// carries from one directive to the next rather than anything the output text
// shows, so the Preprocessor outlives the call.
struct ReadSource {
  static PreprocConfig KeyConfig() {
    PreprocConfig config;
    config.protect_keys = RegionKeys();
    return config;
  }

  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp;
  std::string text;

  explicit ReadSource(const std::string& src) : pp(mgr, diag, KeyConfig()) {
    text = pp.Preprocess(mgr.AddFile("<test>", src));
  }

  // How many protected envelopes the reading is still inside where the text
  // ends, and how many it opened and then closed.
  size_t OpenEnvelopes() const {
    return pp.ProtectEnvelopes().DecryptionEnvelopeDepth();
  }
  size_t ClosedEnvelopes() const {
    return pp.ProtectEnvelopes().ClosedEnvelopes().size();
  }

  bool Holds(std::string_view needle) const {
    return text.find(needle) != std::string::npos;
  }
};

// `written` with the directive naming its author taken out of the envelope's
// description and written again just past the block, on the line before the
// word that closes the envelope.
//
// An envelope cannot be spelled by hand for this -- what its block holds
// depends on the key the region was sealed under -- so an envelope whose naming
// stands somewhere else is made by moving that directive inside a real produced
// one. A text the directive was not found in comes back as it stands, and the
// expectations of the test that asked for the move then fail on the envelope
// that was never altered.
std::string WithTheNamingMovedPastTheBlock(const std::string& written) {
  std::string naming = NamesAuthor(kAuthorName);
  size_t at = written.find(naming);
  if (at == std::string::npos) return written;
  std::string moved(written);
  moved.erase(at, naming.size());
  size_t closing = moved.find(kEndProtected);
  if (closing == std::string::npos) return written;
  moved.insert(closing, naming);
  return moved;
}

// `written` with the directive naming the key its block is under replaced by
// this subclause's expression carrying that very name.
//
// The characters a reader would have drawn the key from are still in the
// envelope, and the only thing that changed is which keyword they were written
// against. It is the closest input the decryption rule has to turn away: an
// expression that looks in every respect like the one thing a reader does take
// from an envelope's description, and that a reader takes nothing from.
std::string WithTheKeyNameWrittenAsTheNaming(const std::string& written) {
  size_t at = written.find(kKeyNameDirective);
  if (at == std::string::npos) return written;
  std::string replaced(written);
  replaced.replace(at, kKeyNameDirective.size(), NamesAuthor(kKeyName));
  return replaced;
}

// ---------------------------------------------------------------------------
// ENCRYPTION INPUT: the expression specifies the name of the IP author.
// ---------------------------------------------------------------------------

// The rule at its plainest. The string a region wrote against the keyword is
// the name the envelope taking that region's place states, and the design the
// region held is sealed rather than standing in the clear beside it.
TEST(ProtectAuthorDescription, TheStringAgainstTheKeywordIsTheNameStated) {
  std::string written = Encrypted(RegionWriting(NamesAuthor(kAuthorName)));
  EXPECT_FALSE(Holds(written, kSealedDesign));
  EXPECT_TRUE(Holds(written, NamesAuthor(kAuthorName)));
}

// §22.5.1 gives a pragma_value more than one spelling, and a keyword whose
// value is a name is not thereby barred from being written with an identifier
// against it. What the subclause asks for is who wrote the design, so a region
// that answered in that spelling has answered.
TEST(ProtectAuthorDescription, AnIdentifierAgainstTheKeywordNamesTheAuthor) {
  std::string written =
      Encrypted(RegionWriting("`pragma protect author=ada_lovelace\n"));
  EXPECT_FALSE(Holds(written, kSealedDesign));
  EXPECT_TRUE(Holds(written, "`pragma protect author=ada_lovelace\n"));
}

// The third spelling §22.5.1 admits, read the same way. A number written
// against the keyword is one written thing standing for the author, so it names
// them as far as this rule is concerned and the envelope carries it.
TEST(ProtectAuthorDescription, ANumberAgainstTheKeywordNamesTheAuthor) {
  std::string written =
      Encrypted(RegionWriting("`pragma protect author=1843\n"));
  EXPECT_FALSE(Holds(written, kSealedDesign));
  EXPECT_TRUE(Holds(written, "`pragma protect author=1843\n"));
}

// The value form where two quantities part company: a string with nothing
// between its quotation marks was written, and what it holds is nothing at all.
// A reading that asked whether the region said anything, rather than whether it
// wrote the expression, would take this for a region that named nobody -- and
// every other value here would let that reading pass. What the region specified
// is a design whose author is written as nobody, which is a thing it specified,
// so the envelope states it.
TEST(ProtectAuthorDescription, AnEmptyStringAgainstTheKeywordIsPlaced) {
  std::string written = Encrypted(RegionWriting(NamesAuthor("")));
  EXPECT_FALSE(Holds(written, kSealedDesign));
  EXPECT_TRUE(Holds(written, NamesAuthor("")));
}

// The negative of the same rule, and the closest input it has to turn away: the
// other pragma_value spelling §22.5.1 admits, a parenthesized list of further
// expressions written where the string belongs. A list is not one written
// thing, so it specifies no name -- what it holds are subkeywords of somebody's
// own devising -- and a reading that took it would publish that list in the
// clear as whoever wrote the design.
TEST(ProtectAuthorDescription, AParenthesizedListSpecifiesNoName) {
  std::string listed =
      "`pragma protect author=(first=\"Ada\", last=\"Lovelace\")\n";
  std::string written = Encrypted(RegionWriting(listed));
  EXPECT_TRUE(Holds(written, kBeginProtected));
  EXPECT_FALSE(Holds(written, kAnyNaming));
  EXPECT_TRUE(Holds(OpenedBlockWriting(listed), listed));
}

// What the keyword being tabulated apart from the one carrying uninterpreted
// documentation is worth. The whole of this expression is written inside a
// documentation string here, so a tool that went looking for an author by
// reading such a string would find this one -- a name to publish, and the
// keyword spelled out beside it. The author is recognized by the keyword the
// directive named instead, and this directive named the other one, so what a
// documentation string holds settles nothing either way.
TEST(ProtectAuthorDescription, ANameInsideADocumentationStringIsNotRecognized) {
  std::string documented =
      "`pragma protect comment=\"author=\\\"Ada Lovelace\\\"\"\n";
  std::string written = Encrypted(RegionWriting(documented));
  EXPECT_TRUE(Holds(written, kBeginProtected));
  EXPECT_FALSE(Holds(written, kAnyNaming));
  EXPECT_TRUE(Holds(OpenedBlockWriting(documented), documented));
}

// The two keywords side by side on one directive, which is the position that
// tells them apart: §22.5.1 lets one directive carry a list of expressions, and
// the name the envelope states is the one written against this keyword rather
// than the documentation written beside it.
TEST(ProtectAuthorDescription, TheNameBesideADocumentationStringIsTheName) {
  std::string written = Encrypted(RegionWriting(
      "`pragma protect comment=\"Grace Hopper\", author=\"Ada Lovelace\"\n"));
  EXPECT_TRUE(Holds(written, NamesAuthor(kAuthorName)));
  EXPECT_FALSE(Holds(written, kOtherAuthorName));
}

// ---------------------------------------------------------------------------
// ENCRYPTION OUTPUT: the expression is placed in a directive the protected
// envelope encloses.
// ---------------------------------------------------------------------------

// Enclosed within the envelope, read as the position it is: the directive
// stands between the two expressions delimiting the envelope, so a reader that
// reached the envelope reached the name inside it. It is written once, the
// expression the region wrote having been placed here rather than written out
// beside a copy of itself.
TEST(ProtectAuthorDescription, ThePlacedDirectiveStandsInsideTheEnvelope) {
  std::string written = Encrypted(RegionWriting(NamesAuthor(kAuthorName)));
  EXPECT_EQ(Occurrences(written, NamesAuthor(kAuthorName)), 1U);
  EXPECT_LT(written.find(kBeginProtected),
            written.find(NamesAuthor(kAuthorName)));
  EXPECT_LT(written.find(NamesAuthor(kAuthorName)),
            written.find(kEndProtected));
}

// The negative: a region whose text names no author has no expression to place,
// so the envelope taking its place carries no such directive. What is placed is
// the expression the region held rather than the keyword as a matter of course.
TEST(ProtectAuthorDescription, ARegionNamingNobodyPlacesNoDirective) {
  std::string enclosed = NamesTheKey();
  enclosed.append(kSealedDesign);
  std::string written = Encrypted(Region(enclosed));
  EXPECT_TRUE(Holds(written, kBeginProtected));
  EXPECT_FALSE(Holds(written, kAnyNaming));
}

// The expression the envelope holds is the one its own region wrote. A model
// §34.5.3.1's and §34.5.4.1's words delimit travels into the enclosing block as
// the bytes it is written with, so the name it states is a name some earlier
// encryption placed for a design of its own: this envelope states the name its
// region wrote, once, and says nothing about the other.
TEST(ProtectAuthorDescription, AnEnclosedSealedModelsNameIsNotPlacedAgain) {
  std::string enclosed = NamesTheKey();
  enclosed.append(NamesAuthor(kAuthorName));
  enclosed.append(SealedModelNaming(kOtherAuthorName));
  enclosed.append(kSealedDesign);
  std::string written = Encrypted(Region(enclosed));
  EXPECT_EQ(Occurrences(written, NamesAuthor(kAuthorName)), 1U);
  EXPECT_FALSE(Holds(written, kOtherAuthorName));
}

// Where that name went instead, which no absence from the produced text can
// show: the sealed model is inside the new block whole, its own delimiters and
// the naming directive an earlier run placed inside it included. It was carried
// across rather than dropped, and this rule reached none of it.
TEST(ProtectAuthorDescription, AnEnclosedSealedModelsNameTravelsIntoTheBlock) {
  std::string enclosed = NamesTheKey();
  enclosed.append(NamesAuthor(kAuthorName));
  enclosed.append(SealedModelNaming(kOtherAuthorName));
  enclosed.append(kSealedDesign);
  std::string opened = OpenedBlockOf(Encrypted(Region(enclosed)));
  EXPECT_TRUE(Holds(opened, kBeginProtected));
  EXPECT_TRUE(Holds(opened, NamesAuthor(kOtherAuthorName)));
}

// Each envelope carries what its own region held. The second region here names
// nobody, so the envelope standing in its place states nobody -- the name the
// first region wrote describes the first envelope, and an envelope separated
// from the one before it says exactly what it said where it stood.
TEST(ProtectAuthorDescription, AnEnvelopePlacesOnlyItsOwnRegionsName) {
  std::string second = NamesTheKey();
  second.append("module other_m; endmodule\n");
  std::string written =
      Encrypted(RegionWriting(NamesAuthor(kAuthorName)) + Region(second));
  EXPECT_EQ(Occurrences(written, kBeginProtected), 2U);
  EXPECT_EQ(Occurrences(written, kAnyNaming), 1U);
  size_t first_envelope = written.find(kBeginProtected);
  size_t second_envelope = written.find(kBeginProtected, first_envelope + 1);
  EXPECT_LT(written.find(kAnyNaming), second_envelope);
}

// ---------------------------------------------------------------------------
// ENCRYPTION OUTPUT: the expression is not encrypted into the data block.
// ---------------------------------------------------------------------------

// The rule observed where it is decided: the block is opened with the key the
// region was sealed under and read. The design the region held is in there, and
// the expression naming its author is not -- which is what leaves the name
// readable to somebody holding no key.
TEST(ProtectAuthorDescription, TheOpenedBlockHoldsNoNamingDirective) {
  std::string opened = OpenedBlockWriting(NamesAuthor(kAuthorName));
  EXPECT_TRUE(Holds(opened, kSealedDesign));
  EXPECT_FALSE(Holds(opened, kAnyNaming));
}

// The same of a name written in the other spelling a pragma_value admits. What
// is kept out of the block is the expression, however the value against the
// keyword was spelled, so the two readings of a line -- the one that holds it
// back and the one that takes the name -- admit the same spellings.
TEST(ProtectAuthorDescription, AnAuthorNamedByAnIdentifierIsKeptOut) {
  std::string opened =
      OpenedBlockWriting("`pragma protect author=ada_lovelace\n");
  EXPECT_TRUE(Holds(opened, kSealedDesign));
  EXPECT_FALSE(Holds(opened, kAnyNaming));
}

// The value form that keeps the two halves of this rule honest. A string with
// nothing between its quotation marks is the expression, so the line carrying
// it is held back from the block like any other -- and a reading that decided
// what to withhold by looking at the value rather than at the expression would
// seal this line with the design while the envelope went on naming nobody in
// the clear.
TEST(ProtectAuthorDescription, AnEmptyStringNamingIsKeptOutOfTheBlock) {
  std::string opened = OpenedBlockWriting(NamesAuthor(""));
  EXPECT_TRUE(Holds(opened, kSealedDesign));
  EXPECT_FALSE(Holds(opened, kAnyNaming));
}

// The complement of what opening the block shows: the block a region naming its
// author is written into is the block written from that same region with the
// naming struck out. The cipher is a function of the text and the key, so two
// blocks written alike were written from the same text -- which says the naming
// line was the whole of what this rule withheld, rather than one of several
// lines that quietly failed to reach the block.
TEST(ProtectAuthorDescription, TheBlockIsTheOneTheUnnamedRegionProduces) {
  std::string named = Encrypted(RegionWriting(NamesAuthor(kAuthorName)));
  std::string unnamed = Encrypted(RegionWriting(""));
  EXPECT_FALSE(DataBlockOf(unnamed).empty());
  EXPECT_EQ(DataBlockOf(named), DataBlockOf(unnamed));
}

// The negative, and the pairing that says the spelling rather than the keyword
// did the work: the keyword standing alone writes no name, so it is not the
// expression this rule keeps out of the block. §34.5.1's rule for the rest of
// the enclosed text governs instead, and the line is sealed with the design.
TEST(ProtectAuthorDescription, TheKeywordStandingAloneIsLeftInTheBlock) {
  std::string bare = "`pragma protect author\n";
  EXPECT_FALSE(Holds(Encrypted(RegionWriting(bare)), kAnyNaming));
  EXPECT_TRUE(Holds(OpenedBlockWriting(bare), bare));
}

// ---------------------------------------------------------------------------
// ENCRYPTION OUTPUT: otherwise, the expression is copied without change.
// ---------------------------------------------------------------------------

// A text no encryption envelope encloses holds the expression where it was
// written, character for character. Without change is meant of the characters,
// so the spacing positioning the parts of the directive and the comment written
// after them come back as they went in: there is no envelope for the expression
// to be placed inside, and nothing here rewrites it.
TEST(ProtectAuthorDescription, AnExpressionOutsideEveryEnvelopeIsCopied) {
  std::string src = "module m;\n";
  src.append("`pragma  protect   author  =  \"Ada Lovelace\" // who\n");
  src.append("endmodule\n");
  EXPECT_EQ(Encrypted(src), src);
}

// The position that tells the two halves of the rule apart. The expression
// stands between two regions, so it is inside neither: it is copied where it
// was written rather than lifted into the envelope on either side of it, and
// neither envelope states a name.
TEST(ProtectAuthorDescription, AnExpressionBetweenTwoRegionsIsCopiedInPlace) {
  std::string enclosed = NamesTheKey();
  enclosed.append(kSealedDesign);
  std::string src = Region(enclosed);
  src.append(NamesAuthor(kAuthorName));
  src.append(Region(enclosed));
  std::string written = Encrypted(src);
  EXPECT_EQ(Occurrences(written, kAnyNaming), 1U);
  EXPECT_LT(written.find(kEndProtected), written.find(kAnyNaming));
  size_t first_envelope = written.find(kBeginProtected);
  size_t second_envelope = written.find(kBeginProtected, first_envelope + 1);
  EXPECT_LT(written.find(kAnyNaming), second_envelope);
}

// The same for an expression inside a model an earlier encryption sealed, where
// that model stands outside every encryption envelope. The words §34.5.3.1 and
// §34.5.4.1 define delimit a model rather than a region to be encrypted, so
// there is nothing here for a tool to transform and the whole text -- the
// naming directive an earlier run placed among its description included -- goes
// out exactly as it came in.
TEST(ProtectAuthorDescription, AnExpressionInAPassingSealedModelIsCopied) {
  std::string src = "module m;\n";
  src.append(SealedModelNaming(kAuthorName));
  src.append("endmodule\n");
  EXPECT_EQ(Encrypted(src), src);
}

// A region no key of the tool's reaches is not transformed at all, so the
// expression written inside it is text of the source like everything else there
// and goes back where it stands. There is no envelope for it to be placed in
// and no block for it to be kept out of, so what is left is the copying.
TEST(ProtectAuthorDescription, ARegionReachingNoKeyKeepsItsNamingAsWritten) {
  std::string src = RegionWriting(NamesAuthor(kAuthorName));
  EXPECT_EQ(EncryptedWithoutTheirKey(src), src);
}

// ---------------------------------------------------------------------------
// DECRYPTION INPUT: none.
// ---------------------------------------------------------------------------

// The round trip. A region naming its author comes back as the design it was
// written from, and the name reaches none of the text the compilation step
// after the preprocessor reads: the expression describes the envelope rather
// than the design, so nothing of it is design text.
TEST(ProtectAuthorDescription, TheNameReachesNoneOfTheRecoveredDesign) {
  ReadSource read(Encrypted(RegionWriting(NamesAuthor(kAuthorName))));
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_TRUE(read.Holds("module sealed_m"));
  EXPECT_FALSE(read.Holds(kAuthorName));
}

// Drawing nothing from the expression, read as a comparison rather than as an
// absence: two envelopes whose regions differ in nothing but the name they
// wrote are read to the same text. The name changed and the reading did not, so
// there is no part of what the reading produces that the name reached.
TEST(ProtectAuthorDescription, TwoEnvelopesDifferingOnlyInTheNameReadAlike) {
  std::string named = Encrypted(RegionWriting(NamesAuthor(kAuthorName)));
  std::string other = Encrypted(RegionWriting(NamesAuthor(kOtherAuthorName)));
  ASSERT_NE(named, other);
  ReadSource read(named);
  ReadSource read_other(other);
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_FALSE(read_other.diag.HasErrors());
  EXPECT_EQ(read.text, read_other.text);
}

// Where the directive stands among an envelope's description is not something a
// reader gets to settle, another producer having written its expressions in
// whatever order it chose. This is a real produced envelope with the naming
// moved to stand past the block, and the reading takes as much from it there as
// it took from it before: nothing, and the design still comes back.
TEST(ProtectAuthorDescription, ANamingPastTheBlockCostsTheReadingNothing) {
  std::string moved = WithTheNamingMovedPastTheBlock(
      Encrypted(RegionWriting(NamesAuthor(kAuthorName))));
  ASSERT_LT(moved.find("`pragma protect data_block=\""),
            moved.find(NamesAuthor(kAuthorName)));
  ReadSource read(moved);
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_TRUE(read.Holds("module sealed_m"));
  EXPECT_FALSE(read.Holds(kAuthorName));
}

// An envelope written by hand in §34.5.3.1's and §34.5.4.1's words, carrying
// this expression and nothing else. There is nothing here to draw on and
// nothing missed by not drawing on it: the envelope is opened and closed, the
// name reaches none of the design text, and the source standing on either side
// of the envelope arrives at the step after the preprocessor as it was written.
TEST(ProtectAuthorDescription, AnEnvelopeStatingOnlyANameIsReadAndClosed) {
  std::string envelope(kBeginProtected);
  envelope.append(NamesAuthor(kAuthorName)).append(kEndProtected);
  ReadSource read("module m;\n" + envelope + "endmodule\n");
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_EQ(read.ClosedEnvelopes(), 1U);
  EXPECT_EQ(read.OpenEnvelopes(), 0U);
  EXPECT_FALSE(read.Holds(kAuthorName));
  EXPECT_TRUE(read.Holds("endmodule"));
}

// The closest input this heading has to turn away. §34.5.12's expression is one
// a reading really does draw on -- it is how the key that opens the block is
// picked out -- and here the very characters it carried are written against
// this keyword instead. Drawing nothing from the expression, the reading is
// left with no key for the block, and the design stays sealed.
//
// The envelope the characters were moved in is the one read above, where the
// key stands under §34.5.12's own keyword and the design comes back. That
// reading is this one's control: the two differ in which keyword the characters
// were written against and in nothing else, so it is the keyword that kept the
// design sealed here rather than anything about the envelope.
TEST(ProtectAuthorDescription, ANameSpellingAKeyNameOpensNothing) {
  std::string replaced = WithTheKeyNameWrittenAsTheNaming(
      Encrypted(RegionWriting(NamesAuthor(kAuthorName))));
  ASSERT_TRUE(Holds(replaced, NamesAuthor(kKeyName)));
  ReadSource read(replaced);
  EXPECT_TRUE(read.diag.HasErrors());
  EXPECT_FALSE(read.Holds("module sealed_m"));
}

}  // namespace
