// §34.5.8.2 Description, for the protect pragma keyword that carries whatever
// further the tool which performed an encryption offered about itself. The
// syntax block above it settles how the expression is spelled; this one settles
// what a tool does with one, under each of the three headings the subclause
// writes its rules under.
//
// ENCRYPTION INPUT: none. An encrypting tool draws nothing at all from the
// expression. Whatever a source text wrote against the keyword was written
// before this tool ever saw the text, so it was offered by some tool the text
// passed through earlier and about that tool, and it settles nothing about the
// encryption now being performed. A line carrying it is text of the region like
// any other.
//
// ENCRYPTION OUTPUT. Three rules. The value the expression carries is a string
// holding information the encrypting tool provides beyond the name that
// identifies it; where such a value was provided, the expression is placed in a
// pragma directive the protected envelope encloses; and it is kept out of the
// data_block. The placement is stated on that condition rather than
// unconditionally, so a tool with nothing further to offer writes no expression
// at all -- which is the one branch of this subclause no source text can ask
// for, the condition being about what the tool provides rather than about what
// it reads.
//
// DECRYPTION INPUT: none. A tool reading a protected envelope draws nothing
// from the expression -- neither design text nor any part of what opens the
// block -- so an envelope whose sealer said more about itself is read as far
// as an envelope whose sealer said nothing.
//
// All of it is preprocessor-stage. src/preprocessor/protect_envelope_output.h
// holds the further word this implementation offers about itself, and
// src/preprocessor/protect_envelope_output.cpp places the directive carrying it
// inside each envelope it writes, ahead of the block and outside the text the
// block is written from. src/preprocessor/protect_keywords.cpp spells that
// directive out of the description an envelope carries, and it is that file
// which writes one only where a value was provided.
// src/preprocessor/protect_processing.cpp is the half that reads an encrypting
// tool's input, and it holds no line back from the block on account of this
// keyword: that absence is the encryption-input rule. The decrypting half is
// src/preprocessor/preprocessor.cpp with
// src/preprocessor/preprocessor_protect_keys.cpp, which consume the directive
// like any other protect pragma and take nothing out of it.
//
// The inputs are the real syntax of the dependencies this rule consumes.
// §34.5.3.1's word opens a model an earlier encryption sealed already and
// §34.5.4.1's word closes it, and such a model is the position this rule is
// hardest in: an expression written inside one was offered by the tool that
// sealed somebody else's design, so it is neither lifted onto the new envelope
// nor held back from the bytes travelling into its block. The models below are
// written by running the encrypting half over a region of its own rather than
// spelled by hand, so the words delimiting them and the offering inside them
// are a tool's. §34.5.1.1 and §34.5.2.1 delimit the regions being encrypted,
// §34.5.10's data_keyowner and §34.5.12's data_keyname are the names a region
// reaches its key through, and §34.5.15's data_block is where the text a
// region sealed is carried. Every text below is written as directive syntax
// and driven through the encrypting half, the preprocessor, or both in turn,
// rather than handed to the envelope state by hand.

#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_envelope.h"
#include "preprocessor/protect_envelope_output.h"
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

// The word a source text offers further about the tool that sealed it, standing
// for whatever that tool said of itself before this one reached the text. It
// holds spaces, so finding it anywhere is finding the value of an expression
// rather than a stray word of a line.
constexpr std::string_view kInputOffering = "assembled in Springfield";

// A second such word, for the model an earlier encryption sealed already and
// for the readings that write one envelope's offering against another's.
constexpr std::string_view kOtherOffering = "sealed on the night shift";

// The opening of any directive writing this keyword with a value against it.
constexpr std::string_view kAnyOffering = "`pragma protect encrypt_agent_info=";

// The design a region seals. Nothing of it survives the alphabet an encrypted
// block is written in, so finding it outside a block is finding a region that
// was never sealed, and finding it in what a reading produced is finding a
// block that opened.
constexpr std::string_view kSealedDesign = "module sealed_m; endmodule\n";

// Where the expression recording one envelope's sealed region begins. What
// stands between the quotation marks after it is the block itself.
constexpr std::string_view kBlockOpening = "`pragma protect data_block=\"";

// The two words §34.5.3.1 and §34.5.4.1 define, which delimit a model an
// encryption sealed already -- as the encrypting half writes them, and as a
// text carrying somebody else's sealed model writes them.
constexpr std::string_view kBeginProtected =
    "`pragma protect begin_protected\n";
constexpr std::string_view kEndProtected = "`pragma protect end_protected\n";

// The one key every region below reaches, held under the names that select it.
ProtectKeyList TheRegionsKey() {
  ProtectKeyList held;
  held.Add(
      {std::string(kKeyOwner), std::string(kKeyName), std::string(kRegionKey)});
  return held;
}

// A key of the same entity held under some other name, for the region that
// reaches no key at all. A tool holding this has keys, and none of them is the
// one the region asked for, so a region left untransformed was left so for want
// of its own key rather than for want of any.
ProtectKeyList AKeyUnderAnotherName() {
  ProtectKeyList held;
  held.Add(
      {std::string(kKeyOwner), "some-other-key-name", std::string(kRegionKey)});
  return held;
}

// Whether `where` writes `what` anywhere in it.
bool Holds(std::string_view where, std::string_view what) {
  return where.find(what) != std::string_view::npos;
}

// How many times `where` writes `what`, counting the writings that do not
// overlap.
size_t TimesWritten(std::string_view where, std::string_view what) {
  size_t written = 0;
  for (size_t at = where.find(what); at != std::string_view::npos;
       at = where.find(what, at + what.size())) {
    ++written;
  }
  return written;
}

// The expression naming the entity that provided the key, as §34.5.10 writes
// it, and the expression picking that provider's key out by name, as §34.5.12
// writes it. The second is a line a reading really does draw on, which is what
// makes it the thing to write this subclause's expression in the place of.
std::string DesignatesTheProvider() {
  std::string written = "`pragma protect data_keyowner=\"";
  written.append(kKeyOwner).append("\"\n");
  return written;
}

std::string DesignatesTheKey() {
  std::string written = "`pragma protect data_keyname=\"";
  written.append(kKeyName).append("\"\n");
  return written;
}

// Both designations together, which is what a region has to write to reach a
// key at all.
std::string ReachesTheKey() {
  return DesignatesTheProvider() + DesignatesTheKey();
}

// The expression this subclause is about, carrying `word` as the string it
// specifies.
//
// It serves both sides. A source text offers a further word about the tool it
// passed through by writing this, and an encrypting tool providing one for an
// envelope of its own writes the same thing, so what a tool produced is
// compared against the spelling an input was built from.
std::string OffersFurther(std::string_view word) {
  std::string written(kAnyOffering);
  written.append("\"").append(word).append("\"\n");
  return written;
}

// The expression an encrypting tool provides for an envelope it wrote: the
// keyword with this implementation's own further word about itself written
// against it as a string. There is no other tool the value could be about, this
// being the tool that performed the encryption.
std::string TheGeneratedOffering() { return OffersFurther(kEncryptAgentInfo); }

// One encryption envelope: §34.5.1.1's and §34.5.2.1's words with `inside`
// between them.
std::string RegionAround(std::string_view inside) {
  std::string written = "`pragma protect begin\n";
  written.append(inside).append("`pragma protect end\n");
  return written;
}

// The text one such region encloses: the designations reaching its key, then
// `written`, then the design it seals.
//
// The designations come first so that every region here is one there is
// something to encrypt in, and the design comes last so that a `written` the
// reading passed over is a `written` that went into the block ahead of it.
std::string RegionBody(std::string_view written) {
  std::string inside = ReachesTheKey();
  inside.append(written).append(kSealedDesign);
  return inside;
}

// That body between the two words delimiting a region to be encrypted.
std::string RegionWriting(std::string_view written) {
  return RegionAround(RegionBody(written));
}

// The text standing where the encryption envelopes of `source` were written,
// for a tool holding the key those regions name.
std::string Encrypted(std::string_view source) {
  return EncryptEnvelopes(source, "", TheRegionsKey());
}

// The same, for a tool holding a key of that entity under another name.
std::string EncryptedWithoutTheKey(std::string_view source) {
  return EncryptEnvelopes(source, "", AKeyUnderAnotherName());
}

// The characters recording one envelope's sealed region: what stands between
// the quotation marks of its data_block expression, and empty where the text
// carries no such expression.
std::string DataBlockOf(std::string_view envelope) {
  size_t opens = envelope.find(kBlockOpening);
  if (opens == std::string_view::npos) return {};
  size_t from = opens + kBlockOpening.size();
  size_t to = envelope.find('"', from);
  if (to == std::string_view::npos) return {};
  return std::string(envelope.substr(from, to - from));
}

// The text that block records, recovered under the key the region was sealed
// with, and empty where the block does not open.
//
// A rule about what a block shall not hold is settled by opening the block and
// looking. The characters a block is written as say nothing about what went
// into it, so a reading that only searched the produced text could not tell a
// line that was kept out of the block from one that is in there unreadably.
std::string OpenedBlockOf(std::string_view envelope) {
  std::string recovered;
  if (!DecryptProtectedRegion(DataBlockOf(envelope), kRegionKey, &recovered)) {
    return {};
  }
  return recovered;
}

// The same, over a region writing `written` inside itself.
std::string OpenedBlockWriting(std::string_view written) {
  return OpenedBlockOf(Encrypted(RegionWriting(written)));
}

// A model an earlier encryption sealed already, whose sealer offered `word`
// about itself.
//
// Nothing of it is spelled by hand: it is what the encrypting half writes from
// a region of its own, so the words §34.5.3.1 and §34.5.4.1 define delimit it
// because a tool put them there. The offering inside it is then written over
// with the word asked for, that directive standing in the clear where a tool
// placed it, so the model carries a further word about a tool other than the
// one that sealed the region it is about to be enclosed by.
std::string SealedModelOffering(std::string_view word) {
  std::string model = Encrypted(RegionWriting(""));
  std::string offering = TheGeneratedOffering();
  size_t stands = model.find(offering);
  if (stands == std::string::npos) return model;
  model.replace(stands, offering.size(), OffersFurther(word));
  return model;
}

// A source text read through the preprocessor by a tool holding the region
// keys, with the text the reading produced and what the reading left behind.
//
// Which envelopes the reading opened and closed is state the preprocessor
// carries from one directive to the next rather than anything the output text
// shows, so the Preprocessor outlives the call.
struct ReadWithTheKeys {
  static PreprocConfig ConfigHoldingTheKeys() {
    PreprocConfig config;
    config.protect_keys = TheRegionsKey();
    return config;
  }

  SourceManager sources;
  DiagEngine diags{sources};
  Preprocessor reader;
  std::string produced;

  explicit ReadWithTheKeys(const std::string& src)
      : reader(sources, diags, ConfigHoldingTheKeys()) {
    produced = reader.Preprocess(sources.AddFile("<test>", src));
  }

  // How many protected envelopes the reading is still inside where the text
  // ends, and how many it opened and then closed.
  size_t StillOpen() const {
    return reader.ProtectEnvelopes().DecryptionEnvelopeDepth();
  }
  size_t Closed() const {
    return reader.ProtectEnvelopes().ClosedEnvelopes().size();
  }

  bool Produced(std::string_view what) const {
    return produced.find(what) != std::string::npos;
  }
};

// `envelope` with the further word it offers replaced by `word`.
//
// An envelope cannot be spelled by hand for the readings that compare two of
// them -- what its block holds depends on the key the region was sealed under
// -- so an envelope offering another word is made by writing over the offering
// inside a real produced one. The directive stands in the clear outside the
// block, so nothing the block records changes with it. A text the directive was
// not found in comes back as it stands, and the expectations of the test that
// asked for the change then fail on the envelope that was never altered.
std::string WithTheOfferingReworded(const std::string& envelope,
                                    std::string_view word) {
  std::string offering = TheGeneratedOffering();
  size_t stands = envelope.find(offering);
  if (stands == std::string::npos) return envelope;
  std::string reworded(envelope);
  reworded.replace(stands, offering.size(), OffersFurther(word));
  return reworded;
}

// `envelope` with the directive offering the further word taken out of its
// description and written again just past the block, on the line before the
// word that closes it.
std::string WithTheOfferingMovedPastTheBlock(const std::string& envelope) {
  std::string offering = TheGeneratedOffering();
  size_t stands = envelope.find(offering);
  if (stands == std::string::npos) return envelope;
  std::string moved(envelope);
  moved.erase(stands, offering.size());
  size_t closes = moved.find(kEndProtected);
  if (closes == std::string::npos) return envelope;
  moved.insert(closes, offering);
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
std::string WithTheKeyNameWrittenAsTheOffering(const std::string& envelope) {
  std::string designation = DesignatesTheKey();
  size_t stands = envelope.find(designation);
  if (stands == std::string::npos) return envelope;
  std::string replaced(envelope);
  replaced.replace(stands, designation.size(), OffersFurther(kKeyName));
  return replaced;
}

// One directive carrying two expressions: this subclause's, and §34.5.12's
// designation of the key a block is under. The offering is written first, so a
// reading arrives at the designation having stepped over this expression on the
// way to it.
std::string OfferingAheadOfTheKeyName() {
  std::string listed = "`pragma protect encrypt_agent_info=\"";
  listed.append(kOtherOffering).append("\", data_keyname=\"");
  listed.append(kKeyName).append("\"\n");
  return listed;
}

// The same two expressions in the other order, which leaves the reading in a
// different state where this one begins: the key has been designated already,
// so what this expression must leave alone is a designation in hand rather than
// one still to come.
std::string OfferingAfterTheKeyName() {
  std::string listed = "`pragma protect data_keyname=\"";
  listed.append(kKeyName).append("\", encrypt_agent_info=\"");
  listed.append(kOtherOffering).append("\"\n");
  return listed;
}

// `envelope` with the directive designating the key its block is under
// rewritten as `listed`.
//
// An envelope cannot be spelled by hand for these readings -- what its block
// holds depends on the key the region was sealed under -- so a producer that
// wrote two expressions on one directive is made by rewriting one directive of
// a real produced envelope. Everything else about it, the block included, is
// left exactly as the encrypting half wrote it. A text the directive was not
// found in comes back as it stands, and the expectations of the test that asked
// for the change then fail on the envelope that was never altered.
std::string WithTheKeyNameListedAs(const std::string& envelope,
                                   const std::string& listed) {
  std::string designation = DesignatesTheKey();
  size_t stands = envelope.find(designation);
  if (stands == std::string::npos) return envelope;
  std::string replaced(envelope);
  replaced.replace(stands, designation.size(), listed);
  return replaced;
}

// ---------------------------------------------------------------------------
// ENCRYPTION INPUT: none.
// ---------------------------------------------------------------------------

// The rule at its plainest, and the one position where drawing on the input
// would be invisible in the count: a region offers a further word about a tool,
// the envelope taking its place offers one, and the two words are different.
// What describes the envelope was provided by the tool that performed this
// encryption rather than by the tool the text passed through before it arrived.
TEST(ProtectEncryptAgentInfoDescription, TheWordARegionWroteDescribesNothing) {
  std::string written = Encrypted(RegionWriting(OffersFurther(kInputOffering)));
  EXPECT_FALSE(Holds(written, kSealedDesign));
  EXPECT_TRUE(Holds(written, TheGeneratedOffering()));
  EXPECT_FALSE(Holds(written, kInputOffering));
}

// Where the region's own expression went instead, read as an equality rather
// than as a search: the text a block records is the region's own text
// character for character, the offering line included and standing in the
// place the region wrote it.
//
// The equality is what makes this one reading rather than two. A search of the
// opened block would say the line is in there and leave open whether something
// else was quietly dropped on the way; and it would say nothing about what the
// block does not hold, which is the other half of this envelope's story. Both
// halves are here: the block is written from the region's text, all of it and
// nothing besides.
TEST(ProtectEncryptAgentInfoDescription, TheBlockRecordsTheRegionsTextEntire) {
  std::string body = RegionBody(OffersFurther(kInputOffering));
  EXPECT_EQ(OpenedBlockOf(Encrypted(RegionAround(body))), body);
}

// §22.5.1 gives a pragma_value more than one spelling, and none of them is a
// spelling this rule reads a word out of, there being no reading of the value
// at all. An identifier written against the keyword is text of the region like
// the quoted spelling is, and the envelope offers this tool's word either way.
//
// The identifier stands here for every spelling that is one written thing
// carrying no quotation marks, and the case above it stands for every spelling
// that is one written thing carrying them. The line this rule draws is drawn
// before the value is looked at -- nothing is read out of any spelling -- so a
// run of digits written here is the same input as a run of letters, and the
// spelling that closes a string on three quotation marks is the same input as
// the one that closes it on a single mark. A case for each would be one case
// several times over: none of them can come out differently while this rule is
// the one being observed, because the rule reaches no value to tell them apart
// by. Which spellings §22.5.1 tells apart from one another is that subclause's
// question, and where they are told apart is §34.5.8.1, whose rule does turn on
// which one was written.
TEST(ProtectEncryptAgentInfoDescription, AnIdentifierAgainstItIsSealed) {
  std::string offered = "`pragma protect encrypt_agent_info=springfield\n";
  std::string written = Encrypted(RegionWriting(offered));
  EXPECT_TRUE(Holds(written, TheGeneratedOffering()));
  EXPECT_TRUE(Holds(OpenedBlockWriting(offered), offered));
}

// The spelling §22.5.1 admits that §34.5.8.1 does not define this keyword with:
// a parenthesized list of further expressions written where the string belongs.
// It is the closest input the encryption-input rule has to turn away, and it is
// turned away by the same silence every other spelling meets -- the list is
// sealed with the design, and the envelope goes on offering this tool's word.
TEST(ProtectEncryptAgentInfoDescription, AParenthesizedListAgainstItIsSealed) {
  std::string listed(kAnyOffering);
  listed.append("(site=\"Springfield\", shift=\"2\")\n");
  std::string written = Encrypted(RegionWriting(listed));
  EXPECT_EQ(TimesWritten(written, kAnyOffering), 1U);
  EXPECT_TRUE(Holds(written, TheGeneratedOffering()));
  EXPECT_TRUE(Holds(OpenedBlockWriting(listed), listed));
}

// The value form where two quantities part company: a string with nothing
// between its quotation marks offers no further word, and it is passed over
// exactly as a string offering one is. A reading that decided what to do by
// looking at the value would part company with the rule here, the rule being
// about the expression rather than about what it carries.
TEST(ProtectEncryptAgentInfoDescription, AnEmptyStringAgainstItIsSealed) {
  std::string offered = OffersFurther("");
  std::string written = Encrypted(RegionWriting(offered));
  EXPECT_TRUE(Holds(written, TheGeneratedOffering()));
  EXPECT_TRUE(Holds(OpenedBlockWriting(offered), offered));
}

// The keyword standing alone, which is the other pragma expression spelling
// §22.5.1 offers. It carries no further word and it is not the expression
// §34.5.8.1 defines, and nothing about it changes what the envelope states
// either: the line is sealed with the design like any other.
TEST(ProtectEncryptAgentInfoDescription, TheKeywordStandingAloneIsSealedToo) {
  std::string bare = "`pragma protect encrypt_agent_info\n";
  std::string written = Encrypted(RegionWriting(bare));
  EXPECT_EQ(TimesWritten(written, kAnyOffering), 1U);
  EXPECT_TRUE(Holds(OpenedBlockWriting(bare), bare));
}

// §22.5.1 lets one directive carry a list of expressions, and the position
// that tells this rule from a rule about lines is a region designating its key
// on the very directive that offers a further word. The region was sealed, so
// the list was read to its end; and the word it offered still describes
// nothing.
TEST(ProtectEncryptAgentInfoDescription, AWordBesideADesignationIsPassedOver) {
  std::string listed = DesignatesTheProvider();
  listed.append("`pragma protect encrypt_agent_info=\"assembled in ");
  listed.append("Springfield\", ");
  listed.append("data_keyname=\"").append(kKeyName).append("\"\n");
  listed.append(kSealedDesign);
  std::string written = Encrypted(RegionAround(listed));
  EXPECT_FALSE(Holds(written, kSealedDesign));
  EXPECT_TRUE(Holds(written, TheGeneratedOffering()));
  EXPECT_FALSE(Holds(written, kInputOffering));
}

// §34.4 makes the scope of a protect pragma keyword lexical, so a word written
// ahead of a region is in effect where the region opens. That is still not a
// place anything is drawn from: the expression stays outside the envelope on
// the line it was written on, written once, and the envelope offers this
// tool's own word.
TEST(ProtectEncryptAgentInfoDescription, AWordInEffectAheadIsNotDrawnOn) {
  std::string src = OffersFurther(kInputOffering);
  src.append(RegionWriting(""));
  std::string written = Encrypted(src);
  EXPECT_EQ(TimesWritten(written, OffersFurther(kInputOffering)), 1U);
  EXPECT_LT(written.find(OffersFurther(kInputOffering)),
            written.find(kBeginProtected));
  EXPECT_TRUE(Holds(written, TheGeneratedOffering()));
}

// The position where the drawing of nothing is the whole of what happens: a
// word written where no region encloses it. There is no region for the
// encrypting half to transform, so nothing is taken from the expression and
// there is no envelope for it to describe. The spacing that positions the
// parts of the directive and the comment written after them come back as they
// went in, which is what tells a line that was passed over from one that was
// read and written out again.
TEST(ProtectEncryptAgentInfoDescription, AWordOutsideEveryRegionIsUntouched) {
  std::string spaced = "`pragma  protect   encrypt_agent_info  =  ";
  spaced.append("\"assembled in Springfield\" // whoever sealed it\n");
  std::string src = "module m;\n";
  src.append(spaced).append("endmodule\n");
  EXPECT_EQ(Encrypted(src), src);
}

// A model an earlier encryption sealed already, enclosed by a region this one
// seals. §34.5.3 leaves the expressions of such a model uninterpreted and
// §34.5.1 has it travel into the larger block as the bytes it is written with,
// so the word it offers was offered by the tool that sealed somebody else's
// design. This envelope offers the word of the tool that sealed it, once, and
// says nothing of the other.
TEST(ProtectEncryptAgentInfoDescription, AnEnclosedModelsWordIsNotDrawnOn) {
  std::string written =
      Encrypted(RegionWriting(SealedModelOffering(kOtherOffering)));
  EXPECT_EQ(TimesWritten(written, kAnyOffering), 1U);
  EXPECT_TRUE(Holds(written, TheGeneratedOffering()));
  EXPECT_FALSE(Holds(written, kOtherOffering));
}

// Where that word went instead, which no absence from the produced text can
// show: the sealed model is inside the new block whole, its own delimiters and
// the offering directive standing among them included. It was carried across
// rather than dropped, and this rule reached none of it.
TEST(ProtectEncryptAgentInfoDescription, AnEnclosedModelsWordIsCarriedIn) {
  std::string opened = OpenedBlockWriting(SealedModelOffering(kOtherOffering));
  EXPECT_TRUE(Holds(opened, kBeginProtected));
  EXPECT_TRUE(Holds(opened, OffersFurther(kOtherOffering)));
}

// ---------------------------------------------------------------------------
// ENCRYPTION OUTPUT: the value is a string holding information the tool
// provides beyond the name identifying it.
// ---------------------------------------------------------------------------

// The value read as what it has to be: a string, written against the keyword,
// with something in it. An envelope carrying the keyword alone would offer
// nothing, and one carrying an empty string would state that its sealer had
// something further to say and then not say it.
//
// It is also read as additional to the name. The identifying name is what
// §34.5.7 already puts in the envelope, so a value repeating it would be the
// same information written twice rather than the further information this
// keyword exists to carry.
TEST(ProtectEncryptAgentInfoDescription, TheProvidedValueIsAStringSayingMore) {
  std::string written = Encrypted(RegionWriting(""));
  EXPECT_FALSE(kEncryptAgentInfo.empty());
  EXPECT_NE(kEncryptAgentInfo, kEncryptAgent);
  EXPECT_TRUE(Holds(written, TheGeneratedOffering()));
  EXPECT_FALSE(Holds(written, "`pragma protect encrypt_agent_info\n"));
}

// ---------------------------------------------------------------------------
// ENCRYPTION OUTPUT: if provided, the expression is placed in a directive the
// protected envelope encloses.
// ---------------------------------------------------------------------------

// Provided by the tool rather than carried over, at its plainest: a region that
// says nothing at all about an encrypting tool is described by a further word
// anyway. There was nothing in the text to copy, so the expression the envelope
// carries was made for it.
TEST(ProtectEncryptAgentInfoDescription, ARegionOfferingNothingStillGetsOne) {
  std::string written = Encrypted(RegionWriting(""));
  EXPECT_FALSE(Holds(written, kSealedDesign));
  EXPECT_EQ(TimesWritten(written, TheGeneratedOffering()), 1U);
}

// Provided for each envelope rather than once for the text. Two regions are
// sealed here and neither leans on what stands in the envelope before it: an
// envelope separated from its neighbour still carries what its sealer offered,
// which is what makes the envelopes self-contained §34.4 asks them to be.
TEST(ProtectEncryptAgentInfoDescription, EachEnvelopeIsGivenOneOfItsOwn) {
  std::string second = ReachesTheKey();
  second.append("module other_m; endmodule\n");
  std::string written = Encrypted(RegionWriting("") + RegionAround(second));
  EXPECT_EQ(TimesWritten(written, kBeginProtected), 2U);
  EXPECT_EQ(TimesWritten(written, TheGeneratedOffering()), 2U);
  EXPECT_EQ(TimesWritten(written, kAnyOffering), 2U);
}

// The negative of placing one: a region there is no key to seal is not
// transformed into an envelope at all, so there is no protected envelope for an
// expression to be enclosed by and none is placed. The key held here belongs to
// the entity the region designates, under a name the region designates nothing
// by, which is what leaves the region standing.
TEST(ProtectEncryptAgentInfoDescription, ARegionReachingNoKeyIsGivenNone) {
  std::string src = RegionWriting(OffersFurther(kInputOffering));
  EXPECT_EQ(EncryptedWithoutTheKey(src), src);
}

// The condition the placement is stated on, read in both directions. This is
// the one branch of the subclause no source text can ask for: what decides it
// is whether the tool provided a value, and a tool's own further word about
// itself is settled where the tool is written rather than by anything it
// reads. So the description an envelope is written from is handed to the
// writing half directly, once with a word provided and once without.
//
// A tool with nothing further to say writes no expression at all rather than
// one carrying an empty string, an empty offering being a claim to have said
// something. The remaining keywords of the description are written either way,
// so what changed between the two is this expression and nothing else.
TEST(ProtectEncryptAgentInfoDescription, NoOfferingIsWrittenWhereNoneIsGiven) {
  std::string with = ProtectEnvelopeDescriptionDirectives(
      {kEncryptAgent, kEncryptAgentInfo, kDataMethod, "(enctype=\"base64\")"});
  std::string without = ProtectEnvelopeDescriptionDirectives(
      {kEncryptAgent, "", kDataMethod, "(enctype=\"base64\")"});
  EXPECT_TRUE(Holds(with, TheGeneratedOffering()));
  EXPECT_FALSE(Holds(without, kAnyOffering));
  EXPECT_TRUE(Holds(without, kDataMethod));
}

// Enclosed within the envelope, read as the position it is: the directive
// stands between the two expressions delimiting the protected envelope, so a
// reader that reached the envelope reached what the tool that made it offered
// about itself.
TEST(ProtectEncryptAgentInfoDescription, TheOfferingStandsInsideTheEnvelope) {
  std::string written = Encrypted(RegionWriting(""));
  std::string offering = TheGeneratedOffering();
  EXPECT_LT(written.find(kBeginProtected), written.find(offering));
  EXPECT_LT(written.find(offering), written.find(kEndProtected));
}

// The half of that position which the enclosing alone does not fix: the
// directive stands ahead of the block rather than after it, so nothing a
// reader has to hold a key for comes between the envelope and what its maker
// said about itself. That readability is what placing the expression in a
// directive is for.
TEST(ProtectEncryptAgentInfoDescription, TheOfferingStandsAheadOfTheBlock) {
  std::string written = Encrypted(RegionWriting(""));
  EXPECT_TRUE(Holds(written, kBlockOpening));
  EXPECT_LT(written.find(TheGeneratedOffering()), written.find(kBlockOpening));
}

// One directive for one envelope. A region that already offered a further word
// does not get its own offering placed beside the provided one: what the
// envelope holds is the expression the tool provided, and the region's own line
// went into the block with the design.
TEST(ProtectEncryptAgentInfoDescription, TheEnvelopeCarriesTheOnePlaced) {
  std::string written = Encrypted(RegionWriting(OffersFurther(kInputOffering)));
  EXPECT_EQ(TimesWritten(written, kAnyOffering), 1U);
  EXPECT_EQ(TimesWritten(written, TheGeneratedOffering()), 1U);
}

// ---------------------------------------------------------------------------
// ENCRYPTION OUTPUT: the expression is not encrypted into the data block.
// ---------------------------------------------------------------------------

// Opening the block and reading it is one way to see what went into it. §34.5.9
// gives a second way that does not involve opening anything: an encrypting tool
// states how much data a block stands for, so what the envelope itself says
// about the size of the text it sealed is a reading of the same fact by another
// route. The count here is of the region's own text, the provided offering
// having joined the envelope rather than the text being sealed -- so a tool
// that swept the line into the block would have to misstate the size to keep
// this quiet.
TEST(ProtectEncryptAgentInfoDescription, TheStatedBlockSizeLeavesItOut) {
  std::string body = RegionBody("");
  std::string counted = "bytes=";
  counted.append(std::to_string(ProtectedRegionBlockSize(body))).append(")");
  EXPECT_TRUE(Holds(Encrypted(RegionAround(body)), counted));
}

// The pairing that says the rule is about the expression the tool provided
// rather than about the keyword: an offering the region wrote is in the block,
// and the offering the tool provided is not, in one and the same envelope. A
// reading that kept every line carrying this keyword out of the block would
// publish the region's own line in the clear; one that kept none out would seal
// the provided line the envelope is supposed to state.
TEST(ProtectEncryptAgentInfoDescription, OnlyTheProvidedOfferingIsWithheld) {
  std::string written = Encrypted(RegionWriting(OffersFurther(kInputOffering)));
  std::string opened = OpenedBlockOf(written);
  EXPECT_TRUE(Holds(opened, OffersFurther(kInputOffering)));
  EXPECT_FALSE(Holds(opened, kEncryptAgentInfo));
  EXPECT_TRUE(Holds(written, TheGeneratedOffering()));
}

// ---------------------------------------------------------------------------
// DECRYPTION INPUT: none.
// ---------------------------------------------------------------------------

// The round trip. A region comes back as the design it was written from, and
// what the tool that sealed it offered about itself reaches none of the text
// the compilation step after the preprocessor reads: the expression describes
// the envelope rather than the design, so nothing of it is design text.
TEST(ProtectEncryptAgentInfoDescription, ItReachesNoneOfTheRecoveredDesign) {
  ReadWithTheKeys read(Encrypted(RegionWriting("")));
  EXPECT_FALSE(read.diags.HasErrors());
  EXPECT_TRUE(read.Produced("module sealed_m"));
  EXPECT_FALSE(read.Produced(kEncryptAgentInfo));
}

// Drawing nothing from the expression, read as a comparison rather than as an
// absence: two envelopes differing in nothing but the word their sealers
// offered are read to the same text. The word changed and the reading did not,
// so there is no part of what the reading produces that the word reached.
TEST(ProtectEncryptAgentInfoDescription, TwoEnvelopesDifferingOnlyInItRead) {
  std::string mine = Encrypted(RegionWriting(""));
  std::string theirs = WithTheOfferingReworded(mine, kOtherOffering);
  ASSERT_NE(mine, theirs);
  ReadWithTheKeys read(mine);
  ReadWithTheKeys read_theirs(theirs);
  EXPECT_FALSE(read.diags.HasErrors());
  EXPECT_FALSE(read_theirs.diags.HasErrors());
  EXPECT_EQ(read.produced, read_theirs.produced);
}

// Where the directive stands among an envelope's description is not something a
// reader gets to settle, another producer having written its expressions in
// whatever order it chose. This is a real produced envelope with the offering
// moved to stand past the block, and the reading takes as much from it there as
// it took from it before: nothing, and the design still comes back.
TEST(ProtectEncryptAgentInfoDescription, AnOfferingPastTheBlockCostsNothing) {
  std::string moved =
      WithTheOfferingMovedPastTheBlock(Encrypted(RegionWriting("")));
  ASSERT_LT(moved.find(kBlockOpening), moved.find(TheGeneratedOffering()));
  ReadWithTheKeys read(moved);
  EXPECT_FALSE(read.diags.HasErrors());
  EXPECT_TRUE(read.Produced("module sealed_m"));
  EXPECT_FALSE(read.Produced(kEncryptAgentInfo));
}

// An envelope written by hand in §34.5.3.1's and §34.5.4.1's words, offering
// some other word and carrying nothing else. There is nothing here to draw on
// and nothing missed by not drawing on it: the envelope is opened and closed,
// the word reaches none of the design text, and the source standing on either
// side of the envelope arrives at the step after the preprocessor as it was
// written.
TEST(ProtectEncryptAgentInfoDescription, AForeignEnvelopeOfferingOnlyItCloses) {
  std::string envelope(kBeginProtected);
  envelope.append(OffersFurther(kOtherOffering)).append(kEndProtected);
  ReadWithTheKeys read("module m;\n" + envelope + "endmodule\n");
  EXPECT_FALSE(read.diags.HasErrors());
  EXPECT_EQ(read.Closed(), 1U);
  EXPECT_EQ(read.StillOpen(), 0U);
  EXPECT_FALSE(read.Produced(kOtherOffering));
  EXPECT_TRUE(read.Produced("endmodule"));
}

// The whole round trip built from the words §34.5.3.1 and §34.5.4.1 define,
// with none of it spelled by hand: a model an earlier encryption sealed is
// enclosed by a region, that region is sealed in its turn by the encrypting
// half, and the envelope it produced is read back through the preprocessor.
// The design comes out at the far end, and neither word reaches it -- not the
// one the enclosed model carried among its own description, which came back
// out of this envelope's block and was read there as description, nor the one
// this tool provided for the envelope itself.
TEST(ProtectEncryptAgentInfoDescription, AnEnclosedModelsWordReachesNoDesign) {
  std::string written =
      Encrypted(RegionWriting(SealedModelOffering(kOtherOffering)));
  ReadWithTheKeys read(written);
  EXPECT_FALSE(read.diags.HasErrors());
  EXPECT_TRUE(read.Produced("module sealed_m"));
  EXPECT_FALSE(read.Produced(kOtherOffering));
  EXPECT_FALSE(read.Produced(kEncryptAgentInfo));
}

// The spelling a conforming producer would not have written, met on the side
// that has to read whatever it is given. §34.5.8.1 defines the expression with
// a string against the keyword, so the keyword standing alone offers nothing
// at all -- and there being nothing to draw on either way, the reading treats
// it as it treats the defined spelling: the envelope opens and closes on
// schedule, the directive is consumed, and no part of it turns up in the
// design text.
TEST(ProtectEncryptAgentInfoDescription, AForeignEnvelopeWithTheBareKeyword) {
  std::string envelope(kBeginProtected);
  envelope.append("`pragma protect encrypt_agent_info\n").append(kEndProtected);
  ReadWithTheKeys read("module m;\n" + envelope + "endmodule\n");
  EXPECT_FALSE(read.diags.HasErrors());
  EXPECT_EQ(read.Closed(), 1U);
  EXPECT_EQ(read.StillOpen(), 0U);
  EXPECT_FALSE(read.Produced("encrypt_agent_info"));
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
TEST(ProtectEncryptAgentInfoDescription, AnOfferingSpellingAKeyNameOpensNone) {
  std::string replaced =
      WithTheKeyNameWrittenAsTheOffering(Encrypted(RegionWriting("")));
  ASSERT_TRUE(Holds(replaced, OffersFurther(kKeyName)));
  ReadWithTheKeys read(replaced);
  EXPECT_TRUE(read.diags.HasErrors());
  EXPECT_FALSE(read.Produced("module sealed_m"));
}

// The expression-list position, met on the side that reads. §22.5.1 lets one
// directive carry a list, and how another producer grouped its expressions is
// not something a reader gets to settle, so this expression may arrive with the
// one thing a reading really does draw on written after it on the same line.
//
// Drawing nothing from an expression has to leave the reading able to go on to
// the next one. The design comes back, so the designation was reached across
// this expression rather than lost behind it; and the word offered reaches none
// of the design text, so reaching past it was not reading it. A reading that
// ended the directive here would take the key with it and the block would stay
// shut, which is what the section above shows a reading with no key looks like.
TEST(ProtectEncryptAgentInfoDescription, AnOfferingAheadOfTheKeyNameCostsNone) {
  std::string listed = OfferingAheadOfTheKeyName();
  std::string rewritten =
      WithTheKeyNameListedAs(Encrypted(RegionWriting("")), listed);
  ASSERT_TRUE(Holds(rewritten, listed));
  ReadWithTheKeys read(rewritten);
  EXPECT_FALSE(read.diags.HasErrors());
  EXPECT_TRUE(read.Produced("module sealed_m"));
  EXPECT_FALSE(read.Produced(kOtherOffering));
}

// The same two expressions in the other order. The reading arrives at this one
// having taken the key already, which is a different state to carry forward
// than the order above leaves it in: what drawing nothing has to leave standing
// here is a designation in hand rather than one still to come.
//
// A reading that let this expression disturb what the directive had already put
// in effect would leave the block under a key that was designated and then
// undone, and the design would stay sealed with nothing on the line to say why.
TEST(ProtectEncryptAgentInfoDescription, AnOfferingAfterTheKeyNameCostsNone) {
  std::string listed = OfferingAfterTheKeyName();
  std::string rewritten =
      WithTheKeyNameListedAs(Encrypted(RegionWriting("")), listed);
  ASSERT_TRUE(Holds(rewritten, listed));
  ReadWithTheKeys read(rewritten);
  EXPECT_FALSE(read.diags.HasErrors());
  EXPECT_TRUE(read.Produced("module sealed_m"));
  EXPECT_FALSE(read.Produced(kOtherOffering));
}

}  // namespace
