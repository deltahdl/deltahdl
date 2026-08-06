// §34.5.7.2 Description, for the protect pragma keyword that names the tool
// which performed an encryption. The syntax block above it settles how the
// expression is spelled; this one settles what a tool does with one, under each
// of the three headings the subclause writes its rules under.
//
// ENCRYPTION INPUT: none. An encrypting tool draws nothing at all from the
// expression. Whatever a source text wrote against the keyword was written
// before this tool ever saw the text, so it names some tool the text passed
// through earlier and settles nothing about the encryption now being performed.
// A line carrying it is text of the region like any other.
//
// ENCRYPTION OUTPUT. Three rules. The value the expression carries is a string
// naming the tool that performed the encryption; the tool that performed it
// generates the expression itself, rather than finding one to carry over; and
// the expression it generated is placed in a pragma directive the protected
// envelope encloses and kept out of the data_block.
//
// DECRYPTION INPUT: none. A tool reading a protected envelope draws nothing
// from the expression -- neither design text nor any part of what opens the
// block -- so an envelope naming the tool that sealed it is read exactly as far
// as an envelope naming none.
//
// All of it is preprocessor-stage. src/preprocessor/protect_envelope_output.h
// holds the name this implementation identifies itself by, and
// src/preprocessor/protect_envelope_output.cpp places the directive carrying it
// inside each envelope it writes, ahead of the block and outside the text the
// block is written from. src/preprocessor/protect_keywords.cpp spells that
// directive out of the description an envelope carries.
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
// hardest in: an expression written inside one names the tool that sealed
// somebody else's design, so it is neither lifted onto the new envelope nor
// held back from the bytes travelling into its block. The models below are
// written by running the encrypting half over a region of its own rather than
// spelled by hand, so the words delimiting them and the naming directive inside
// them are a tool's. §34.5.1.1 and §34.5.2.1 delimit the regions being
// encrypted, §34.5.10's data_keyowner and §34.5.12's data_keyname are the names
// a region reaches its key through, and §34.5.15's data_block is where the text
// a region sealed is carried. Every text below is written as directive syntax
// and driven through the encrypting half, the preprocessor, or both in turn,
// rather than handed to the envelope state by hand.

#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_protect_region.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_envelope.h"
#include "preprocessor/protect_envelope_output.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

// The name a source text writes against the keyword, standing for whatever tool
// the text passed through before this one reached it. It holds a space, so
// finding it anywhere is finding the value of an expression rather than a stray
// word of a line.
constexpr std::string_view kInputAgent = "AcmeCrypt 3.1";

// A second such name, for the model an earlier encryption sealed already and
// for the readings that write one envelope's naming against another's.
constexpr std::string_view kOtherAgent = "Globex Sealer 7";

// The opening of any directive writing this keyword with a value against it.
//
// It carries the equals sign because the keyword §34.5.8 defines is spelled
// with the characters this one opens with: a search for the shorter name alone
// would answer yes to a directive carrying only the longer.
constexpr std::string_view kAnyNaming = "`pragma protect encrypt_agent=";

// The expression this subclause is about, carrying `name` as the string it
// specifies.
//
// It serves both sides. A source text names the tool it passed through by
// writing this, and an encrypting tool generating the expression for an
// envelope of its own writes the same thing, so what a tool produced is
// compared against the spelling an input was built from.
std::string NamesTheAgent(std::string_view name) {
  std::string written = "`pragma protect encrypt_agent=\"";
  written.append(name).append("\"\n");
  return written;
}

// The expression an encrypting tool generates for an envelope it wrote: the
// keyword with this implementation's own name written against it as a string.
// There is no other tool the value could be naming, this being the tool that
// performed the encryption.
std::string TheGeneratedNaming() { return NamesTheAgent(kEncryptAgent); }

// A model an earlier encryption sealed already, naming `name` as the tool that
// sealed it.
//
// Nothing of it is spelled by hand: it is what the encrypting half writes from
// a region of its own, so the words §34.5.3.1 and §34.5.4.1 define delimit it
// because a tool put them there. The naming inside it is then written over with
// the name asked for, that directive standing in the clear where a tool placed
// it, so the model names a tool other than the one that sealed the region it is
// about to be enclosed by.
std::string SealedModelNaming(std::string_view name) {
  std::string model = Encrypted(RegionWriting(""));
  std::string naming = TheGeneratedNaming();
  size_t stands = model.find(naming);
  if (stands == std::string::npos) return model;
  model.replace(stands, naming.size(), NamesTheAgent(name));
  return model;
}

// `envelope` with the tool it names replaced by `name`.
//
// An envelope cannot be spelled by hand for the readings that compare two of
// them -- what its block holds depends on the key the region was sealed under
// -- so an envelope naming another tool is made by writing over the naming
// inside a real produced one. The directive stands in the clear outside the
// block, so nothing the block records changes with it. A text the directive was
// not found in comes back as it stands, and the expectations of the test that
// asked for the change then fail on the envelope that was never altered.
std::string WithTheAgentRenamed(const std::string& envelope,
                                std::string_view name) {
  std::string naming = TheGeneratedNaming();
  size_t stands = envelope.find(naming);
  if (stands == std::string::npos) return envelope;
  std::string renamed(envelope);
  renamed.replace(stands, naming.size(), NamesTheAgent(name));
  return renamed;
}

// `envelope` with the directive naming the tool taken out of its description
// and written again just past the block, on the line before the word that
// closes it.
std::string WithTheNamingMovedPastTheBlock(const std::string& envelope) {
  std::string naming = TheGeneratedNaming();
  size_t stands = envelope.find(naming);
  if (stands == std::string::npos) return envelope;
  std::string moved(envelope);
  moved.erase(stands, naming.size());
  size_t closes = moved.find(kEndProtected);
  if (closes == std::string::npos) return envelope;
  moved.insert(closes, naming);
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
std::string WithTheKeyNameWrittenAsTheNaming(const std::string& envelope) {
  std::string designation = DesignatesTheKey();
  size_t stands = envelope.find(designation);
  if (stands == std::string::npos) return envelope;
  std::string replaced(envelope);
  replaced.replace(stands, designation.size(), NamesTheAgent(kKeyName));
  return replaced;
}

// ---------------------------------------------------------------------------
// ENCRYPTION INPUT: none.
// ---------------------------------------------------------------------------

// The rule at its plainest, and the one position where drawing on the input
// would be invisible in the count: a region names a tool, the envelope taking
// its place names one, and the two names are different. What describes the
// envelope is the tool that performed this encryption rather than the tool the
// text passed through before it arrived.
TEST(ProtectEncryptAgentDescription, TheNameARegionWroteDescribesNoEnvelope) {
  std::string written = Encrypted(RegionWriting(NamesTheAgent(kInputAgent)));
  EXPECT_FALSE(Holds(written, kSealedDesign));
  EXPECT_TRUE(Holds(written, TheGeneratedNaming()));
  EXPECT_FALSE(Holds(written, kInputAgent));
}

// Where the region's own expression went instead, read as an equality rather
// than as a search: the text a block records is the region's own text character
// for character, the naming line included and standing in the place the region
// wrote it.
//
// The equality is what makes this one reading rather than two. A search of the
// opened block would say the line is in there and leave open whether something
// else was quietly dropped on the way; and it would say nothing about what the
// block does not hold, which is the other half of this envelope's story. Both
// halves are here: the block is written from the region's text, all of it and
// nothing besides.
TEST(ProtectEncryptAgentDescription, TheBlockRecordsTheRegionsTextEntire) {
  std::string body = RegionBody(NamesTheAgent(kInputAgent));
  EXPECT_EQ(OpenedBlockOf(Encrypted(RegionAround(body))), body);
}

// §22.5.1 gives a pragma_value more than one spelling, and none of them is a
// spelling this rule reads a name out of, there being no reading of the value
// at all. An identifier written against the keyword is text of the region like
// the quoted spelling is, and the envelope names this tool either way.
//
// The identifier stands here for every spelling that is one written thing
// carrying no quotation marks. The line this rule draws is drawn before the
// value is looked at -- nothing is read out of any spelling -- so a run of
// digits written here is the same input as a run of letters, and a case for
// each would be one case twice. Which spellings §22.5.1 tells apart from one
// another is that subclause's question.
TEST(ProtectEncryptAgentDescription, AnIdentifierAgainstTheKeywordIsSealed) {
  std::string named = "`pragma protect encrypt_agent=acme_crypt\n";
  std::string written = Encrypted(RegionWriting(named));
  EXPECT_TRUE(Holds(written, TheGeneratedNaming()));
  EXPECT_TRUE(Holds(OpenedBlockWriting(named), named));
}

// The spelling §22.5.1 admits that §34.5.7.1 does not define this keyword with:
// a parenthesized list of further expressions written where the string belongs.
// It is the closest input the encryption-input rule has to turn away, and it is
// turned away by the same silence every other spelling meets -- the list is
// sealed with the design, and the envelope goes on naming this tool.
TEST(ProtectEncryptAgentDescription, AParenthesizedListAgainstItIsSealed) {
  std::string listed =
      "`pragma protect encrypt_agent=(name=\"Acme\", version=\"3.1\")\n";
  std::string written = Encrypted(RegionWriting(listed));
  EXPECT_EQ(TimesWritten(written, kAnyNaming), 1U);
  EXPECT_TRUE(Holds(written, TheGeneratedNaming()));
  EXPECT_TRUE(Holds(OpenedBlockWriting(listed), listed));
}

// The value form where two quantities part company: a string with nothing
// between its quotation marks names no tool, and it is passed over exactly as a
// string naming one is. A reading that decided what to do by looking at the
// value would part company with the rule here, the rule being about the
// expression rather than about what it carries.
TEST(ProtectEncryptAgentDescription, AnEmptyStringAgainstTheKeywordIsSealed) {
  std::string named = NamesTheAgent("");
  std::string written = Encrypted(RegionWriting(named));
  EXPECT_TRUE(Holds(written, TheGeneratedNaming()));
  EXPECT_TRUE(Holds(OpenedBlockWriting(named), named));
}

// The keyword standing alone, which is the other pragma expression spelling
// §22.5.1 offers. It names no tool and it is not the expression §34.5.7.1
// defines, and nothing about it changes what the envelope states either: the
// line is sealed with the design like any other.
TEST(ProtectEncryptAgentDescription, TheKeywordStandingAloneIsSealedToo) {
  std::string bare = "`pragma protect encrypt_agent\n";
  std::string written = Encrypted(RegionWriting(bare));
  EXPECT_EQ(TimesWritten(written, kAnyNaming), 1U);
  EXPECT_TRUE(Holds(OpenedBlockWriting(bare), bare));
}

// §22.5.1 lets one directive carry a list of expressions, and the position that
// tells this rule from a rule about lines is a region designating its key on
// the very directive that names a tool. The region was sealed, so the list was
// read through to its end; and the tool it named still describes nothing.
TEST(ProtectEncryptAgentDescription, ANameBesideAKeyDesignationIsPassedOver) {
  std::string listed = DesignatesTheProvider();
  listed.append("`pragma protect encrypt_agent=\"AcmeCrypt 3.1\", ");
  listed.append("data_keyname=\"").append(kKeyName).append("\"\n");
  listed.append(kSealedDesign);
  std::string written = Encrypted(RegionAround(listed));
  EXPECT_FALSE(Holds(written, kSealedDesign));
  EXPECT_TRUE(Holds(written, TheGeneratedNaming()));
  EXPECT_FALSE(Holds(written, kInputAgent));
}

// §34.4 makes the scope of a protect pragma keyword lexical, so a name written
// ahead of a region is in effect where the region opens. That is still not a
// place anything is drawn from: the expression stays outside the envelope on
// the line it was written on, written once, and the envelope names this tool.
TEST(ProtectEncryptAgentDescription, ANameInEffectAheadOfARegionIsNotDrawnOn) {
  std::string src = NamesTheAgent(kInputAgent);
  src.append(RegionWriting(""));
  std::string written = Encrypted(src);
  EXPECT_EQ(TimesWritten(written, NamesTheAgent(kInputAgent)), 1U);
  EXPECT_LT(written.find(NamesTheAgent(kInputAgent)),
            written.find(kBeginProtected));
  EXPECT_TRUE(Holds(written, TheGeneratedNaming()));
}

// The position where the drawing of nothing is the whole of what happens: a
// name written where no region encloses it. There is no region for the
// encrypting half to transform, so nothing is taken from the expression and
// there is no envelope for it to describe. The spacing that positions the
// parts of the directive and the comment written after them come back as they
// went in, which is what tells a line that was passed over from one that was
// read and written out again.
TEST(ProtectEncryptAgentDescription, ANameOutsideEveryRegionStaysAsWritten) {
  std::string spaced = "`pragma  protect   encrypt_agent  =  ";
  spaced.append("\"AcmeCrypt 3.1\" // whoever sealed it\n");
  std::string src = "module m;\n";
  src.append(spaced).append("endmodule\n");
  EXPECT_EQ(Encrypted(src), src);
}

// A model an earlier encryption sealed already, enclosed by a region this one
// seals. §34.5.3 leaves the expressions of such a model uninterpreted and
// §34.5.1 has it travel into the larger block as the bytes it is written with,
// so the tool it names sealed somebody else's design. This envelope names the
// tool that sealed it, once, and says nothing of the other.
TEST(ProtectEncryptAgentDescription, AnEnclosedSealedModelsNameIsNotDrawnOn) {
  std::string written =
      Encrypted(RegionWriting(SealedModelNaming(kOtherAgent)));
  EXPECT_EQ(TimesWritten(written, kAnyNaming), 1U);
  EXPECT_TRUE(Holds(written, TheGeneratedNaming()));
  EXPECT_FALSE(Holds(written, kOtherAgent));
}

// Where that name went instead, which no absence from the produced text can
// show: the sealed model is inside the new block whole, its own delimiters and
// the naming directive standing among them included. It was carried across
// rather than dropped, and this rule reached none of it.
TEST(ProtectEncryptAgentDescription, AnEnclosedSealedModelsNameIsCarriedIn) {
  std::string opened = OpenedBlockWriting(SealedModelNaming(kOtherAgent));
  EXPECT_TRUE(Holds(opened, kBeginProtected));
  EXPECT_TRUE(Holds(opened, NamesTheAgent(kOtherAgent)));
}

// ---------------------------------------------------------------------------
// ENCRYPTION OUTPUT: the value is a string naming the encrypting tool.
// ---------------------------------------------------------------------------

// The value read as what it has to be: a string, written against the keyword,
// with a name in it. An envelope carrying the keyword alone would name no tool,
// and one carrying an empty string would leave a reader unable to say which
// tool sealed what it is holding.
TEST(ProtectEncryptAgentDescription, TheGeneratedValueIsAStringNamingATool) {
  std::string written = Encrypted(RegionWriting(""));
  EXPECT_FALSE(kEncryptAgent.empty());
  EXPECT_TRUE(Holds(written, TheGeneratedNaming()));
  EXPECT_FALSE(Holds(written, "`pragma protect encrypt_agent\n"));
}

// ---------------------------------------------------------------------------
// ENCRYPTION OUTPUT: the encrypting tool generates the expression.
// ---------------------------------------------------------------------------

// Generated rather than carried over, at its plainest: a region that says
// nothing at all about an encrypting tool is described by one anyway. There was
// nothing in the text to copy, so the expression the envelope carries was made
// for it.
TEST(ProtectEncryptAgentDescription, ARegionNamingNoToolStillGetsANaming) {
  std::string written = Encrypted(RegionWriting(""));
  EXPECT_FALSE(Holds(written, kSealedDesign));
  EXPECT_EQ(TimesWritten(written, TheGeneratedNaming()), 1U);
}

// Generated for each envelope rather than once for the text. Two regions are
// sealed here and neither leans on what stands in the envelope before it: an
// envelope separated from its neighbour still says which tool sealed it, which
// is what makes the envelopes self-contained §34.4 asks them to be.
TEST(ProtectEncryptAgentDescription, EachEnvelopeIsGivenANamingOfItsOwn) {
  std::string second = ReachesTheKey();
  second.append("module other_m; endmodule\n");
  std::string written = Encrypted(RegionWriting("") + RegionAround(second));
  EXPECT_EQ(TimesWritten(written, kBeginProtected), 2U);
  EXPECT_EQ(TimesWritten(written, TheGeneratedNaming()), 2U);
  EXPECT_EQ(TimesWritten(written, kAnyNaming), 2U);
}

// The negative of generating one: a region there is no key to seal is not
// transformed into an envelope at all, so there is no protected envelope for an
// expression to be enclosed by and none is generated. The key held here belongs
// to the entity the region designates, under a name the region designates
// nothing by, which is what leaves the region standing.
TEST(ProtectEncryptAgentDescription, ARegionReachingNoKeyIsGivenNoNaming) {
  std::string src = RegionWriting(NamesTheAgent(kInputAgent));
  EXPECT_EQ(EncryptedWithoutTheKey(src), src);
}

// ---------------------------------------------------------------------------
// ENCRYPTION OUTPUT: the expression is placed in a directive the protected
// envelope encloses.
// ---------------------------------------------------------------------------

// Enclosed within the envelope, read as the position it is: the directive
// stands between the two expressions delimiting the protected envelope, so a
// reader that reached the envelope reached the name of the tool that made it.
TEST(ProtectEncryptAgentDescription, TheNamingStandsInsideTheEnvelope) {
  std::string written = Encrypted(RegionWriting(""));
  EXPECT_LT(written.find(kBeginProtected), written.find(TheGeneratedNaming()));
  EXPECT_LT(written.find(TheGeneratedNaming()), written.find(kEndProtected));
}

// The half of that position which the enclosing alone does not fix: the
// directive stands ahead of the block rather than after it, so nothing a reader
// has to hold a key for comes between the envelope and the name of the tool
// that wrote it. That readability is what placing the expression in a directive
// is for.
TEST(ProtectEncryptAgentDescription, TheNamingStandsAheadOfTheBlock) {
  std::string written = Encrypted(RegionWriting(""));
  EXPECT_TRUE(Holds(written, kBlockOpening));
  EXPECT_LT(written.find(TheGeneratedNaming()), written.find(kBlockOpening));
}

// One directive for one envelope. A region that already named a tool does not
// get its own naming placed beside the generated one: what the envelope holds
// is the expression the tool generated, and the region's own line went into the
// block with the design.
TEST(ProtectEncryptAgentDescription, TheEnvelopeCarriesTheOneNamingPlaced) {
  std::string written = Encrypted(RegionWriting(NamesTheAgent(kInputAgent)));
  EXPECT_EQ(TimesWritten(written, kAnyNaming), 1U);
  EXPECT_EQ(TimesWritten(written, TheGeneratedNaming()), 1U);
}

// ---------------------------------------------------------------------------
// ENCRYPTION OUTPUT: the expression is not encrypted into the data block.
// ---------------------------------------------------------------------------

// Opening the block and reading it is one way to see what went into it. §34.5.9
// gives a second way that does not involve opening anything: an encrypting tool
// states how much data a block stands for, so what the envelope itself says
// about the size of the text it sealed is a reading of the same fact by another
// route. The count here is of the region's own text, the generated naming
// having joined the envelope rather than the text being sealed -- so a tool
// that swept the line into the block would have to misstate the size to keep
// this quiet.
TEST(ProtectEncryptAgentDescription, TheStatedBlockSizeLeavesTheNamingOut) {
  std::string body = RegionBody("");
  std::string counted = "bytes=";
  counted.append(std::to_string(ProtectedRegionBlockSize(body))).append(")");
  EXPECT_TRUE(Holds(Encrypted(RegionAround(body)), counted));
}

// The pairing that says the rule is about the expression the tool generated
// rather than about the keyword: a naming the region wrote is in the block, and
// the naming the tool generated is not, in one and the same envelope. A reading
// that kept every line carrying this keyword out of the block would publish the
// region's own line in the clear; one that kept none out would seal the
// generated line the envelope is supposed to state.
TEST(ProtectEncryptAgentDescription, OnlyTheGeneratedNamingIsWithheld) {
  std::string written = Encrypted(RegionWriting(NamesTheAgent(kInputAgent)));
  std::string opened = OpenedBlockOf(written);
  EXPECT_TRUE(Holds(opened, NamesTheAgent(kInputAgent)));
  EXPECT_FALSE(Holds(opened, kEncryptAgent));
  EXPECT_TRUE(Holds(written, TheGeneratedNaming()));
}

// ---------------------------------------------------------------------------
// DECRYPTION INPUT: none.
// ---------------------------------------------------------------------------

// The round trip. A region comes back as the design it was written from, and
// the name of the tool that sealed it reaches none of the text the compilation
// step after the preprocessor reads: the expression describes the envelope
// rather than the design, so nothing of it is design text.
TEST(ProtectEncryptAgentDescription, TheNamingReachesNoneOfTheRecoveredDesign) {
  ReadWithTheKeys read(Encrypted(RegionWriting("")));
  EXPECT_FALSE(read.diags.HasErrors());
  EXPECT_TRUE(read.Produced("module sealed_m"));
  EXPECT_FALSE(read.Produced(kEncryptAgent));
}

// Drawing nothing from the expression, read as a comparison rather than as an
// absence: two envelopes differing in nothing but the tool they name are read
// to the same text. The name changed and the reading did not, so there is no
// part of what the reading produces that the name reached.
TEST(ProtectEncryptAgentDescription, TwoEnvelopesDifferingOnlyInTheNameRead) {
  std::string mine = Encrypted(RegionWriting(""));
  std::string theirs = WithTheAgentRenamed(mine, kOtherAgent);
  ASSERT_NE(mine, theirs);
  ReadWithTheKeys read(mine);
  ReadWithTheKeys read_theirs(theirs);
  EXPECT_FALSE(read.diags.HasErrors());
  EXPECT_FALSE(read_theirs.diags.HasErrors());
  EXPECT_EQ(read.produced, read_theirs.produced);
}

// Where the directive stands among an envelope's description is not something a
// reader gets to settle, another producer having written its expressions in
// whatever order it chose. This is a real produced envelope with the naming
// moved to stand past the block, and the reading takes as much from it there as
// it took from it before: nothing, and the design still comes back.
TEST(ProtectEncryptAgentDescription, ANamingPastTheBlockCostsTheReadingNone) {
  std::string moved =
      WithTheNamingMovedPastTheBlock(Encrypted(RegionWriting("")));
  ASSERT_LT(moved.find(kBlockOpening), moved.find(TheGeneratedNaming()));
  ReadWithTheKeys read(moved);
  EXPECT_FALSE(read.diags.HasErrors());
  EXPECT_TRUE(read.Produced("module sealed_m"));
  EXPECT_FALSE(read.Produced(kEncryptAgent));
}

// An envelope written by hand in §34.5.3.1's and §34.5.4.1's words, naming some
// other tool and carrying nothing else. There is nothing here to draw on and
// nothing missed by not drawing on it: the envelope is opened and closed, the
// name reaches none of the design text, and the source standing on either side
// of the envelope arrives at the step after the preprocessor as it was written.
TEST(ProtectEncryptAgentDescription, AForeignEnvelopeNamingOnlyAToolIsClosed) {
  std::string envelope(kBeginProtected);
  envelope.append(NamesTheAgent(kOtherAgent)).append(kEndProtected);
  ReadWithTheKeys read("module m;\n" + envelope + "endmodule\n");
  EXPECT_FALSE(read.diags.HasErrors());
  EXPECT_EQ(read.Closed(), 1U);
  EXPECT_EQ(read.StillOpen(), 0U);
  EXPECT_FALSE(read.Produced(kOtherAgent));
  EXPECT_TRUE(read.Produced("endmodule"));
}

// The whole round trip built from the words §34.5.3.1 and §34.5.4.1 define,
// with none of it spelled by hand: a model an earlier encryption sealed is
// enclosed by a region, that region is sealed in its turn by the encrypting
// half, and the envelope it produced is read back through the preprocessor.
// The design comes out at the far end, and neither name reaches it -- not the
// one the enclosed model carried among its own description, which came back out
// of this envelope's block and was read there as description, nor the one this
// tool generated for the envelope itself.
TEST(ProtectEncryptAgentDescription, AnEnclosedModelsNameReachesNoDesignText) {
  std::string written =
      Encrypted(RegionWriting(SealedModelNaming(kOtherAgent)));
  ReadWithTheKeys read(written);
  EXPECT_FALSE(read.diags.HasErrors());
  EXPECT_TRUE(read.Produced("module sealed_m"));
  EXPECT_FALSE(read.Produced(kOtherAgent));
  EXPECT_FALSE(read.Produced(kEncryptAgent));
}

// The spelling a conforming producer would not have written, met on the side
// that has to read whatever it is given. §34.5.7.1 defines the expression with
// a string against the keyword, so the keyword standing alone names no tool at
// all -- and there being nothing to draw on either way, the reading treats it
// as it treats the defined spelling: the envelope opens and closes on schedule,
// the directive is consumed, and no part of it turns up in the design text.
TEST(ProtectEncryptAgentDescription, AForeignEnvelopeWithTheBareKeywordIsRead) {
  std::string envelope(kBeginProtected);
  envelope.append("`pragma protect encrypt_agent\n").append(kEndProtected);
  ReadWithTheKeys read("module m;\n" + envelope + "endmodule\n");
  EXPECT_FALSE(read.diags.HasErrors());
  EXPECT_EQ(read.Closed(), 1U);
  EXPECT_EQ(read.StillOpen(), 0U);
  EXPECT_FALSE(read.Produced("encrypt_agent"));
  EXPECT_TRUE(read.Produced("endmodule"));
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
TEST(ProtectEncryptAgentDescription, ANamingSpellingAKeyNameOpensNothing) {
  std::string replaced =
      WithTheKeyNameWrittenAsTheNaming(Encrypted(RegionWriting("")));
  ASSERT_TRUE(Holds(replaced, NamesTheAgent(kKeyName)));
  ReadWithTheKeys read(replaced);
  EXPECT_TRUE(read.diags.HasErrors());
  EXPECT_FALSE(read.Produced("module sealed_m"));
}

}  // namespace
