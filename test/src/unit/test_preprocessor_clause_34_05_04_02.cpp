// §34.5.4.2 Description, for the protect pragma keyword that closes a region of
// text some earlier encryption sealed. The syntax block above it settles how
// the expression is spelled; this one settles what a tool does with one, and it
// settles it under each of the three headings the subclause writes its rules
// under.
//
// ENCRYPTION INPUT. The expression marks where a block some earlier
// begin_protected expression opened stops. Two things follow from that, and the
// subclause states both: the block is complete where the word stands, and the
// pragma expression values written after it are gathered again -- for the
// envelope that is to be written next. §34.5.3.2 settles what happens to the
// values written inside such a block; what this one settles is that the word is
// the point where gathering starts up again, so a value owes its place in an
// envelope's description to standing on the far side of it.
//
// ENCRYPTION OUTPUT. The word answering the opening expression of a sealed
// model goes into the data_block of the envelope being written, under the
// method and the keys that encryption is running with. The word is inside the
// block rather than around it, so an encrypting tool leaves none of it
// readable, and what gets it back is the key the envelope was written under.
//
// DECRYPTION INPUT. Read from the other side, the word marks the end of a run
// of pragma expressions -- and the subclause says that run is enough to open
// the block the envelope carries. Enough, so the run is complete where the word
// stands: nothing gathered inside it is still owed a line, and nothing it
// carried is what opens some later envelope's block instead.
//
// All of it is preprocessor-stage. src/preprocessor/protect_processing.cpp
// carries the encrypting half: it walks a source text through a counter of the
// sealed models it stands inside and starts reading values again where the word
// takes that counter back to nothing, handing the model's own lines to the
// block of the enclosing region. src/preprocessor/protect_envelope_output.cpp
// writes the envelope that block goes into.
// src/preprocessor/protect_envelope.cpp pairs the word with the opening
// expression it answers on the decrypting side, and
// src/preprocessor/preprocessor.cpp is where the run of gathered expressions is
// ended at the word, so that the directive spelling it is read as the
// expression it is rather than as a value some keyword above it was still
// waiting for.
//
// The inputs are the real syntax of the dependencies this rule consumes.
// §34.5.3.1's word opens each of the models this one ends, §34.5.15's
// data_block is the expression an envelope's own text is carried on, and
// §34.5.11's data_method is the identifier an envelope states for the cipher
// its block is under -- which is what "the current method" names. §34.5.10's
// data_keyowner and §34.5.12's data_keyname are the values whose gathering the
// word restarts, §34.5.13's and §34.5.14's keywords are the ones that speak for
// the line beneath them and so the ones the word can find still waiting,
// §34.5.9's encoding decides what a line beneath one of those says, and
// §34.5.1.1 and §34.5.2.1 delimit the larger model a sealed one is resealed
// inside of. Every text below is written as directive syntax and driven through
// the encrypting half, the preprocessor, or both in turn, rather than handed to
// the envelope state by hand.

#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_protect_read.h"
#include "helpers_protect_keys.h"
#include "helpers_text_lines.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_envelope.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

// A second such key, held by a reader the envelope was not written for. It is
// what says a block opened because the reading reached the right key rather
// than because any key at all would have done.
constexpr std::string_view kOtherReaderKey = "other-reader-key";

// The entity writing the larger model, and the name picking its key out of the
// list of keys that entity provided. §34.5.10 and §34.5.12 give the pair, and
// neither half reaches a key alone.
constexpr std::string_view kAuthorEntity = "Acme Corp";
constexpr std::string_view kAuthorKeyName = "design-2026";
constexpr std::string_view kAuthorKey = "acme-design-key";

// The same pair for whoever sealed the model being resealed. Their key is
// supplied to the tool alongside the one above, so a run that gathered their
// names as though they had been written after the word would reach a real key
// and produce a real envelope -- one nothing holding the current author's key
// could open.
constexpr std::string_view kSealerEntity = "Other Corp";
constexpr std::string_view kSealerKeyName = "other-2019";
constexpr std::string_view kSealerKey = "other-legacy-key";

// The statement the larger model encloses. It does not survive the writing of a
// block, so finding it in a tool's output is finding text that was not sealed,
// and finding it in what a reading produced is finding a block that opened.
constexpr std::string_view kOuterStatement = "initial result = 42;";

// The statement a model sealed by an earlier run of the encrypting half
// encloses, and the one the region resealing that model writes past its closing
// word. Neither survives the writing of a block either.
constexpr std::string_view kInnerStatement = "initial sealed = 7;";
constexpr std::string_view kAfterStatement = "initial after = 9;";

// A block written in the clear inside a model somebody sealed earlier. What it
// says is not a value any scheme writes, so finding it in an output is finding
// text that was carried across rather than sealed.
constexpr std::string_view kSealedBlockMarker = "SEALEDMODELBLOCKMARKER";

// The identifier this implementation states for the blocks it writes, which is
// the method the current encryption is running under. §34.5.11 defines the
// keyword; what it is doing here is standing for "the current method" the
// subclause has the word encrypted under, so a text stating it is a text an
// envelope was really written for.
constexpr std::string_view kCurrentMethod = "x-deltahdl-stream";

// The identifier a model somebody sealed earlier names for the cipher its own
// block is under, written as §34.5.11 spells it. It is not this
// implementation's, so an envelope stating it would be one that had read a
// sealed model's account of itself as its own.
constexpr std::string_view kSealerMethod = "x-legacy-cipher";

// The directive carrying the word, in the spelling §34.5.4.1 defines it with:
// the pragma_keyword standing alone.
constexpr std::string_view kWordDirective = "`pragma protect end_protected\n";

// The same word in the other spelling §22.5.1 allows a pragma expression, which
// §34.5.4.1 leaves closing nothing. It is the closest input the rules below
// have to turn away -- a reserved word written in a spelling the standard does
// not define it with -- so it stands where the word stands and completes no
// block.
constexpr std::string_view kValuedWordDirective =
    "`pragma protect end_protected=\"1\"\n";
// Both entities' keys, supplied to whichever half is running. Holding the
// sealed model's key too is what makes the tests below discriminating: a run
// that gathered the sealed model's names would find a key under them rather
// than falling back to the current author's for want of one.
ProtectKeyList BothEntitiesKeys() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kAuthorEntity, kAuthorKeyName, kAuthorKey));
  keys.Add(KeyOf(kSealerEntity, kSealerKeyName, kSealerKey));
  return keys;
}

// The same, under the keys the two entities provided, which is what a region
// naming an entity and one of its keys is encrypted with.
std::string EncryptedUnderNames(const std::string& src) {
  return EncryptEnvelopes(src, {}, BothEntitiesKeys());
}

// A model somebody sealed earlier, written by hand as the decryption envelope
// §34.5.3.1 opens and this subclause's word closes, with `closing` standing
// where that word belongs.
//
// It describes itself with the real syntax of the dependencies this rule
// consumes: §34.5.5's author, and §34.5.10's entity beside §34.5.12's key name.
// The names are a real entity's and a real key of theirs, so gathering them
// would reach a key rather than reach nothing, and a run that started gathering
// one expression too early is told apart from one that started where the word
// stands.
//
// It carries no block of its own. Every text below is read back through the
// preprocessor at some point, and a block standing outside every encryption the
// tests perform would be tried against the reader's key and reported for not
// opening -- which would say nothing about the word.
std::string SealedModel(std::string_view closing) {
  std::string text = "`pragma protect begin_protected\n";
  text.append("`pragma protect author=\"").append(kSealerEntity).append("\"\n");
  text.append("`pragma protect data_keyowner=\"").append(kSealerEntity);
  text.append("\"\n");
  text.append("`pragma protect data_keyname=\"").append(kSealerKeyName);
  text.append("\"\n");
  text.append(closing);
  return text;
}

// The two expressions naming the key the encryption now in process is to run
// under, written as §34.5.10 and §34.5.12 spell them.
std::string CurrentKeyNames() {
  std::string text = "`pragma protect data_keyowner=\"";
  text.append(kAuthorEntity).append("\"\n");
  text.append("`pragma protect data_keyname=\"").append(kAuthorKeyName);
  text.append("\"\n");
  return text;
}

// An encryption region enclosing a sealed model whose closing expression is
// `closing`, with the current encryption's own key names written past that
// expression.
//
// The position of those names is the whole point of the arrangement. They are
// the only account the region gives of which key it is to be under, and they
// stand on the far side of the word, so they reach the envelope only if the
// word put the reading back to gathering values. Written one line earlier they
// would be inside the sealed model, where §34.5.3.2 leaves them uninterpreted.
std::string RegionNamingItsKeyPastTheWord(std::string_view closing) {
  std::string text = "`pragma protect begin\n";
  text.append("  ").append(kOuterStatement).append("\n");
  text.append(SealedModel(closing));
  text.append(CurrentKeyNames());
  text.append("`pragma protect end\n");
  return text;
}

// The same names, gathered past a word standing outside every encryption region
// and spent on the region opened after it.
//
// This is the other position the subclause's own words put the rule in: what is
// gathered after the word is gathered "for the next envelope", so a value
// written between one model's ending and the next region's opening describes
// the envelope that region becomes.
std::string NextRegionNamingItsKeyPastTheWord(std::string_view closing) {
  std::string text = SealedModel(closing);
  text.append(CurrentKeyNames());
  text.append("`pragma protect begin\n");
  text.append("  ").append(kOuterStatement).append("\n");
  text.append("`pragma protect end\n");
  return text;
}

// A region enclosing a sealed model that holds a further sealed model, which
// §34.5.1 allows: the inner one is bytes of the outer like everything else it
// holds.
//
// Two of this word stand in it, and both belong to the block being written. The
// current encryption's key names stand past the outer one, which is the word
// answering the expression that opened the outer model -- the corresponding one
// this subclause names. A reading that paired the outer opening expression with
// the inner closing word would take the sealer's own key name, written between
// the two closing words, for the name the envelope is to be under.
std::string RegionAroundNestedSealedModels() {
  std::string text = "`pragma protect begin\n";
  text.append("  ").append(kOuterStatement).append("\n");
  text.append("`pragma protect begin_protected\n");
  text.append("`pragma protect begin_protected\n");
  text.append("`pragma protect end_protected\n");
  text.append("`pragma protect data_keyname=\"").append(kSealerKeyName);
  text.append("\"\n");
  text.append("`pragma protect end_protected\n");
  text.append(CurrentKeyNames());
  text.append("`pragma protect end\n");
  return text;
}

// The design an author seals, written as the region §34.5.1.1 and §34.5.2.1
// delimit. Run through the encrypting half it becomes a model whose every line
// -- its account of itself, its block, the word ending it -- that half wrote.
std::string Design(std::string_view statement) {
  std::string text = "`pragma protect begin\n";
  text.append("  ").append(statement).append("\n");
  text.append("`pragma protect end\n");
  return text;
}

// A region enclosing `sealed` -- a model the encrypting half itself produced --
// with a statement of the region's own written past that model's closing word.
//
// Nothing of the model is spelled by hand, so the word the rule speaks of is
// one a tool wrote. The statement past it says the reading came back out of the
// model there: it belongs to the region, and so to the region's own block.
std::string RegionAroundAProducedModel(const std::string& sealed) {
  std::string text = "`pragma protect begin\n";
  text.append(sealed);
  text.append("  ").append(kAfterStatement).append("\n");
  text.append("`pragma protect end\n");
  return text;
}

// A region opening with a closing word that answers no opening one, and
// enclosing a sealed model further down.
//
// The word is the end of nothing, no block having been begun for it to be the
// end of, so the name after it describes the encryption in process like any
// other line of the region. The model below is the other half of the claim: a
// count of sealed models the stray word had disturbed would take that model's
// own account of itself for this encryption's, or the region's for a model's.
std::string RegionOpeningWithAStrayWord() {
  std::string text = "`pragma protect begin\n";
  text.append(kWordDirective);
  text.append("`pragma protect author=\"").append(kAuthorEntity).append("\"\n");
  text.append("  ").append(kOuterStatement).append("\n");
  text.append("`pragma protect begin_protected\n");
  text.append("`pragma protect author=\"").append(kSealerEntity).append("\"\n");
  text.append("`pragma protect data_block=\"").append(kSealedBlockMarker);
  text.append("\"\n");
  text.append(kWordDirective);
  text.append("`pragma protect end\n");
  return text;
}

// A region enclosing a sealed model, with `closing` where that model's closing
// word belongs and §34.5.5's expression naming this design's author past it.
//
// A second, bare word stands at the foot of the model, so both spellings of
// `closing` leave a model ending somewhere and a region that closes. What the
// pair tells apart is which side of the boundary the name fell on, rather than
// whether anything was encrypted at all.
std::string RegionNamingItsAuthorPastTheWord(std::string_view closing) {
  std::string text = "`pragma protect begin\n";
  text.append("  ").append(kOuterStatement).append("\n");
  text.append("`pragma protect begin_protected\n");
  text.append("`pragma protect author=\"").append(kSealerEntity).append("\"\n");
  text.append(closing);
  text.append("`pragma protect author=\"").append(kAuthorEntity).append("\"\n");
  text.append(kWordDirective);
  text.append("`pragma protect end\n");
  return text;
}

// The same shape for §34.5.9's coding scheme, stated past the word for the
// block the region is about to become.
//
// The scheme is one the standard sets aside rather than this implementation's
// own, so an envelope that gathered the statement says so in the clear where a
// test reads it off, and one that did not states the default instead. The bare
// word at the model's foot again leaves both spellings an envelope to compare.
std::string RegionStatingASchemePastTheWord(std::string_view closing) {
  std::string text = "`pragma protect begin\n";
  text.append("  ").append(kOuterStatement).append("\n");
  text.append("`pragma protect begin_protected\n");
  text.append(closing);
  text.append("`pragma protect encoding=(enctype=\"base64\")\n");
  text.append(kWordDirective);
  text.append("`pragma protect end\n");
  return text;
}

// A region enclosing a sealed model that names, in §34.5.11's own syntax, the
// cipher its own block is under, with `closing` where the model's closing word
// belongs. No second word stands at this model's foot: it completes where the
// word does or not at all, so the pair tells a block written under the current
// method from a text nothing was written for.
std::string RegionAroundAModelNamingItsMethod(std::string_view closing) {
  std::string text = "`pragma protect begin\n";
  text.append("  ").append(kOuterStatement).append("\n");
  text.append("`pragma protect begin_protected\n");
  text.append("`pragma protect data_method=\"").append(kSealerMethod);
  text.append("\"\n");
  text.append(closing);
  text.append("`pragma protect end\n");
  return text;
}

// One region naming the current author's key and enclosing the statement, for
// the readings that are about what a produced envelope carries rather than
// about a sealed model standing in the input.
std::string RegionUnderTheAuthorsKey() {
  std::string text = "`pragma protect begin\n";
  text.append(CurrentKeyNames());
  text.append("  ").append(kOuterStatement).append("\n");
  text.append("`pragma protect end\n");
  return text;
}

// A decryption envelope carrying a keyword that speaks for the line beneath it
// and nothing for that keyword to speak for: the word closing the envelope is
// written on the very next line.
//
// `keyword` is one of the three written in that shape: §34.5.14's, which gives
// the line beneath to the key that opens the region's data block, §34.5.13's,
// which gives it to the public key those data are under, and §34.5.27's, which
// says a block carrying the region's own keys begins there. Each leaves the
// reading part way through something, and the line that arrives is the
// envelope's own ending.
std::string EnvelopeAnnouncingNothing(std::string_view keyword) {
  std::string text = "`pragma protect begin_protected\n";
  text.append("`pragma protect ").append(keyword).append("\n");
  text.append("`pragma protect end_protected\n");
  return text;
}

// A decryption envelope that announces a key, gives it, and then ends without
// ever carrying a block for that key to open.
//
// §34.5.9's identity scheme is stated for the envelope so that the key can be
// written as itself on the line the keyword speaks for; §34.5.14's keyword is
// what announces it. The envelope is complete and well formed -- it simply
// spends nothing, which is the state the run of gathered expressions ends in.
std::string EnvelopeCarryingAnUnspentKey(std::string_view key) {
  std::string text = "`pragma protect begin_protected\n";
  text.append("`pragma protect encoding=(enctype=\"raw\")\n");
  text.append("`pragma protect data_decrypt_key\n");
  text.append(key).append("\n");
  text.append("`pragma protect end_protected\n");
  return text;
}

// The directive naming the key an envelope's block is under, as a produced
// envelope writes it.
std::string KeyNameDirective(std::string_view name) {
  std::string text = "`pragma protect data_keyname=\"";
  text.append(name).append("\"\n");
  return text;
}

// `written` with `line` taken out of the envelope and written again just past
// the expression that closes it.
//
// A decryption envelope cannot be written out by hand -- what its block holds
// depends on the key the region was sealed under -- so an envelope with one of
// its expressions displaced is made by moving that expression in a real
// produced one. A text either line was not found in comes back as it stands,
// and the expectations of whichever test asked for the move then fail on the
// envelope that was never altered.
std::string WithLineMovedPastTheWord(const std::string& written,
                                     const std::string& line) {
  constexpr std::string_view kClosing = "`pragma protect end_protected\n";
  size_t at = written.find(line);
  if (at == std::string::npos) return written;
  std::string moved(written);
  moved.erase(at, line.size());
  size_t closing = moved.find(kClosing);
  if (closing == std::string::npos) return written;
  moved.insert(closing + kClosing.size(), line);
  return moved;
}

// `written` with the expression closing the envelope moved to stand just ahead
// of the block, which leaves the block on the far side of the boundary.
//
// The block is the one expression that cannot be moved instead: its characters
// depend on the key the region was sealed under, so there is no line to search
// for. Moving the word around it reaches that arrangement from the only side
// a test can spell.
std::string WithTheWordAheadOfTheBlock(const std::string& written) {
  constexpr std::string_view kClosing = "`pragma protect end_protected\n";
  constexpr std::string_view kBlockDirective = "`pragma protect data_block=";
  size_t at = written.find(kClosing);
  if (at == std::string::npos) return written;
  std::string moved(written);
  moved.erase(at, kClosing.size());
  size_t block = moved.find(kBlockDirective);
  if (block == std::string::npos) return written;
  moved.insert(block, kClosing);
  return moved;
}

// ---------------------------------------------------------------------------
// ENCRYPTION INPUT: the block the word ends is a previous one.
// ---------------------------------------------------------------------------

// The qualifier the subclause puts on the block the word ends: it is one that
// was begun. A word written where none was begun is the end of nothing, so the
// expression after it describes the encryption in process like any other line
// of the region, and it reaches the envelope.
//
// The sealed model written further down is what makes the reading answerable. A
// count of models disturbed by the stray word would take that model's own name
// for this encryption's, or would leave the region's lines looking like a
// model's, so the sealer's name and the block that model wrote are asserted
// absent beside the current author's presence.
TEST(ProtectEndProtectedDescription, AWordWithNoPreviousBlockEndsNothing) {
  std::string written = EncryptedByTheAuthor(RegionOpeningWithAStrayWord());
  EXPECT_TRUE(Holds(written, "author=\"Acme Corp\""));
  EXPECT_FALSE(Holds(written, "author=\"Other Corp\""));
  EXPECT_FALSE(Holds(written, kSealedBlockMarker));
}

// The same qualifier at the other half. A word with no previously begun region
// to answer closes none, so the envelope after it is paired with its opening
// expression, one region is closed by the reading, and the design that region
// carried arrives at the step after.
TEST(ProtectEndProtectedDescription, AWordWithNoPreviousRegionClosesNothing) {
  std::string src(kWordDirective);
  src.append(EncryptedByTheAuthor(Design(kOuterStatement)));
  ReadSource run(src, ReadSource::KeyConfig(kExchangeKey));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.Closed().size(), 1U);
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
  EXPECT_TRUE(Holds(run.text, kOuterStatement));
}

// ---------------------------------------------------------------------------
// ENCRYPTION INPUT: the block is complete, and values written after the word
// are gathered again.
// ---------------------------------------------------------------------------

// The gathering put where a produced envelope shows it. §34.5.12's name is one
// of the expressions an envelope states in the clear, so which name lands there
// says which text the encrypting half read as description of itself. The names
// written past the word are the ones it carries, and the sealer's own name --
// written inside the completed block -- is nowhere in the output.
TEST(ProtectEndProtectedDescription,
     TheNamesWrittenPastTheWordDescribeTheEnvelope) {
  std::string written =
      EncryptedUnderNames(RegionNamingItsKeyPastTheWord(kWordDirective));
  EXPECT_TRUE(Holds(written, "data_keyname=\"design-2026\""));
  EXPECT_FALSE(Holds(written, kSealerKeyName));
}

// What the gathering is worth where it counts: which key the block is really
// under. The tool holds a key under each entity's names, so the reading is
// asked for the design with the key the names past the word select, and getting
// it back is the whole path -- word, gathering, key, block -- having run.
//
// The assertion on the produced text stands ahead of the reading on purpose.
// The names are the region's only account of a key, so a run that never
// gathered them leaves the region with none and hands the design back in the
// clear -- where a reading would find the statement standing just as it does
// after a block that opened. It is the design's absence from the produced text
// that tells the two apart.
TEST(ProtectEndProtectedDescription,
     TheEnvelopeIsUnderTheKeyTheNamesPastTheWordSelect) {
  std::string written =
      EncryptedUnderNames(RegionNamingItsKeyPastTheWord(kWordDirective));
  ASSERT_FALSE(Holds(written, kOuterStatement));
  ReadSource run(written, ReadSource::KeyConfig(kAuthorKey));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, kOuterStatement));
}

// The other half of that pair. The sealer's key is a real key this tool holds,
// and it is not what the region was sealed under: a run that had gone on
// gathering the sealed model's names would have reached it, and the reading
// offered it here would open the block.
//
// The count of closed regions is read off the same failure, and it is the half
// of it that belongs to this word: the block stayed shut, so the word that
// travelled inside it never arrived to end a model of its own, and the reading
// closes only the envelope the file itself wrote.
TEST(ProtectEndProtectedDescription, TheSealedModelsNamesSelectNoKeyForIt) {
  ReadSource run(
      EncryptedUnderNames(RegionNamingItsKeyPastTheWord(kWordDirective)),
      ReadSource::KeyConfig(kSealerKey));
  EXPECT_TRUE(run.diag.HasErrors());
  EXPECT_FALSE(Holds(run.text, kOuterStatement));
  EXPECT_EQ(run.Closed().size(), 1U);
}

// The closest input the rule has to turn away, and the one that says the word
// is what restarts the gathering: the same arrangement with the word written in
// the spelling §34.5.4.1 leaves closing nothing. No block is completed, so the
// names below it are inside one still and are never gathered -- the region is
// left designating no key, and a region with no key is one nothing is written
// for. Its own closing delimiter is inside the unfinished model as well, so the
// design the author meant to seal goes back readable.
TEST(ProtectEndProtectedDescription,
     AWordCompletingNoBlockLeavesTheNamesUngathered) {
  std::string written =
      EncryptedUnderNames(RegionNamingItsKeyPastTheWord(kValuedWordDirective));
  EXPECT_FALSE(Holds(written, kCurrentMethod));
  EXPECT_TRUE(Holds(written, kOuterStatement));
}

// The subclause's own words for where the gathered values go: the next
// envelope. Here the word stands outside every encryption region, so the names
// past it belong to no region as it is read -- they wait, and the region opened
// after them is what they describe.
//
// The assertion on the produced text stands ahead of the reading for the reason
// it does above: a region that gathered nothing is handed back in the clear,
// and only the design's absence from what the encrypting half wrote says a
// block was made of it at all.
TEST(ProtectEndProtectedDescription,
     TheNamesPastTheWordAreGatheredForTheNextEnvelope) {
  std::string written =
      EncryptedUnderNames(NextRegionNamingItsKeyPastTheWord(kWordDirective));
  ASSERT_FALSE(Holds(written, kOuterStatement));
  ReadSource run(written, ReadSource::KeyConfig(kAuthorKey));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, kOuterStatement));
}

// The negative form at that position. The word spelled so that it completes no
// block leaves the model running to the end of the text, so the region opened
// below is inside it as well: nothing is gathered, nothing is a region, and the
// design the author meant to seal comes back exactly as it was written.
TEST(ProtectEndProtectedDescription,
     NamesPastAWordCompletingNoBlockReachNoLaterEnvelope) {
  std::string src = NextRegionNamingItsKeyPastTheWord(kValuedWordDirective);
  std::string written = EncryptedUnderNames(src);
  EXPECT_EQ(written, src);
  EXPECT_FALSE(Holds(written, kCurrentMethod));
}

// §34.5.5's expression is the second kind of value the word restarts the
// gathering of, and the one a produced envelope states in the clear about the
// design rather than about a key. The name past the word is what the envelope
// carries; the name the sealed model wrote for itself is not.
TEST(ProtectEndProtectedDescription,
     TheAuthorNamedPastTheWordIsTheEnvelopesOwn) {
  std::string written =
      EncryptedByTheAuthor(RegionNamingItsAuthorPastTheWord(kWordDirective));
  EXPECT_TRUE(Holds(written, "author=\"Acme Corp\""));
  EXPECT_FALSE(Holds(written, "author=\"Other Corp\""));
}

// Its negative, and the pairing that says the position rather than the writing
// did the work. With the word spelled so it completes no block, the model runs
// on to the word at its foot and the same expression falls inside the block
// instead. An envelope is written either way, the region being under a key
// throughout, and this one names nobody.
TEST(ProtectEndProtectedDescription, AnAuthorInsideTheUnendedBlockNamesNobody) {
  std::string written = EncryptedByTheAuthor(
      RegionNamingItsAuthorPastTheWord(kValuedWordDirective));
  EXPECT_TRUE(Holds(written, kCurrentMethod));
  EXPECT_FALSE(Holds(written, "author="));
}

// §34.5.9's scheme is the third value the word restarts the gathering of, and
// the one whose miscarriage shows as no wrong name at all: it decides what the
// characters of each block written after it stand for. That a scheme gathered
// past the word is what the envelope states is read off further down, where the
// same statement is followed all the way to the block a reader opens with it.
//
// This is that claim's negative, and it stands here because the positive cannot
// be written without it. The statement falls inside a block the word never
// completed, so it reaches nothing: the envelope is written under this
// implementation's own scheme, and the one the region asked for is nowhere
// readable, having gone into the block with the rest of the model.
TEST(ProtectEndProtectedDescription,
     ASchemeInsideTheUnendedBlockReachesNothing) {
  std::string written = EncryptedByTheAuthor(
      RegionStatingASchemePastTheWord(kValuedWordDirective));
  EXPECT_TRUE(Holds(written, "enctype=\"x-deltahdl-block\""));
  EXPECT_FALSE(Holds(written, "base64"));
}

// ---------------------------------------------------------------------------
// ENCRYPTION OUTPUT: the word goes into the current block, under the current
// method and keys.
// ---------------------------------------------------------------------------

// The word is inside the block rather than around it. It cannot be asserted
// absent from the output -- the envelope being written spells the same word for
// itself -- so what says the sealed model's own word went into the block is the
// count holding at one across the transformation: the occurrence the source
// wrote is the model's, and the one that comes back is the envelope's.
TEST(ProtectEndProtectedDescription, TheWordOfTheSealedModelGoesIntoTheBlock) {
  std::string src = RegionNamingItsKeyPastTheWord(kWordDirective);
  ASSERT_EQ(TimesWritten(src, "end_protected"), 1U);
  std::string written = EncryptedUnderNames(src);
  EXPECT_EQ(TimesWritten(written, "end_protected"), 1U);
  EXPECT_TRUE(Holds(written, kCurrentMethod));
}

// What being inside the block is worth on the way back: opening the block puts
// the word into the text again, where it ends the model its opening expression
// re-began. Two envelopes are therefore closed by a reading of a text that
// wrote one, and none is left standing open -- which is the half of the claim
// no count of closed envelopes shows on its own, a block that had kept the
// opening word and dropped the closing one leaving the recovered model unended.
TEST(ProtectEndProtectedDescription, TheWordComesBackOutOfTheBlockAndEnds) {
  ReadSource run(
      EncryptedUnderNames(RegionNamingItsKeyPastTheWord(kWordDirective)),
      ReadSource::KeyConfig(kAuthorKey));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.Closed().size(), 2U);
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
}

// "The corresponding begin_protected", read where two of them stand. Both
// closing words are inside the one block, so the produced envelope spells the
// word once where the source wrote it twice, and the name written between them
// -- still inside the outer model -- describes no envelope. The name past the
// outer word does, which is what says the outer opening expression was paired
// with the outer closing one rather than with the inner.
TEST(ProtectEndProtectedDescription, TheWordOfEachNestedModelGoesIntoOneBlock) {
  std::string src = RegionAroundNestedSealedModels();
  ASSERT_EQ(TimesWritten(src, "end_protected"), 2U);
  std::string written = EncryptedUnderNames(src);
  EXPECT_EQ(TimesWritten(written, "end_protected"), 1U);
  EXPECT_TRUE(Holds(written, "data_keyname=\"design-2026\""));
  EXPECT_FALSE(Holds(written, kSealerKeyName));
}

// The negative form of the same rule, and the one the keys decide. A region the
// tool holds no key for has nothing to encrypt it under, so no block is written
// at all: nothing states the current method, and the word stays exactly where
// the source wrote it rather than travelling inside anything.
TEST(ProtectEndProtectedDescription, ARegionWithNoKeyLeavesTheWordWhereItIs) {
  KeylessEncryptionRun run(RegionNamingItsKeyPastTheWord(kWordDirective));
  EXPECT_FALSE(Holds(run.text, kCurrentMethod));
  EXPECT_EQ(TimesWritten(run.text, "end_protected"), 1U);
  EXPECT_TRUE(Holds(run.text, kOuterStatement));
}

// "The current method", read off the identifier §34.5.11 defines a keyword for.
// The sealed model names a cipher of its own, and that name is inside the block
// the word completed, along with the word itself, so the envelope goes on
// stating the identifier this encryption is really running under.
TEST(ProtectEndProtectedDescription,
     TheModelsMethodGoesIntoTheBlockWithTheWord) {
  std::string written =
      EncryptedByTheAuthor(RegionAroundAModelNamingItsMethod(kWordDirective));
  EXPECT_TRUE(Holds(written, kCurrentMethod));
  EXPECT_FALSE(Holds(written, kSealerMethod));
  EXPECT_EQ(TimesWritten(written, "end_protected"), 1U);
}

// The negative of that clause, decided by the keys rather than by the word. A
// region the tool holds no key for has neither a method nor a block to write,
// so the identifier the sealed model named for itself stays readable exactly
// where the source wrote it.
TEST(ProtectEndProtectedDescription, ARegionWithNoKeyStatesNoMethodForTheWord) {
  KeylessEncryptionRun run(RegionAroundAModelNamingItsMethod(kWordDirective));
  EXPECT_FALSE(Holds(run.text, kCurrentMethod));
  EXPECT_TRUE(Holds(run.text, kSealerMethod));
}

// The rule over a model no test spelled. The sealed model here is what an
// earlier run of the encrypting half produced from §34.5.3's region syntax, so
// the word going into the block is one that half wrote and everything around it
// is a produced envelope's.
//
// The count is the claim: the text handed to the second encryption spells the
// word once, and what that encryption writes spells it once too -- the one
// occurrence being the new envelope's own.
TEST(ProtectEndProtectedDescription, AProducedModelsOwnWordGoesIntoTheBlock) {
  std::string sealed = EncryptedByTheAuthor(Design(kInnerStatement));
  ASSERT_EQ(TimesWritten(sealed, "end_protected"), 1U);
  std::string written =
      EncryptedByTheAuthor(RegionAroundAProducedModel(sealed));
  EXPECT_EQ(TimesWritten(written, "end_protected"), 1U);
  EXPECT_FALSE(Holds(written, kAfterStatement));
}

// The same arrangement on the way back. Opening the outer block puts the
// produced model back where it stood, its own word ends it there, and the
// statement the region wrote past that word is region text again -- so both
// designs arrive at the step after and no envelope is left standing open.
TEST(ProtectEndProtectedDescription, AProducedModelsWordComesBackAndEndsIt) {
  std::string written = EncryptedByTheAuthor(RegionAroundAProducedModel(
      EncryptedByTheAuthor(Design(kInnerStatement))));
  ReadSource run(written, ReadSource::KeyConfig(kExchangeKey));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, kInnerStatement));
  EXPECT_TRUE(Holds(run.text, kAfterStatement));
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
}

// ---------------------------------------------------------------------------
// DECRYPTION INPUT: the word ends a run of pragma expressions that suffices to
// open the current block.
// ---------------------------------------------------------------------------

// A keyword left waiting for the line beneath it is answered by the word. The
// run ends there, so the designation that keyword began was never completed and
// is dropped.
//
// What the alternative costs is the envelope itself. The line the keyword would
// take is the directive spelling the word, so a reading that took it would
// spend the envelope's own ending on a key nobody wrote and leave the envelope
// open -- with every later line of the file inside somebody else's protected
// region, and a complaint about an encoded value where the source wrote a
// pragma.
TEST(ProtectEndProtectedDescription, TheWordAnswersAKeyLeftAwaitingItsLine) {
  ReadSource run(EnvelopeAnnouncingNothing("data_decrypt_key"),
                 ReadSource::KeyConfig(kExchangeKey));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
  EXPECT_EQ(run.Closed().size(), 1U);
}

// The same for §34.5.13's keyword, which leaves the reading part way through a
// designation of a different kind: the public key the region's data are under
// rather than the key itself. The two are carried apart and read by separate
// steps, so a word that answered one of them says nothing about the other.
TEST(ProtectEndProtectedDescription,
     TheWordAnswersADesignationLeftAwaitingItsLine) {
  ReadSource run(EnvelopeAnnouncingNothing("data_public_key"),
                 ReadSource::KeyConfig(kExchangeKey));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
  EXPECT_EQ(run.Closed().size(), 1U);
}

// The third keyword written in that shape, and the one whose answering does the
// most: §34.5.27 gives the line beneath to a block, which a reading opens and
// then reads through as a source text of its own. A word taken for that block
// would be carried into a decryption and a reading one step deeper before
// anything noticed it was the envelope's ending.
TEST(ProtectEndProtectedDescription,
     TheWordAnswersAKeyBlockLeftAwaitingItsLine) {
  ReadSource run(EnvelopeAnnouncingNothing("key_block"),
                 ReadSource::KeyConfig(kExchangeKey));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
  EXPECT_EQ(run.Closed().size(), 1U);
}

// The run can end on the very directive that opened a designation. §22.5.1 lets
// one directive carry a list of expressions, so a keyword speaking for the line
// beneath it and the word ending the run stand side by side -- and the line
// beneath is then design rather than the value that keyword was left waiting
// for, the run having ended between them.
//
// Reading the directive's characters cannot settle this one. The word is on the
// line before the designation has been opened, so what ends the run has to be
// the expression itself, where the order the two were written in is known.
TEST(ProtectEndProtectedDescription, TheWordEndsTheRunItsOwnDirectiveOpened) {
  std::string src = "`pragma protect begin_protected\n";
  src.append("`pragma protect data_decrypt_key, end_protected\n");
  src.append("  ").append(kOuterStatement).append("\n");
  ReadSource run(src, ReadSource::KeyConfig(kExchangeKey));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
  EXPECT_TRUE(Holds(run.text, kOuterStatement));
}

// What the run the word ends holds besides the names of keys. §34.5.9's scheme
// is gathered with everything else, and this envelope is written under one the
// standard sets aside rather than the default, so the block's characters stand
// for nothing without it. Getting the design back is the run having carried the
// scheme as well.
//
// The assertion on the produced text stands ahead of the reading on purpose: it
// says the scheme reached the envelope at all. Without it a run that fell back
// to this implementation's own writing would look like one that honored the
// region's statement.
TEST(ProtectEndProtectedDescription,
     TheSchemeInTheRunIsWhatTheBlockIsReadUnder) {
  std::string written =
      EncryptedByTheAuthor(RegionStatingASchemePastTheWord(kWordDirective));
  ASSERT_TRUE(Holds(written, "enctype=\"base64\""));
  ReadSource run(written, ReadSource::KeyConfig(kExchangeKey));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, kOuterStatement));
}

// The boundary from the other direction, over §34.5.15's expression. A real
// produced envelope has its closing word moved to stand ahead of its block, so
// the block is now past the word: the run it belonged to has ended and there is
// no region for it to be the block of. Nothing is reported -- a block outside
// every region is not this reading's business -- and the design stays away.
TEST(ProtectEndProtectedDescription, ABlockLeftPastTheWordBelongsToNoRun) {
  ReadSource run(
      WithTheWordAheadOfTheBlock(EncryptedByTheAuthor(Design(kOuterStatement))),
      ReadSource::KeyConfig(kExchangeKey));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(Holds(run.text, kOuterStatement));
}

// The run being sufficient for the current block is also the run being spent on
// it. An envelope that gathered a key and carried no block for it to open ends
// at the word with that key gone, so the envelope written after it is opened by
// what its own run carries.
//
// The key gathered here is a real key of a real reader and simply not this
// envelope's. Carried across, it would be preferred to the key the user
// supplied, and the design would stay sealed behind a key the source of it
// never named.
TEST(ProtectEndProtectedDescription, AKeyOneRunGatheredDoesNotOpenTheNext) {
  std::string src = EnvelopeCarryingAnUnspentKey(kOtherReaderKey);
  src.append(EncryptedByTheAuthor(RegionUnderTheAuthorsKey()));
  ReadSource run(src, ReadSource::KeyConfig(kExchangeKey));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, kOuterStatement));
}

// The pairing that says the key really was gathered rather than never read. The
// same arrangement with the two keys exchanged: the envelope ahead carries the
// key the block after it was written under, and the reader holds one that was
// not. The run ended at the word, so what the reader holds is what the block is
// tried with, and the design does not come back.
TEST(ProtectEndProtectedDescription, TheNextBlockIsNotOpenedByTheEarlierKey) {
  std::string src = EnvelopeCarryingAnUnspentKey(kExchangeKey);
  src.append(EncryptedByTheAuthor(RegionUnderTheAuthorsKey()));
  ReadSource run(src, ReadSource::KeyConfig(kOtherReaderKey));
  EXPECT_TRUE(run.diag.HasErrors());
  EXPECT_FALSE(Holds(run.text, kOuterStatement));
}

// The run is bounded on the other side too: an expression written past the word
// is outside the run that word ended, so it is no part of what opens the block.
// The envelope here is a real produced one with the expression naming its key
// moved from inside the envelope to just past its ending -- the same
// characters, on the far side of the boundary -- and the block is left with
// nothing to be opened with.
TEST(ProtectEndProtectedDescription, AnExpressionPastTheWordIsOutsideTheRun) {
  ReadSource run(
      WithLineMovedPastTheWord(EncryptedUnderNames(RegionUnderTheAuthorsKey()),
                               KeyNameDirective(kAuthorKeyName)),
      ReadSource::KeysConfig(BothEntitiesKeys()));
  EXPECT_TRUE(run.diag.HasErrors());
  EXPECT_FALSE(Holds(run.text, kOuterStatement));
}

// The control the test above needs to mean anything. The very same envelope
// with that expression left where the encrypting half wrote it -- inside the
// run the word ends -- opens under the keys the reader was given. Without this
// pairing an envelope that opened for no reader would look exactly like one
// whose run had been cut correctly.
TEST(ProtectEndProtectedDescription, TheSameExpressionInsideTheRunOpensIt) {
  ReadSource run(EncryptedUnderNames(RegionUnderTheAuthorsKey()),
                 ReadSource::KeysConfig(BothEntitiesKeys()));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, kOuterStatement));
}

}  // namespace
