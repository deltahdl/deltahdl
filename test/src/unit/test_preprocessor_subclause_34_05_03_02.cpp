// §34.5.3.2 Description, for the protect pragma keyword that opens a region of
// text some earlier encryption sealed. The syntax block above it settles how
// the expression is spelled; this one settles what a tool does with one, and it
// settles it under each of the three headings the subclause writes its rules
// under.
//
// ENCRYPTION INPUT. A begin_protected-end_protected block standing in the text
// an encrypting tool was handed is a model somebody sealed already, and what
// its contents are to that tool is input cleartext -- bytes to be carried into
// whatever region encloses them rather than description of anything. That is
// what lets a sealed model be resealed as one part of a larger one. Two
// consequences are stated outright: the protect pragmas written inside such a
// block are not interpreted and do not displace the values the encryption now
// in process has in effect, and the encryption nested inside this one leaves
// those values uncorrupted.
//
// ENCRYPTION OUTPUT. The opening expression itself, and everything up to the
// closing expression answering it, go into the data_block of the envelope being
// written, under the method and the keys that encryption is running with. The
// delimiters are inside the block rather than around it, so nothing of the
// earlier model -- not even the words that marked where it began and ended --
// is left readable in what the tool writes out.
//
// DECRYPTION INPUT. The same expression read from the other side begins a
// region that was encrypted already, and a decrypting tool gathers the pragma
// expressions the block carries so that it has them when it comes to open the
// block. An expression standing where no such region was begun opens nothing,
// and a block whose region never carried the expression naming its key has
// nothing to be opened with.
//
// All of it is preprocessor-stage. src/preprocessor/protect_processing.cpp
// carries the encrypting half: it walks a source text through a counter of the
// previously sealed models it stands inside, holds the lines of one back from
// every reading that puts a value in effect, and hands them unread to the block
// of the enclosing region.
// src/preprocessor/protect_envelope_output.cpp writes the envelope that block
// goes into. src/preprocessor/protect_envelope.cpp opens the region on the
// decrypting side and accumulates the expressions written inside it, and
// src/preprocessor/preprocessor_protect_keys.cpp is where the accumulated
// expressions select the key a block is opened with.
//
// The inputs are the real syntax of the dependencies this rule consumes.
// §34.5.4.1's word closes each sealed model, §34.5.15's data_block is what one
// carries, §34.5.10's data_keyowner and §34.5.12's data_keyname are the
// expressions whose displacement the rule forbids and whose accumulation it
// requires, §34.5.11's data_method is the identifier an envelope states for its
// block, §34.5.13's and §34.5.14's keywords speak for the line beneath them and
// only inside a region this word began, and §34.5.1.1 and §34.5.2.1 delimit the
// larger model a sealed one is resealed inside of. Every text below is written
// as directive syntax and driven through the encrypting half, the preprocessor,
// or both in turn, rather than handed to the envelope state by hand.

#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_protect_read.h"
#include "helpers_protect_keys.h"
#include "helpers_reported_error.h"
#include "helpers_text_lines.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_envelope.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

// The entity writing the larger model, and the name picking its key out of the
// list of keys that entity provided. §34.5.10 and §34.5.12 give the pair, and
// neither half reaches a key alone.
constexpr std::string_view kAuthorEntity = "Acme Corp";
constexpr std::string_view kAuthorKeyName = "design-2026";
constexpr std::string_view kAuthorKey = "acme-design-key";

// §34.5.10 lets one of that entity's keys be picked out by the public key it is
// rather than by the name given to it, and §34.5.13 has that value written on
// the line beneath the keyword announcing it. This is the value; the key it
// selects is the same one the name above selects, the two being alternative
// ways into one list rather than two keys.
constexpr std::string_view kAuthorPublicKey = "acme-public-key";

// The same pair for whoever sealed the model being resealed. Their key is
// supplied to the tool alongside the one above, so a run that let their names
// displace the current ones would reach a real key and produce a real envelope
// -- one nothing holding the current author's key could open.
constexpr std::string_view kSealerEntity = "Other Corp";
constexpr std::string_view kSealerKeyName = "other-2019";
constexpr std::string_view kSealerKey = "other-legacy-key";

// The statement the larger model encloses, and the one the sealed model that
// was produced by an earlier run of the encrypting half encloses. Neither
// survives the writing of a block, so finding either in a tool's output is
// finding text that was not sealed.
constexpr std::string_view kOuterStatement = "initial result = 42;";
constexpr std::string_view kInnerStatement = "initial sealed = 7;";

// A value written inside the sealed model that nothing else in any text below
// spells. It is long enough that finding it in an output is finding it carried
// rather than coincided with.
constexpr std::string_view kSealedBlockMarker = "SEALEDMODELBLOCKMARKER";
constexpr std::string_view kNestedBlockMarker = "NESTEDMODELBLOCKMARKER";

// The identifier the sealed model names for the cipher its own block is under.
// §34.5.11 defines the keyword; what it is doing here is standing as a value
// the current encryption would be writing out if it had read the sealed model's
// description as its own.
constexpr std::string_view kSealerMethod = "x-legacy-cipher";

// The identifier this implementation states for the blocks it writes, which is
// the method the current encryption is running under.
constexpr std::string_view kCurrentMethod = "x-deltahdl-stream";
// Both entities' keys, supplied to whichever half is running. Holding the
// sealed model's key too is what makes the tests below discriminating: a run
// that read the sealed model's names as its own would find a key under them
// rather than falling back to the current author's for want of one.
ProtectKeyList BothEntitiesKeys() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kAuthorEntity, kAuthorKeyName, kAuthorKey));
  keys.Add(KeyOf(kSealerEntity, kSealerKeyName, kSealerKey));
  return keys;
}

// One key of the current author's, held under the public key it is rather than
// under a name given to it.
//
// It is a list of its own rather than an entry added to the one above, because
// the two lists are asked different questions. A region designating its key by
// public key alone reaches this list only through that designation, so a run
// that never made the designation is left with no key -- which is what makes
// the two placements of the designation tell apart. A list that also held the
// key under a name would answer either way.
ProtectKeyList KeysUnderThePublicKey() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kAuthorEntity, kAuthorPublicKey, kAuthorKey));
  return keys;
}

// The same, under the keys the two entities provided, which is what a region
// naming an entity and one of its keys is encrypted with.
std::string EncryptedUnderNames(const std::string& src) {
  return EncryptEnvelopes(src, {}, BothEntitiesKeys());
}

// The same again, under the one key held by the public key it is.
std::string EncryptedUnderThePublicKey(const std::string& src) {
  return EncryptEnvelopes(src, {}, KeysUnderThePublicKey());
}

// The design an author seals, written as the region §34.5.1.1 and §34.5.2.1
// delimit, enclosing `statement`.
std::string Design(std::string_view statement) {
  std::string text = "`pragma protect begin\n";
  text.append("  ").append(statement).append("\n");
  text.append("`pragma protect end\n");
  return text;
}

// A model somebody sealed earlier, written by hand as the decryption envelope
// §34.5.3.1 opens and §34.5.4.1 closes.
//
// What it describes itself with is the real syntax of the dependencies this
// rule consumes: §34.5.5's author, §34.5.11's identifier for the cipher its
// block is under, §34.5.10's entity and §34.5.12's key name, and §34.5.15's
// block itself. Every one of them is a value the current encryption would be
// writing out if the block's contents were read as description rather than as
// cleartext, which is what makes their absence from a produced envelope worth
// asserting.
std::string SealedModel() {
  std::string text = "`pragma protect begin_protected\n";
  text.append("`pragma protect author=\"").append(kSealerEntity).append("\"\n");
  text.append("`pragma protect data_method=\"").append(kSealerMethod);
  text.append("\"\n");
  text.append("`pragma protect data_keyowner=\"").append(kSealerEntity);
  text.append("\"\n");
  text.append("`pragma protect data_keyname=\"").append(kSealerKeyName);
  text.append("\"\n");
  text.append("`pragma protect data_block=\"").append(kSealedBlockMarker);
  text.append("\"\n");
  text.append("`pragma protect end_protected\n");
  return text;
}

// The same, with a further sealed model written inside it and the sealing
// entity's key name written after that inner model closes.
//
// §34.5.1 has a block inside a block travel as bytes like everything else, so
// what ends the outer one is the closing expression answering its own opening
// expression rather than the first closing expression met. The key name below
// the inner model is what says which of the two readings ran: it is still
// inside the outer sealed model, so a reading that ended that model at the
// inner closing expression would take the name as description of the encryption
// now in process.
std::string SealedModelHoldingAnother() {
  std::string text = "`pragma protect begin_protected\n";
  text.append("`pragma protect data_keyowner=\"").append(kSealerEntity);
  text.append("\"\n");
  text.append("`pragma protect begin_protected\n");
  text.append("`pragma protect data_block=\"").append(kNestedBlockMarker);
  text.append("\"\n");
  text.append("`pragma protect end_protected\n");
  text.append("`pragma protect data_keyname=\"").append(kSealerKeyName);
  text.append("\"\n");
  text.append("`pragma protect data_block=\"").append(kSealedBlockMarker);
  text.append("\"\n");
  text.append("`pragma protect end_protected\n");
  return text;
}

// A sealed model that describes itself with names only.
//
// A block of its own would be tried against the reader's key wherever this
// model is met -- standing outside every region, or recovered out of the block
// of one -- and reported for not opening, which would say nothing about the
// names. What is under test in either position is which text the names reach,
// so the names are all there is.
std::string SealedModelNamingItsOwnKeys() {
  std::string text = "`pragma protect begin_protected\n";
  text.append("`pragma protect author=\"").append(kSealerEntity).append("\"\n");
  text.append("`pragma protect data_keyowner=\"").append(kSealerEntity);
  text.append("\"\n");
  text.append("`pragma protect data_keyname=\"").append(kSealerKeyName);
  text.append("\"\n");
  text.append("`pragma protect end_protected\n");
  return text;
}

// A sealed model stating §34.5.9's coding scheme for its own blocks. The scheme
// is one the standard sets aside rather than this implementation's own, so an
// envelope that had taken the statement in would say so in the clear where a
// test can read it off.
std::string SealedModelDeclaringAScheme() {
  std::string text = "`pragma protect begin_protected\n";
  text.append("`pragma protect encoding=(enctype=\"base64\")\n");
  text.append("`pragma protect data_block=\"").append(kSealedBlockMarker);
  text.append("\"\n");
  text.append("`pragma protect end_protected\n");
  return text;
}

// §34.5.13's designation of the key a region's data are under, in the spelling
// that subclause defines: the keyword standing alone, with the key's encoded
// value written on the line beneath it rather than against the keyword.
//
// This is a second shape a sealed model's contents can take. The keywords
// tested above carry what they say on their own line; this one says something
// about the line after it, so a reading that failed to pass over it would take
// a line of somebody else's model for the key its own data are to be under.
std::string PublicKeyDesignation() {
  std::string text = "`pragma protect data_public_key\n";
  text.append(kAuthorPublicKey).append("\n");
  return text;
}

// The same designation written inside a model somebody sealed already.
std::string SealedModelHoldingAPublicKeyDesignation() {
  std::string text = "`pragma protect begin_protected\n";
  text.append(PublicKeyDesignation());
  text.append("`pragma protect end_protected\n");
  return text;
}

// An encryption region enclosing `sealed`, describing itself with the names of
// the entity running the encryption now.
//
// The names stand ahead of the sealed model on purpose. They are the values in
// effect where that model is reached, so they are exactly what the subclause
// forbids the model's own contents from displacing, and the envelope this
// region becomes states them in the clear where a test can read them off.
std::string NamedRegionAround(std::string_view sealed) {
  std::string text = "`pragma protect begin\n";
  text.append("`pragma protect author=\"").append(kAuthorEntity).append("\"\n");
  text.append("`pragma protect data_keyowner=\"").append(kAuthorEntity);
  text.append("\"\n");
  text.append("`pragma protect data_keyname=\"").append(kAuthorKeyName);
  text.append("\"\n");
  text.append("  ").append(kOuterStatement).append("\n");
  text.append(sealed);
  text.append("`pragma protect end\n");
  return text;
}

// The same region with its own key name written below the sealed model rather
// than above it. What that position asks is whether the reading came back out
// of the model where the model ended: a name written after a block that never
// closed would never be read at all.
std::string NamedRegionNamingItsKeyAfter(std::string_view sealed) {
  std::string text = "`pragma protect begin\n";
  text.append("`pragma protect data_keyowner=\"").append(kAuthorEntity);
  text.append("\"\n");
  text.append("  ").append(kOuterStatement).append("\n");
  text.append(sealed);
  text.append("`pragma protect data_keyname=\"").append(kAuthorKeyName);
  text.append("\"\n");
  text.append("`pragma protect end\n");
  return text;
}

// An encryption region enclosing `sealed` and naming nobody, for the tests that
// run both halves under the single exchange key.
std::string RegionAround(std::string_view sealed) {
  std::string text = "`pragma protect begin\n";
  text.append("  ").append(kOuterStatement).append("\n");
  text.append(sealed);
  text.append("`pragma protect end\n");
  return text;
}

// One region naming `owner` and `name` for its key, enclosing `statement`.
// Two of these in one text are two regions encrypted under two keys, and each
// becomes an envelope carrying its own account of which key opens it.
std::string RegionUnderKey(std::string_view owner, std::string_view name,
                           std::string_view statement) {
  std::string text = "`pragma protect begin\n";
  text.append("`pragma protect data_keyowner=\"").append(owner).append("\"\n");
  text.append("`pragma protect data_keyname=\"").append(name).append("\"\n");
  text.append("  ").append(statement).append("\n");
  text.append("`pragma protect end\n");
  return text;
}

// A region whose one designation of a key is §34.5.13's, with `designation`
// standing where that designation is to be read from.
//
// The region states §34.5.9's identity scheme for itself, which is what lets
// the key's value be written as itself on the line the keyword speaks for. It
// names no key by name at all, so the public key is the region's only route to
// one: a run that never reached the designation is left with nothing to encrypt
// the region under, and the region goes back readable.
std::string RegionDesignatingItsKeyByPublicKey(std::string_view designation) {
  std::string text = "`pragma protect begin\n";
  text.append("`pragma protect data_keyowner=\"").append(kAuthorEntity);
  text.append("\"\n");
  text.append("`pragma protect encoding=(enctype=\"raw\")\n");
  text.append("  ").append(kOuterStatement).append("\n");
  text.append(designation);
  text.append("`pragma protect end\n");
  return text;
}

// A region announcing a designation immediately ahead of a sealed model, with
// the characters that would have named the key standing after the model rather
// than beneath the keyword.
//
// The keyword speaks for the line beneath it, and that line opens somebody
// else's model. The value the announcement never received is written below that
// model in exactly the characters the key is held under, so a reading carrying
// the announcement across would find a designation the source wrote as design.
std::string RegionAnnouncingAKeyAheadOfASealedModel() {
  std::string text = "`pragma protect begin\n";
  text.append("`pragma protect data_keyowner=\"").append(kAuthorEntity);
  text.append("\"\n");
  text.append("`pragma protect encoding=(enctype=\"raw\")\n");
  text.append("`pragma protect data_public_key\n");
  text.append(SealedModel());
  text.append(kAuthorPublicKey).append("\n");
  text.append("  ").append(kOuterStatement).append("\n");
  text.append("`pragma protect end\n");
  return text;
}

// A region opening with a closing expression that answers no opening one, and
// enclosing a sealed model further down.
//
// The stray expression ends no block, there being none open, so it is a line of
// the region like any other and the name written after it is read. The sealed
// model below is the other half of the claim: a reading whose count of the
// models it stands inside had been disturbed would take that model's lines for
// description, or the region's own lines for a model's.
std::string RegionAfterAStrayClosingExpression() {
  std::string text = "`pragma protect begin\n";
  text.append("`pragma protect end_protected\n");
  text.append("`pragma protect author=\"").append(kAuthorEntity).append("\"\n");
  text.append("  ").append(kOuterStatement).append("\n");
  text.append(SealedModel());
  text.append("`pragma protect end\n");
  return text;
}

// A region enclosing a sealed model whose closing expression was never written.
// There is no corresponding expression for the model's content to run up to, so
// the region's own closing delimiter stands inside the unfinished model rather
// than ending anything.
std::string RegionAroundAnUnclosedSealedModel() {
  std::string text = "`pragma protect begin\n";
  text.append("  ").append(kOuterStatement).append("\n");
  text.append("`pragma protect begin_protected\n");
  text.append("`pragma protect data_block=\"").append(kSealedBlockMarker);
  text.append("\"\n");
  text.append("`pragma protect end\n");
  return text;
}

// The same design under a coding scheme the region states for itself, in the
// spelling §34.5.9.1 defines. The scheme is one the standard sets aside rather
// than this implementation's own, so the envelope's block is written in
// characters that mean nothing under the default and the expression stating the
// scheme is one a reader has to have taken in to get anything back.
std::string DesignUnderDeclaredEncoding() {
  std::string text = "`pragma protect begin\n";
  text.append("`pragma protect encoding=(enctype=\"base64\")\n");
  text.append("  ").append(kOuterStatement).append("\n");
  text.append("`pragma protect end\n");
  return text;
}

// `written` with the first line spelling `line` removed.
//
// A decryption envelope cannot be written out by hand -- what its block holds
// depends on the key the region was sealed under -- so an envelope missing one
// of its expressions is made by taking that expression out of a real produced
// one. A text the line was never found in comes back as it stands, and the
// expectations of whichever test asked for the removal then fail on the
// envelope that was never altered.
std::string Without(const std::string& written, const std::string& line) {
  size_t at = written.find(line);
  if (at == std::string::npos) return written;
  std::string shortened(written);
  shortened.erase(at, line.size());
  return shortened;
}

// The directive that opens a produced envelope, and the one naming the key its
// block is under. Both are removed from produced envelopes below.
std::string OpeningDirective() { return "`pragma protect begin_protected\n"; }

std::string KeyNameDirective(std::string_view name) {
  std::string text = "`pragma protect data_keyname=\"";
  text.append(name).append("\"\n");
  return text;
}

// ---------------------------------------------------------------------------
// ENCRYPTION INPUT: the block's contents are input cleartext.
// ---------------------------------------------------------------------------

// The claim the subclause states the arrangement for: a model sealed by an
// earlier run of the encrypting half is put inside a larger model, the larger
// model is sealed in turn, and a reader holding the key gets both designs back.
//
// Nothing here is arranged by hand. The sealed model is what the encrypting
// half produced from real region syntax, the larger model encloses it with the
// same syntax, and the reading is the whole preprocessor over what the second
// encryption wrote.
TEST(ProtectBeginProtectedDescription,
     ASealedModelIsResealedAsPartOfTheLargerModel) {
  ReadSource run(EncryptedByTheAuthor(RegionAround(
                     EncryptedByTheAuthor(Design(kInnerStatement)))),
                 ReadSource::KeyConfig(kExchangeKey));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, kOuterStatement));
  EXPECT_TRUE(Holds(run.text, kInnerStatement));
}

// What being cleartext costs the sealed model in the output: its own block, the
// cipher it named, and the entity that sealed it are text of the enclosing
// region like any other, so none of them is readable in what the second
// encryption wrote.
TEST(ProtectBeginProtectedDescription,
     TheSealedModelsOwnDescriptionIsNotReadableInTheOutput) {
  std::string written = EncryptedUnderNames(NamedRegionAround(SealedModel()));
  EXPECT_FALSE(Holds(written, kSealedBlockMarker));
  EXPECT_FALSE(Holds(written, kSealerMethod));
  EXPECT_FALSE(Holds(written, kSealerEntity));
  EXPECT_FALSE(Holds(written, kOuterStatement));
}

// The other position a sealed model can be found in: outside every encryption
// region. Nothing encloses it, so its lines are carried across as the bytes
// they were written with -- its own opening word stands in the output beside
// the produced envelope's -- and the key name it states is one occurrence of
// that name rather than a second account of what the region after it is under.
TEST(ProtectBeginProtectedDescription,
     ASealedModelOutsideEveryRegionIsCarriedAcrossRatherThanRead) {
  std::string src = SealedModelNamingItsOwnKeys() + NamedRegionAround("");
  std::string written = EncryptedUnderNames(src);
  EXPECT_EQ(TimesWritten(written, "begin_protected"), 2U);
  EXPECT_EQ(TimesWritten(written, "data_keyname=\"design-2026\""), 1U);
  EXPECT_EQ(TimesWritten(written, "data_keyname=\"other-2019\""), 1U);
}

// The negative that placement has to answer. The names inside that model are a
// real entity's and a real key of theirs, and they are still not what the
// region after it is sealed under: a reading offered the sealer's key alone
// cannot open the block, which it could have done had those names been taken.
TEST(ProtectBeginProtectedDescription,
     ASealedModelOutsideEveryRegionSelectsNoKeyForTheRegionAfterIt) {
  std::string src = SealedModelNamingItsOwnKeys() + NamedRegionAround("");
  std::string written = EncryptedUnderNames(src);
  ReadSource run(written, ReadSource::KeyConfig(kSealerKey));
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma data block cannot be decrypted with the key supplied",
      LineHolding(written, "data_block="), "34.3.2"));
  EXPECT_FALSE(Holds(run.text, kOuterStatement));
}

// ---------------------------------------------------------------------------
// ENCRYPTION INPUT: the pragmas inside are not interpreted.
// ---------------------------------------------------------------------------

// §34.5.5 has the author of the design being encrypted written in the clear on
// the produced envelope, so which name lands there says which text was read as
// description. The sealed model names somebody else, and it is the current
// author's name the envelope carries.
TEST(ProtectBeginProtectedDescription,
     TheSealedModelsAuthorDoesNotDisplaceTheCurrentOne) {
  std::string written = EncryptedUnderNames(NamedRegionAround(SealedModel()));
  EXPECT_TRUE(Holds(written, "author=\"Acme Corp\""));
  EXPECT_FALSE(Holds(written, "author=\"Other Corp\""));
}

// The same read off §34.5.12's name, which the produced envelope also states in
// the clear. The sealed model names a key of its own sealer, and the envelope
// goes on stating the one the current encryption had in effect.
TEST(ProtectBeginProtectedDescription,
     TheSealedModelsKeyNameDoesNotDisplaceTheCurrentOne) {
  std::string written = EncryptedUnderNames(NamedRegionAround(SealedModel()));
  EXPECT_TRUE(Holds(written, "data_keyname=\"design-2026\""));
  EXPECT_FALSE(Holds(written, kSealerKeyName));
}

// What the names are worth, put where it counts: which key the block is really
// under. The tool holds a key under each entity's names, so a run that read the
// sealed model's names as its own would reach the sealer's key rather than
// falling back for want of one. Reading the produced envelope with the current
// author's key alone is what says which of the two it was.
//
// The model enclosed here carries names and no block. §34.5.3.2 hands the
// cleartext of the block that opened back to the source loop, so a model with a
// block of its own comes back out as an envelope to be opened in its turn, and
// this reader holds no key for the sealer's ciphertext -- the run would report
// whichever key the larger model had been sealed under, and the assertion below
// would hold nothing. With the names alone standing, the key selection is the
// only thing left that can fail.
TEST(ProtectBeginProtectedDescription,
     TheLargerModelIsEncryptedUnderTheKeyItsOwnNamesSelect) {
  ReadSource run(
      EncryptedUnderNames(NamedRegionAround(SealedModelNamingItsOwnKeys())),
      ReadSource::KeyConfig(kAuthorKey));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, kOuterStatement));
}

// The other half of that pair, and the negative form of the rule: the sealer's
// key is a real key this tool holds, and it is not what the larger model was
// sealed under. A run that had let the sealed model's names through would open
// the block here and leave the test above failing instead.
//
// The enclosed model carries no block for the reason given above, which this
// case needs as much: a nested block no key opens reports, so a run that had
// opened the larger model would still have been told to expect errors and this
// case would pass on the wrong failure.
TEST(ProtectBeginProtectedDescription,
     TheSealedModelsNamesSelectNoKeyForTheLargerModel) {
  std::string written =
      EncryptedUnderNames(NamedRegionAround(SealedModelNamingItsOwnKeys()));
  ReadSource run(written, ReadSource::KeyConfig(kSealerKey));
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma data block cannot be decrypted with the key supplied",
      LineHolding(written, "data_block="), "34.3.2"));
  EXPECT_FALSE(Holds(run.text, kOuterStatement));
}

// What a reading owes its user for an envelope it recovered out of another
// envelope's block and then cannot open.
//
// §34.5.3.2 hands the cleartext of a block back to the source loop, so a model
// somebody sealed earlier comes back out of the larger model's block as a
// decryption envelope of its own and is read like any other. The block it
// carries is under a key this reader does not hold. Neither §34.5.3.2 nor
// §34.5.4.2 says what a reading owes for that, so the rule is the one this
// reading already applies to an envelope of the text itself, in
// ABlockMissingTheExpressionThatNamesItsKeyDoesNotOpen: it reports, a design
// that silently fails to appear being indistinguishable from a design that was
// never written.
//
// What did open is kept. The larger model's own statement was recovered before
// the model inside it was met, and withholding it would charge the reader twice
// for the one key they are missing.
TEST(ProtectBeginProtectedDescription,
     AModelRecoveredOutOfABlockIsReportedWhenNoKeyOpensIt) {
  // The block that does not open is the sealed model's own, standing in the
  // text the outer block recovered to. That text is the region's body without
  // its opening line and without the author line §34.5.5 holds back from a
  // block, so the model's block stands two lines above where the region wrote
  // it.
  std::string region = NamedRegionAround(SealedModel());
  ReadSource run(EncryptedUnderNames(region),
                 ReadSource::KeyConfig(kAuthorKey));
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma data block cannot be decrypted with the key supplied",
      LineHolding(region, "data_block=") - 2, "34.3.2"));
  EXPECT_TRUE(Holds(run.text, kOuterStatement));
}

// §34.5.15's block is one of the expressions the sealed model carries, and it
// is not read as a block of the encryption now in process either. A block
// belonging to a model sealed already is passed over rather than objected to,
// so nothing is reported about it.
TEST(ProtectBeginProtectedDescription,
     TheBlockInsideTheSealedModelIsNotTakenForOneOfThisEnvelopes) {
  EncryptionRun run(RegionAround(SealedModel()));
  EXPECT_FALSE(run.report.data_block_outside_protected_block);
}

// §34.5.13's keyword is the other shape a protect pragma inside the model can
// take: it carries no value of its own and speaks for the line beneath it. It
// announces nothing there, so the region is left designating no key -- and a
// region with no key is one nothing is written for, which is what the statement
// still standing readable in the output says.
TEST(ProtectBeginProtectedDescription,
     AnAnnouncedKeyInsideTheSealedModelDesignatesNoKeyForTheRegion) {
  std::string src = RegionDesignatingItsKeyByPublicKey(
      SealedModelHoldingAPublicKeyDesignation());
  std::string written = EncryptedUnderThePublicKey(src);
  EXPECT_TRUE(Holds(written, kOuterStatement));
  EXPECT_FALSE(Holds(written, kCurrentMethod));
}

// The control that gives the test above its meaning. The very same designation,
// written where the current encryption does read it, reaches the key and the
// region is sealed under it. Without this pairing a run that designated nothing
// wherever it was written would look exactly like a run that passed over the
// sealed model correctly.
TEST(ProtectBeginProtectedDescription,
     TheSameAnnouncedKeyOutsideTheSealedModelDoesDesignateOne) {
  std::string src = RegionDesignatingItsKeyByPublicKey(PublicKeyDesignation());
  std::string written = EncryptedUnderThePublicKey(src);
  EXPECT_FALSE(Holds(written, kOuterStatement));
  EXPECT_TRUE(Holds(written, kCurrentMethod));
}

// ---------------------------------------------------------------------------
// ENCRYPTION INPUT: nested encryption corrupts none of the current values.
// ---------------------------------------------------------------------------

// The block ends where its own closing expression stands, so the reading comes
// back out with what it went in with and goes on interpreting the text after
// it. The current author's key name is written below the sealed model here, and
// the envelope states it -- which it could not do had the reading stayed inside
// the model to the end of the region.
TEST(ProtectBeginProtectedDescription,
     TheReadingResumesWithItsOwnValuesWhereTheSealedModelEnds) {
  std::string written =
      EncryptedUnderNames(NamedRegionNamingItsKeyAfter(SealedModel()));
  EXPECT_TRUE(Holds(written, "data_keyname=\"design-2026\""));
  EXPECT_FALSE(Holds(written, kSealedBlockMarker));
}

// A sealed model holding a further sealed model, which is the nesting the
// subclause has leave the current values uncorrupted. What ends the outer model
// is the closing expression answering its own opening one, so the key name
// written between the inner closing expression and the outer one is still
// inside the outer model and is not read as description of this encryption.
TEST(ProtectBeginProtectedDescription,
     AFurtherSealedModelInsideOneDoesNotEndTheOuterBlockEarly) {
  std::string written =
      EncryptedUnderNames(NamedRegionAround(SealedModelHoldingAnother()));
  EXPECT_TRUE(Holds(written, "data_keyname=\"design-2026\""));
  EXPECT_FALSE(Holds(written, kSealerKeyName));
}

// Both blocks of that arrangement are blocks of models sealed already -- the
// inner one inside two such models, the outer one inside one -- so neither is
// reported as a block belonging to no envelope, and the text goes into the
// enclosing region whole.
TEST(ProtectBeginProtectedDescription,
     NeitherBlockOfTheNestedSealedModelsIsReported) {
  EncryptionRun run(RegionAround(SealedModelHoldingAnother()));
  EXPECT_FALSE(run.report.data_block_outside_protected_block);
  EXPECT_FALSE(Holds(run.text, kNestedBlockMarker));
}

// A keyword left part way through a designation is the other thing a sealed
// model can corrupt, and the one that outlives the model rather than being
// displaced by it. The announcement is answered by the model, so the region
// designates nothing and there is nothing to encrypt it under. Carried across
// instead, it would spend itself on the line the source wrote as design below
// the model, sealing the region under a key nothing designated for it.
TEST(ProtectBeginProtectedDescription,
     AnAnnouncementAheadOfASealedModelIsAnsweredByIt) {
  std::string written =
      EncryptedUnderThePublicKey(RegionAnnouncingAKeyAheadOfASealedModel());
  EXPECT_TRUE(Holds(written, kOuterStatement));
  EXPECT_FALSE(Holds(written, kCurrentMethod));
}

// §34.5.9's coding scheme is a value of the encryption in process that a sealed
// model's own statement of it could corrupt, and one whose corruption would not
// show as a wrong name: it decides what the characters of every block written
// after it stand for. The envelope goes on stating this implementation's own
// scheme, and the one the model named for itself reaches nothing.
TEST(ProtectBeginProtectedDescription,
     TheSchemeStatedInsideTheSealedModelDoesNotDisplaceTheCurrentOne) {
  std::string written =
      EncryptedByTheAuthor(RegionAround(SealedModelDeclaringAScheme()));
  EXPECT_TRUE(Holds(written, "enctype=\"x-deltahdl-block\""));
  EXPECT_FALSE(Holds(written, "base64"));
}

// The negative form of the counting the rule rests on: a closing expression
// written where no sealed model is open ends nothing. The name after it is read
// as description, which puts it on the envelope, and the model written further
// down is still tracked from where it stands rather than from one expression
// earlier.
TEST(ProtectBeginProtectedDescription,
     AClosingExpressionWithNoModelOpenIsALineOfTheRegion) {
  std::string written =
      EncryptedByTheAuthor(RegionAfterAStrayClosingExpression());
  EXPECT_TRUE(Holds(written, "author=\"Acme Corp\""));
  EXPECT_FALSE(Holds(written, "author=\"Other Corp\""));
  EXPECT_FALSE(Holds(written, kSealedBlockMarker));
}

// ---------------------------------------------------------------------------
// ENCRYPTION OUTPUT: the expression and everything up to its closing one go
// into the current block.
// ---------------------------------------------------------------------------

// The opening expression is inside the block rather than around it. It cannot
// be asserted absent from the output -- the envelope being written spells the
// same word for itself -- so what says the sealed model's own opening word went
// into the block is the count standing at the produced envelope's one.
TEST(ProtectBeginProtectedDescription,
     TheSealedModelsOpeningExpressionGoesIntoTheCurrentBlock) {
  std::string written = EncryptedUnderNames(NamedRegionAround(SealedModel()));
  EXPECT_EQ(TimesWritten(written, "begin_protected"), 1U);
  EXPECT_EQ(TimesWritten(written, "end_protected"), 1U);
}

// The method and the keys the block is written under are the current ones. The
// envelope states this implementation's own identifier for the cipher its block
// is under, and the identifier the sealed model named for its own block is
// nowhere in the output, having gone into the block along with the rest of that
// model.
TEST(ProtectBeginProtectedDescription,
     TheBlockIsWrittenUnderTheMethodTheEnvelopeStates) {
  std::string written = EncryptedUnderNames(NamedRegionAround(SealedModel()));
  EXPECT_TRUE(Holds(written, kCurrentMethod));
  EXPECT_FALSE(Holds(written, kSealerMethod));
}

// What the delimiters being inside the block is worth on the way back: opening
// the outer block puts the sealed model's own opening and closing expressions
// back into the text, where they begin and end a region of their own. Two
// regions are therefore closed by a reading of a text that wrote one.
TEST(ProtectBeginProtectedDescription,
     TheSealedModelsDelimitersComeBackOutOfTheBlock) {
  ReadSource run(EncryptedByTheAuthor(RegionAround(
                     EncryptedByTheAuthor(Design(kInnerStatement)))),
                 ReadSource::KeyConfig(kExchangeKey));
  EXPECT_EQ(run.Closed().size(), 2U);
  EXPECT_EQ(run.OpenDecryptionEnvelopes(), 0U);
}

// The negative form of the same rule, and the one the keys decide. A region the
// tool holds no key for has nothing to encrypt it under, so no envelope is
// written at all -- nothing states the current method, and the sealed model
// goes back exactly as the source spelled it rather than into a block that
// stands for nothing.
TEST(ProtectBeginProtectedDescription,
     ARegionWithNoKeyLeavesTheSealedModelAsItStands) {
  KeylessEncryptionRun run(RegionAround(SealedModel()));
  EXPECT_FALSE(Holds(run.text, kCurrentMethod));
  EXPECT_TRUE(Holds(run.text, kSealedBlockMarker));
  EXPECT_TRUE(Holds(run.text, kOuterStatement));
}

// What the rule is bounded by, put at its edge: the content encrypted runs up
// to the closing expression answering this one, and a model whose closing
// expression was never written supplies no such point. The region's own closing
// delimiter is inside the unfinished model, so no region closes, no envelope is
// written, and the text goes back as the source spelled it -- with a key
// supplied throughout, so it is the missing boundary rather than a missing key
// that left it standing.
TEST(ProtectBeginProtectedDescription,
     ASealedModelWithNoClosingExpressionLeavesNothingToEncrypt) {
  EncryptionRun run(RegionAroundAnUnclosedSealedModel());
  EXPECT_FALSE(run.report.data_block_outside_protected_block);
  EXPECT_FALSE(Holds(run.text, kCurrentMethod));
  EXPECT_TRUE(Holds(run.text, kOuterStatement));
  EXPECT_TRUE(Holds(run.text, kSealedBlockMarker));
}

// ---------------------------------------------------------------------------
// DECRYPTION INPUT: the expression begins a previously encrypted region.
// ---------------------------------------------------------------------------

// The expression standing at the head of a produced envelope is what makes the
// block beneath it a region that was encrypted already, so the block is opened
// and the design is put back where the envelope stood.
TEST(ProtectBeginProtectedDescription,
     TheExpressionIsWhatBeginsTheRegionTheBlockBelongsTo) {
  ReadSource run(EncryptedByTheAuthor(Design(kOuterStatement)),
                 ReadSource::KeyConfig(kExchangeKey));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, kOuterStatement));
}

// The same envelope with that one directive taken out, which is the closest
// input the rule has to turn away. No region was begun, so the block beneath
// belongs to nothing: it is not opened, the design does not come back, and
// nothing is reported about a key -- there being no region for a key to have
// been offered for.
TEST(ProtectBeginProtectedDescription,
     ABlockWithNoExpressionBeginningItsRegionIsNotOpened) {
  ReadSource run(Without(EncryptedByTheAuthor(Design(kOuterStatement)),
                         OpeningDirective()),
                 ReadSource::KeyConfig(kExchangeKey));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_FALSE(Holds(run.text, kOuterStatement));
}

// §34.5.14's keyword gives the line beneath it to the encoded value of the key
// that opens a region's block, and it only speaks that way inside a region this
// expression began. Written where no region was begun there is no block for a
// key to have been made for, so the line beneath is source text and reaches the
// step after the preprocessor.
//
// Every keyword that speaks for the line after it is held back by one decision,
// taken once before any of them is looked at, so a second keyword written here
// would put the same decision to the same question and answer it the same way.
// What differs between two such keywords is which designation each goes on to
// record, and that belongs to the subclause defining it rather than to this
// one. §34.5.13's keyword is driven through this decision below, in the test
// that follows its designation all the way to the key a block is opened with,
// where the reading does turn on which keyword was written.
TEST(ProtectBeginProtectedDescription,
     TheLineBelowAnAnnouncedKeyOutsideEveryRegionIsSourceText) {
  std::string src = "`pragma protect data_decrypt_key\n";
  src.append("  ").append(kOuterStatement).append("\n");
  ReadSource run(src, ReadSource::KeyConfig(kExchangeKey));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, kOuterStatement));
}

// The same two directives inside a region this expression began. There the
// announcement is one an encrypting tool wrote into a protected block, so the
// line beneath it is key material rather than design and does not reach the
// step after.
TEST(ProtectBeginProtectedDescription,
     TheLineBelowAnAnnouncedKeyInsideTheRegionIsKeyMaterial) {
  std::string src = "`pragma protect begin_protected\n";
  src.append("`pragma protect data_decrypt_key\n");
  src.append("  ").append(kOuterStatement).append("\n");
  src.append("`pragma protect end_protected\n");
  ReadSource run(src, ReadSource::KeyConfig(kExchangeKey));
  EXPECT_FALSE(Holds(run.text, kOuterStatement));
}

// ---------------------------------------------------------------------------
// DECRYPTION INPUT: the expressions in the block are accumulated for opening
// it.
// ---------------------------------------------------------------------------

// The envelope states §34.5.10's entity and §34.5.12's key name between the
// expression that begins its region and the block itself, and the pair is what
// selects the key the block is opened with. The reading is given both entities'
// keys, so reaching the design means the pair the block carried was the pair
// that was used.
//
// The model enclosed here carries names and no block. Its cleartext is handed
// back to the source loop by the rule under test, so a model carrying a block
// of its own would be opened in its turn, and neither key opens a block written
// under a cipher that was never run -- the case would report whichever pair the
// envelope had carried, and the assertion below would hold nothing.
TEST(ProtectBeginProtectedDescription,
     TheExpressionsInTheBlockSelectTheKeyThatOpensIt) {
  ReadSource run(
      EncryptedUnderNames(NamedRegionAround(SealedModelNamingItsOwnKeys())),
      ReadSource::KeysConfig(BothEntitiesKeys()));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, kOuterStatement));
}

// The negative form: the same produced envelope with the expression naming its
// key taken out. There is nothing left in the region to accumulate that key
// from, so the block cannot be opened and the reader is told rather than left
// with an empty design.
TEST(ProtectBeginProtectedDescription,
     ABlockMissingTheExpressionThatNamesItsKeyDoesNotOpen) {
  std::string written =
      Without(EncryptedUnderNames(NamedRegionAround(SealedModel())),
              KeyNameDirective(kAuthorKeyName));
  ReadSource run(written, ReadSource::KeysConfig(BothEntitiesKeys()));
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma data block cannot be decrypted with the key supplied",
      LineHolding(written, "data_block="), "34.3.2"));
  EXPECT_FALSE(Holds(run.text, kOuterStatement));
}

// Accumulation belongs to the block rather than to the file: two regions naming
// two entities become two envelopes, each carrying its own account of which key
// opens it, and each block is opened with what its own region carried.
TEST(ProtectBeginProtectedDescription,
     EachBlockIsOpenedWithTheExpressionsItsOwnRegionCarries) {
  std::string src =
      RegionUnderKey(kAuthorEntity, kAuthorKeyName, "initial first = 1;");
  src.append(
      RegionUnderKey(kSealerEntity, kSealerKeyName, "initial second = 2;"));
  ReadSource run(EncryptedUnderNames(src),
                 ReadSource::KeysConfig(BothEntitiesKeys()));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, "initial first = 1;"));
  EXPECT_TRUE(Holds(run.text, "initial second = 2;"));
}

// The accumulated expression need not carry its value on its own line. §34.5.13
// designates a key by writing the keyword alone and the key's encoded value
// beneath it, and a block reached only through that designation is opened only
// if both lines were gathered and paired.
//
// The whole of it is built from that subclause's own syntax and driven through
// both halves: the region designates its key that way in the source, the
// encrypting half reads the designation and writes it into the envelope with
// its value re-encoded under the envelope's scheme, and the reading pairs the
// two lines again to reach the key the block is under. The key is held under no
// name at all, so no other route to it exists.
TEST(ProtectBeginProtectedDescription,
     ARegionDesignatingItsKeyByPublicKeyIsOpenedThroughThatDesignation) {
  std::string src = RegionDesignatingItsKeyByPublicKey(PublicKeyDesignation());
  ReadSource run(EncryptedUnderThePublicKey(src),
                 ReadSource::KeysConfig(KeysUnderThePublicKey()));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, kOuterStatement));
}

// The expressions accumulated are not only the ones naming keys. §34.5.9's
// coding scheme is stated inside the region too, and it decides what the
// block's characters stand for, so an envelope written under a scheme this
// implementation does not default to is one a reading has to have taken that
// statement in to get anything back from.
//
// The assertion on the produced text stands ahead of the reading on purpose: it
// is what says the scheme reached the envelope at all. Without it a run that
// silently fell back to this implementation's own writing would look exactly
// like a run that honored what the source stated.
TEST(ProtectBeginProtectedDescription,
     TheCodingSchemeStatedInTheRegionIsWhatItsBlockIsReadUnder) {
  std::string written = EncryptedByTheAuthor(DesignUnderDeclaredEncoding());
  ASSERT_TRUE(Holds(written, "enctype=\"base64\""));
  ReadSource run(written, ReadSource::KeyConfig(kExchangeKey));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, kOuterStatement));
}

}  // namespace
