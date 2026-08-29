// §34.5.3.2 Description, the three ENCRYPTION INPUT headings, for the protect
// pragma keyword that opens a region of text some earlier encryption sealed.
// The syntax block above the subclause settles how the expression is spelled;
// this one settles what a tool does with one, and it settles it under each of
// three headings. The ENCRYPTION OUTPUT and DECRYPTION INPUT headings are
// covered in test/src/unit/test_preprocessor_subclause_34_05_03_02b.cpp.
//
// A begin_protected-end_protected block standing in the text an encrypting tool
// was handed is a model somebody sealed already, and what its contents are to
// that tool is input cleartext -- bytes to be carried into whatever region
// encloses them rather than description of anything. That is what lets a sealed
// model be resealed as one part of a larger one. Two consequences are stated
// outright: the protect pragmas written inside such a block are not interpreted
// and do not displace the values the encryption now in process has in effect,
// and the encryption nested inside this one leaves those values uncorrupted.
// Those two and the rule they follow from are the three sections below.
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
// expressions whose displacement the rule forbids, §34.5.11's data_method is
// the identifier an envelope states for its block, §34.5.13's and §34.5.14's
// keywords speak for the line beneath them and only inside a region this word
// began, and §34.5.1.1 and §34.5.2.1 delimit the larger model a sealed one is
// resealed inside of. Every text below is written as directive syntax and
// driven through the encrypting half, the preprocessor, or both in turn, rather
// than handed to the envelope state by hand.
//
// The texts five of the subclause's six sections share are written in
// lib/cpp/test_helpers/helpers_protect_sealed_model.h. What stands below the
// includes here is the texts only the sections in this file reach.

#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_protect_read.h"
#include "helpers_protect_sealed_model.h"
#include "helpers_reported_error.h"
#include "helpers_text_lines.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_envelope.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

// The same as kSealedBlockMarker, for the model sealed inside that one: a
// value written in its data_block that nothing else in any text below spells,
// long enough that finding it in an output is finding it carried rather than
// coincided with.
constexpr std::string_view kNestedBlockMarker = "NESTEDMODELBLOCKMARKER";

// SealedModel with a further sealed model written inside it and the sealing
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

// PublicKeyDesignation written inside a model somebody sealed already.
std::string SealedModelHoldingAPublicKeyDesignation() {
  std::string text = "`pragma protect begin_protected\n";
  text.append(PublicKeyDesignation());
  text.append("`pragma protect end_protected\n");
  return text;
}

// NamedRegionAround with its own key name written below the sealed model
// rather than above it. What that position asks is whether the reading came
// back out of the model where the model ended: a name written after a block
// that never closed would never be read at all.
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
  ReadSource run(EncryptedByTheAuthor(UnnamedRegionAround(
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
  // §34.5.11.2 has the data_method state the algorithm a block is decrypted
  // with, and the sealed model names a cipher of its own that this reader does
  // not provide, so that is what the reading cannot get past -- it is met
  // before the key is, a block under an unprovided cipher being unreadable
  // whatever key is held. What §34.5.3.2 asks of the reading either way is that
  // it report rather than let the design silently fail to appear.
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "states an encryption algorithm this implementation does not provide",
      LineHolding(region, "data_block=") - 2, "34.5.11.2"));
  EXPECT_TRUE(Holds(run.text, kOuterStatement));
}

// §34.5.15's block is one of the expressions the sealed model carries, and it
// is not read as a block of the encryption now in process either. A block
// belonging to a model sealed already is passed over rather than objected to,
// so nothing is reported about it.
TEST(ProtectBeginProtectedDescription,
     TheBlockInsideTheSealedModelIsNotTakenForOneOfThisEnvelopes) {
  EncryptionRun run(UnnamedRegionAround(SealedModel()));
  EXPECT_EQ(run.diag.ErrorCount(), 0U);
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
  EncryptionRun run(UnnamedRegionAround(SealedModelHoldingAnother()));
  EXPECT_EQ(run.diag.ErrorCount(), 0U);
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
      EncryptedByTheAuthor(UnnamedRegionAround(SealedModelDeclaringAScheme()));
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

}  // namespace
