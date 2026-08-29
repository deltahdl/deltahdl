// §34.5.3.2 Description, the ENCRYPTION OUTPUT and DECRYPTION INPUT headings,
// for the protect pragma keyword that opens a region of text some earlier
// encryption sealed. The syntax block above the subclause settles how the
// expression is spelled; this one settles what a tool does with one, and it
// settles it under each of three headings. The three ENCRYPTION INPUT headings
// are covered in
// test/src/unit/test_preprocessor_subclause_34_05_03_02a.cpp.
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
// All of it is preprocessor-stage.
// src/preprocessor/protect_envelope_output.cpp writes the envelope a sealed
// model's lines go into. src/preprocessor/protect_envelope.cpp opens the region
// on the decrypting side and accumulates the expressions written inside it, and
// src/preprocessor/preprocessor_protect_keys.cpp is where the accumulated
// expressions select the key a block is opened with.
// src/preprocessor/protect_processing.cpp carries the encrypting half that
// hands those lines unread to the block of the enclosing region.
//
// The inputs are the real syntax of the dependencies this rule consumes.
// §34.5.4.1's word closes each sealed model, §34.5.15's data_block is what one
// carries, §34.5.10's data_keyowner and §34.5.12's data_keyname are the
// expressions whose accumulation the rule requires, §34.5.11's data_method is
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

// Design under a coding scheme the region states for itself, in the spelling
// §34.5.9.1 defines. The scheme is one the standard sets aside rather
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

// The directive that opens a produced envelope, and the one naming the key its
// block is under. Both are removed from produced envelopes below.
std::string OpeningDirective() { return "`pragma protect begin_protected\n"; }

std::string KeyNameDirective(std::string_view name) {
  std::string text = "`pragma protect data_keyname=\"";
  text.append(name).append("\"\n");
  return text;
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
  ReadSource run(EncryptedByTheAuthor(UnnamedRegionAround(
                     EncryptedByTheAuthor(Design(kInnerStatement)))),
                 ReadSource::KeyConfig(kReadingExchangeKey));
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
  KeylessEncryptionRun run(UnnamedRegionAround(SealedModel()));
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
  EXPECT_EQ(run.diag.ErrorCount(), 0U);
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
                 ReadSource::KeyConfig(kReadingExchangeKey));
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
                 ReadSource::KeyConfig(kReadingExchangeKey));
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
  ReadSource run(src, ReadSource::KeyConfig(kReadingExchangeKey));
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
  ReadSource run(src, ReadSource::KeyConfig(kReadingExchangeKey));
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
  ReadSource run(written, ReadSource::KeyConfig(kReadingExchangeKey));
  EXPECT_FALSE(run.diag.HasErrors());
  EXPECT_TRUE(Holds(run.text, kOuterStatement));
}

}  // namespace
