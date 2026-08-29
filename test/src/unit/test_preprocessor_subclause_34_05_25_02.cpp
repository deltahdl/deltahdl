// §34.5.25 key_keyname, Description.
//
// §34.5.25.2 says four things about the keyword §34.5.25.1 spells.
//
//   The value names the key, or the key pair of an asymmetric algorithm, that
//   decrypts the key block.
//
//   It is an error to name a key that is not a member of the list of keys known
//   for the entity written beside it.
//
//   Where a text provides one, it names the key that encrypts the keys the data
//   are under. An encrypting tool combines it with that entity and determines
//   the key to use, and the name itself is output as cleartext.
//
//   On the way back it is combined with the entity to select the single key
//   that decrypts the data block of the envelope.
//
// The key pair never arises. This implementation holds a key as one value that
// an entity and a designation reach together -- ProtectKey in
// src/preprocessor/protect_keywords.h is an owner, a name and a key -- and
// offers no asymmetric algorithm for a pair to belong to, so the alternative
// the first sentence admits is one nothing here can be in.
//
// The error is stated on the path that reports it, which is a reading.
// Preprocessor::CheckKeyKeyname in
// src/preprocessor/preprocessor_protect_keynames.cpp asks it while a text is
// read, and encrypting mode reaches no Preprocessor at all, so a source sealed
// by this tool is not held to the rule its own subclause states for an
// encrypting tool's input. #3279 records that, and records what it costs: a
// region whose designations reach no key comes back exactly as it was written,
// so a mistyped name ships the design in the clear and reports nothing. A case
// below states that consequence, so the report and its absence stand together.
//
// Which spelling of the expression puts which name in effect is §34.5.25.1's
// and is stated in test_preprocessor_subclause_34_05_25_01.cpp.
//
// The last five cases below state what an encrypting run writes for a region
// that designated its key with a parenthesized list. §34.5.25.1 spells the
// expression key_keyname = <string>, and §22.5.1 makes a parenthesized
// pragma_value a list of further pragma expressions rather than the one written
// thing a string is, so a list names no key. Two consequences follow, and the
// cases take them in turn: no name is output as cleartext, and §34.5.27.2 forms
// no key block, a block being owed to each key a region designates for its own
// keys. #3273 is the defect they close: the list was taken as the name, so the
// envelope published it quoted as though a reader could pair it with the
// key_keyowner and reach the key that opens the block.
//
// These read the text the tool wrote rather than the name a Preprocessor holds.
// ProtectKeywordScope::Apply in src/preprocessor/protect_keywords.cpp already
// refuses a list, so a case reading the name back off a reading passes whatever
// the writing side does; the cases in
// test_preprocessor_subclause_34_05_25_01.cpp are of that kind.

#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_preprocessor.h"
#include "helpers_protect_keys.h"
#include "helpers_protect_keyword_value.h"
#include "helpers_reported_error.h"
#include "helpers_text_lines.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

// Two entities, each holding one key under a name of its own. The names differ
// between the lists, so a name belonging to one entity is a name the other
// holds nothing under, which is what lets a case ask whose list a name is read
// against rather than whether the characters appear anywhere at all.
constexpr std::string_view kEntity = "meridian-trust";
constexpr std::string_view kOtherEntity = "cerulean-vault";
constexpr std::string_view kEntitysKeyName = "wrapping-2027";
constexpr std::string_view kOtherEntitysKeyName = "vaulting-2027";
constexpr std::string_view kEntitysKey = "meridian-trust-wrapping-key";
constexpr std::string_view kOtherEntitysKey = "cerulean-vault-vaulting-key";

// A name neither entity holds a key under.
constexpr std::string_view kUnheldName = "wrapping-1998";

// An entity the tool was handed no keys for at all.
constexpr std::string_view kStrangerEntity = "aegis-custody";

constexpr std::string_view kSealedDesign = "module sealed_m; endmodule\n";

// A pragma_value written in the parenthesized spelling §22.5.1 defines, which
// is a list of further pragma expressions rather than the one written thing
// §34.5.25.1 writes against this keyword. Its subkeywords are names §34.4
// tabulates nowhere, so what the list says is beside the point and its spelling
// is the whole of what the cases at the foot of this file read.
constexpr std::string_view kNameList =
    "(rotation=\"quarterly\", escrowed_with=\"northwind-escrow\")";

// The key an author hands an encrypting run for a region that asks for no key
// block of its own. It is what seals such a region, and a region nothing seals
// comes back as its own source text -- where the directive under test is still
// standing, so a case reading what the tool wrote needs the region encrypted.
constexpr std::string_view kAuthorsExchangeKey = "the-authors-own-exchange-key";

// The key the entity holds under the characters the list spells. It is what
// lets the two key block cases fail: a run taking the list as a name reaches
// this key and writes the block §34.5.27.2 owes it, where an entity holding
// nothing under those characters writes no block either way.
constexpr std::string_view kKeyHeldUnderTheListsCharacters =
    "meridian-trust-escrowed-key";

// The expression §34.5.27.1 spells for a key block, which is the keyword
// standing alone on a directive of its own with the block beneath it.
constexpr std::string_view kKeyBlockExpression = "`pragma protect key_block\n";

// The report §34.5.25 draws from a name outside the entity's list.
constexpr std::string_view kNoSuchKey =
    "key_keyname names no key held by the key_keyowner in effect";

std::string Writes(std::string_view keyword, std::string_view value) {
  std::string text = "`pragma protect ";
  text.append(keyword).append("=\"").append(value).append("\"\n");
  return text;
}

// The entity written first and the name against it, which is the pair §34.5.25
// has combined. The entity comes first because the name is read against
// whichever entity stands in effect beside it.
std::string Designates(std::string_view entity, std::string_view name) {
  std::string text = Writes("key_keyowner", entity);
  text.append(Writes("key_keyname", name));
  return text;
}

// The keyword with `value` written against it as the source spelled it. Writes
// above puts quotation marks around what it is given, and a list in quotation
// marks is a string rather than the parenthesized spelling of a pragma_value.
std::string WritesAsSpelled(std::string_view keyword, std::string_view value) {
  std::string text = "`pragma protect ";
  text.append(keyword).append("=").append(value).append("\n");
  return text;
}

ProtectKeyList KeysOfBothEntities() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kEntity, kEntitysKeyName, kEntitysKey));
  keys.Add(KeyOf(kOtherEntity, kOtherEntitysKeyName, kOtherEntitysKey));
  return keys;
}

// A reading handed both lists, which is what the rule needs: a tool holding no
// list for an entity holds nothing the name can be missing from.
PreprocConfig HoldingBothLists() {
  PreprocConfig config;
  config.protect_keys = KeysOfBothEntities();
  return config;
}

// An encryption region designating a key and sealing a design.
std::string Region(const std::string& described) {
  std::string text = "`pragma protect begin\n";
  text.append(described).append(kSealedDesign);
  text.append("`pragma protect end\n");
  return text;
}

// -- The name is a member of the entity's list -------------------------------

// §34.5.25.2: it is an error to name a key that is not a member of the list
// known for the entity written beside it. The tool holds a list for this entity
// and no key of that name is in it.
TEST(ProtectKeyKeynameDescription, ANameOutsideTheEntitysListIsReported) {
  std::string src = Designates(kEntity, kUnheldName);
  PreprocFixture f;
  Preprocess(src, f, HoldingBothLists());
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoSuchKey,
                            LineHolding(src, "key_keyname"), "34.5.25"));
}

// The list a name is read against is the one the entity beside it names, and
// not every list the tool holds. This name is a key of the other entity, held
// under the other entity's name, and it is still no key of this one's.
TEST(ProtectKeyKeynameDescription, ANameOfAnotherEntitysKeyIsReported) {
  std::string src = Designates(kEntity, kOtherEntitysKeyName);
  PreprocFixture f;
  Preprocess(src, f, HoldingBothLists());
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoSuchKey,
                            LineHolding(src, "key_keyname"), "34.5.25"));
}

// The control beside them: a name the entity does hold draws no report, without
// which the two cases above would hold of a reading that reported every name.
TEST(ProtectKeyKeynameDescription, ANameInTheEntitysListIsNotReported) {
  PreprocFixture f;
  Preprocess(Designates(kEntity, kEntitysKeyName), f, HoldingBothLists());
  EXPECT_FALSE(f.diag.HasErrors());
}

// The same name under the entity that does hold it. Together with the case
// above this says the entity decides which list the name is read against: one
// pairing is reported and the other is not, and the name is the same name.
TEST(ProtectKeyKeynameDescription, TheEntityDecidesWhichListTheNameIsIn) {
  PreprocFixture f;
  Preprocess(Designates(kOtherEntity, kOtherEntitysKeyName), f,
             HoldingBothLists());
  EXPECT_FALSE(f.diag.HasErrors());
}

// An entity the tool holds no keys for at all. A name cannot be found missing
// from a list that was never supplied, so there is nothing to report and the
// name stands -- a different state from a list the name is absent from.
TEST(ProtectKeyKeynameDescription, AnEntityWithNoListDrawsNoReport) {
  PreprocFixture f;
  Preprocess(Designates(kStrangerEntity, kUnheldName), f, HoldingBothLists());
  EXPECT_FALSE(f.diag.HasErrors());
}

// -- The key the pair selects ------------------------------------------------

// §34.5.25.2: on the way back the name is combined with the entity to select
// the single key the envelope is opened through. Neither half reaches a key
// alone, so what the pair selects is what a case can read.
TEST(ProtectKeyKeynameDescription, ThePairSelectsTheKeyTheBlockIsOpenedWith) {
  ProtectKeyList keys = KeysOfBothEntities();
  EXPECT_EQ(ReadKeywordScope(Designates(kEntity, kEntitysKeyName))
                .KeyBlockKeyReached(keys),
            kEntitysKey);
  EXPECT_EQ(ReadKeywordScope(Designates(kOtherEntity, kOtherEntitysKeyName))
                .KeyBlockKeyReached(keys),
            kOtherEntitysKey);
}

// The pairing that reaches nothing. Each half names something the tool holds,
// and the two together name no key of anybody's, so the pair rather than either
// half is what selects.
TEST(ProtectKeyKeynameDescription, TheHalvesOfOnePairReachNothingCrossed) {
  ProtectKeyList keys = KeysOfBothEntities();
  EXPECT_TRUE(ReadKeywordScope(Designates(kEntity, kOtherEntitysKeyName))
                  .KeyBlockKeyReached(keys)
                  .empty());
}

// -- What an encrypting run writes and does not write ------------------------

// §34.5.25.2: the name itself is output as cleartext. It stands beside the
// envelope, where a reader pairs it with the entity before opening anything,
// rather than inside the block it is needed to open.
TEST(ProtectKeyKeynameDescription, TheNameStandsAsCleartextOnTheEnvelope) {
  std::string envelope = EncryptEnvelopes(
      Region(Designates(kEntity, kEntitysKeyName)), {}, KeysOfBothEntities());
  EXPECT_FALSE(Holds(envelope, kSealedDesign)) << envelope;
  EXPECT_TRUE(Holds(envelope, Writes("key_keyname", kEntitysKeyName)))
      << envelope;
}

// It stands in the block's own directive as well, that being where a reader
// meeting one block of several learns which key opens this one.
TEST(ProtectKeyKeynameDescription,
     TheNameStandsAsCleartextInTheBlocksOwnDirective) {
  std::string envelope = EncryptEnvelopes(
      Region(Designates(kEntity, kEntitysKeyName)), {}, KeysOfBothEntities());
  EXPECT_TRUE(Holds(envelope, "`pragma protect key_block")) << envelope;
  EXPECT_EQ(TimesWritten(envelope, Writes("key_keyname", kEntitysKeyName)), 2U)
      << envelope;
}

// What the missing report is instead of. §34.5.25.2 states its error for an
// encrypting tool's input, and encrypting mode asks no Preprocessor anything,
// so a region naming a key nobody holds reaches no key, is written no block,
// and comes back exactly as it stood -- design and all, with nothing said.
// #3279 is that gap; this case is what it costs.
TEST(ProtectKeyKeynameDescription, ARegionNamingAKeyNobodyHoldsIsSealedByNone) {
  std::string region = Region(Designates(kEntity, kUnheldName));
  EXPECT_EQ(EncryptEnvelopes(region, {}, KeysOfBothEntities()), region);
}

// -- A parenthesized list names no key ---------------------------------------

// §34.5.25.1 writes a string against this keyword, and §22.5.1 makes a
// parenthesized pragma_value a list of further pragma expressions rather than
// one written thing, so a list names no key. §34.5.25.2 outputs the name as
// cleartext, and a region that named none leaves the envelope with no
// key_keyname directive to output.
//
// The design is checked gone first because a region nothing sealed comes back
// as its own source text, and that text writes the directive under test.
TEST(ProtectKeyKeynameDescription, AListPutsNoKeyNameOnTheEnvelope) {
  std::string envelope = EncryptEnvelopes(
      Region(WritesAsSpelled("key_keyname", kNameList)), kAuthorsExchangeKey);
  EXPECT_FALSE(Holds(envelope, kSealedDesign)) << envelope;
  EXPECT_EQ(TimesWritten(envelope, "key_keyname="), 0U) << envelope;
}

// The control beside it: the spelling §34.5.25.1 does define is output as
// cleartext. Without this the case above would hold of a tool that wrote no
// key_keyname directive whatever the region designated.
TEST(ProtectKeyKeynameDescription, AStringNamesTheKeyTheEnvelopeOutputs) {
  std::string envelope = EncryptEnvelopes(
      Region(Writes("key_keyname", kEntitysKeyName)), kAuthorsExchangeKey);
  EXPECT_FALSE(Holds(envelope, kSealedDesign)) << envelope;
  EXPECT_TRUE(Holds(envelope, Writes("key_keyname", kEntitysKeyName)))
      << envelope;
}

// A list written after a string has named no key, so the key the string named
// still stands and that string is the cleartext the envelope outputs. The list
// itself appears nowhere, which is also what says the region was encrypted
// rather than handed back.
TEST(ProtectKeyKeynameDescription,
     AListLeavesTheStringWrittenBeforeItStanding) {
  std::string envelope =
      EncryptEnvelopes(Region(Writes("key_keyname", kEntitysKeyName) +
                              WritesAsSpelled("key_keyname", kNameList)),
                       kAuthorsExchangeKey);
  EXPECT_TRUE(Holds(envelope, Writes("key_keyname", kEntitysKeyName)))
      << envelope;
  EXPECT_FALSE(Holds(envelope, kNameList)) << envelope;
}

// -- The key block the designation asks for ----------------------------------

// The entity's list holding a key under its own name and a second under the
// characters the list spells. Both cases below are handed this one list, so
// what separates them is the spelling the region designated its key in.
ProtectKeyList KeysHeldUnderBothSpellings() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kEntity, kEntitysKeyName, kEntitysKey));
  keys.Add(KeyOf(kEntity, kNameList, kKeyHeldUnderTheListsCharacters));
  return keys;
}

// §34.5.27.2 forms a key block for a region designating a key for its own keys,
// and §34.5.25.1 writes a string for that designation, so a list designates
// none and the region asks for no block. The entity holds a key under the
// characters the list spells, so a run that took the list would find that key
// and write the block.
TEST(ProtectKeyKeynameDescription, AListAsksForNoKeyBlock) {
  std::string region = Region(Writes("key_keyowner", kEntity) +
                              WritesAsSpelled("key_keyname", kNameList));
  std::string envelope =
      EncryptEnvelopes(region, {}, KeysHeldUnderBothSpellings());
  EXPECT_EQ(TimesWritten(envelope, kKeyBlockExpression), 0U) << envelope;
}

// The control beside it: the string spelling designates the entity's key and
// the envelope carries the one block that key opens. Without it the case above
// would hold of a run that wrote no key block for this region however the
// region designated its key.
TEST(ProtectKeyKeynameDescription, AStringAsksForTheOneKeyBlock) {
  std::string region = Region(Designates(kEntity, kEntitysKeyName));
  std::string envelope =
      EncryptEnvelopes(region, {}, KeysHeldUnderBothSpellings());
  EXPECT_EQ(TimesWritten(envelope, kKeyBlockExpression), 1U) << envelope;
}

}  // namespace
