// §34.5.12.2 data_keyname, Description.
//
// The subclause says three things about the keyword §34.5.12.1 spells.
//
//   Written in an encrypting tool's input, it names the key -- or the key pair,
//   where the algorithm is asymmetric -- that the data_block is to be decrypted
//   with. It shall be an error to name a key that is not a member of the list
//   of keys known for the data_keyowner given.
//
//   The name is output as cleartext in the output file, except where a digital
//   envelope is used, in which case it is encrypted under the key_method and
//   the key the key_keyname or key_public_key designates, and encoded in the
//   key_block.
//
//   Read in a protected envelope, the name is combined with the data_keyowner
//   to select the single key the data_block is decrypted with.
//
// The first is the rule with teeth and it is what this file leads with: a name
// outside the entity's list is reported where it is written, by
// Preprocessor::CheckDataKeyname
// (src/preprocessor/preprocessor_protect_keynames.cpp). The entity is what the
// list belongs to, so the same name is inside one entity's list and outside
// another's, and a tool holding no list for the entity has none for the name to
// be absent from.
//
// The third is what makes the first matter, and it is observed the way a
// reading observes it: a region sealed under a key is opened again only where
// the pair of names an envelope carries reaches that key.

#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_preprocessor.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

// The entity whose list of keys a name is looked for in, and a second entity
// holding a key of its own under a name the first one does not hold. With one
// entity in the tool's hands a reading that never looked at the entity would
// answer the same as one that did.
constexpr std::string_view kOwner = "acme-semiconductor";
constexpr std::string_view kOtherOwner = "globex-ip";

// The name each of them holds a key under, and the keys those pairs reach.
constexpr std::string_view kOwnerKeyName = "acme-2026";
constexpr std::string_view kOtherKeyName = "globex-2026";
constexpr std::string_view kOwnerKey = "acme-region-exchange-key";
constexpr std::string_view kOtherKey = "globex-region-exchange-key";

// The design a region seals.
constexpr std::string_view kSealedDesign = "module sealed_m; endmodule\n";

// The report a name outside its entity's list draws.
constexpr std::string_view kNoSuchKey =
    "data_keyname names no key held by the data_keyowner in effect";

// A user holding one key of each party, each under its own name.
ProtectKeyList KeysOfBothParties() {
  ProtectKeyList keys;
  keys.Add({std::string(kOwner), std::string(kOwnerKeyName),
            std::string(kOwnerKey)});
  keys.Add({std::string(kOtherOwner), std::string(kOtherKeyName),
            std::string(kOtherKey)});
  return keys;
}

PreprocConfig HoldingBothLists() {
  PreprocConfig config;
  config.protect_keys = KeysOfBothParties();
  return config;
}

// The two directives §34.5.10.1 and §34.5.12.1 designate a key with.
std::string Names(std::string_view owner, std::string_view keyname) {
  std::string text = "`pragma protect data_keyowner=\"";
  text.append(owner).append("\"\n");
  text += "`pragma protect data_keyname=\"";
  text.append(keyname).append("\"\n");
  return text;
}

// One encryption envelope with `described` and then the design between the
// words §34.5.1.1 and §34.5.2.1 define.
std::string Region(const std::string& described) {
  std::string text = "`pragma protect begin\n";
  text.append(described).append(kSealedDesign);
  text += "`pragma protect end\n";
  return text;
}

// §34.5.12.2: it shall be an error to name a key that is not a member of the
// list of keys known for the entity given. The entity here holds one key and
// the region names another, so the name reaches nothing.
TEST(ProtectDataKeynameDescription, ANameOutsideTheEntitysListIsReported) {
  std::string src = Names(kOwner, "a-key-nobody-holds");
  PreprocFixture f;
  Preprocess(src, f, HoldingBothLists());
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoSuchKey,
                            LineHolding(src, "data_keyname"), "34.5.12"));
}

// §34.5.12.2: the list is the one known for the entity given, so a name one
// entity holds a key under is outside another's list. This is the same name
// that passes under its own entity in the case below, so what is reported is
// the pairing rather than the name.
TEST(ProtectDataKeynameDescription, ANameOfAnotherEntitysKeyIsReported) {
  std::string src = Names(kOwner, kOtherKeyName);
  PreprocFixture f;
  Preprocess(src, f, HoldingBothLists());
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoSuchKey,
                            LineHolding(src, "data_keyname"), "34.5.12"));
}

// §34.5.12.2: a name that is a member of the entity's list is what the rule
// admits, so nothing is reported. Without this the two cases above would hold
// of an implementation reporting every name it was given.
TEST(ProtectDataKeynameDescription, ANameInTheEntitysListIsNotReported) {
  PreprocFixture f;
  Preprocess(Names(kOwner, kOwnerKeyName), f, HoldingBothLists());
  EXPECT_FALSE(f.diag.HasErrors());
}

// §34.5.12.2: the same name under the entity that does hold a key by it. The
// two entities and the two names are the same four values as the case that was
// reported, differently paired, so the entity is shown to decide which list the
// name is looked for in.
TEST(ProtectDataKeynameDescription, TheEntityDecidesWhichListTheNameIsIn) {
  PreprocFixture f;
  Preprocess(Names(kOtherOwner, kOtherKeyName), f, HoldingBothLists());
  EXPECT_FALSE(f.diag.HasErrors());
}

// §34.5.12.2: the rule is about a name absent from a list, so a tool holding no
// list for the entity named has none for the name to be absent from and reports
// nothing. A reading that reported here would refuse every name whenever it
// held no keys at all.
TEST(ProtectDataKeynameDescription, AnEntityWithNoListDrawsNoReport) {
  PreprocFixture f;
  Preprocess(Names("a-party-nobody-holds-keys-for", kOwnerKeyName), f,
             HoldingBothLists());
  EXPECT_FALSE(f.diag.HasErrors());
}

// §34.5.12.2: read in a protected envelope, the name is combined with the
// entity to select the single key the data block is decrypted with. The region
// is sealed under the key that pair reaches and the same pair opens it again.
TEST(ProtectDataKeynameDescription, ThePairSelectsTheKeyTheBlockIsOpenedWith) {
  std::string envelope = EncryptEnvelopes(Region(Names(kOwner, kOwnerKeyName)),
                                          "", KeysOfBothParties());
  EXPECT_EQ(envelope.find(kSealedDesign), std::string::npos) << envelope;
  PreprocFixture f;
  std::string read = Preprocess(envelope, f, HoldingBothLists());
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(read.find(kSealedDesign), std::string::npos) << read;
}

// §34.5.12.2: the name is output as cleartext, no digital envelope being in
// use here, so the pair the reading needs stands in the envelope where a reader
// can find it rather than inside the block it opens.
TEST(ProtectDataKeynameDescription, TheNameStandsInTheEnvelopeAsCleartext) {
  std::string envelope = EncryptEnvelopes(Region(Names(kOwner, kOwnerKeyName)),
                                          "", KeysOfBothParties());
  EXPECT_NE(envelope.find(kOwnerKeyName), std::string::npos) << envelope;
}

}  // namespace
