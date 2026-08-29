// §34.5.16 digest_keyowner.
//
// The subclause defines one of the protect pragma keywords §34.4 tabulates,
// and says five things about it.
//
//   Its expression is written with a pragma_value against it, and that value
//   names the legal entity or tool that provided the key a protected region's
//   digest is under. It may name a third party, distinct from whoever wrote
//   the design and from the tool that performed the encryption.
//
//   That value is what selects the key a region's digest block is encrypted
//   under.
//
//   The values written against digest_keyname, digest_decrypt_key and
//   digest_public_key are unique for the entity it names.
//
//   Where an input specifies no entity for the digest, the entity in effect
//   for the digest is whatever the input has in effect for the region's data.
//
//   The name is unchanged in what an encrypting tool writes out, and a tool
//   reading a protected envelope combines it with the name given to one of
//   that entity's keys, or with the public key one of them is, to reach the
//   key that opens the digest block.
//
// All five are preprocessor-stage rules. The value the keyword records, the
// entity that stands where an input named none, and the directive that writes
// the name back out are in src/preprocessor/protect_keywords.cpp; the entity
// paired with the public key one of its keys is lives in
// src/preprocessor/protect_digest_block.cpp; the half that reads an encrypting
// tool's input for the name and carries it onto the envelope is
// src/preprocessor/protect_processing.cpp; the half that writes it into the
// envelope in the clear, and the pairing that picks the key a digest block is
// sealed under, are in src/preprocessor/protect_envelope_output.cpp; and the
// reading side -- holding the three designations to being unique for the
// entity, holding a digest key name to that entity's list, and selecting the
// key a digest block opens with -- is
// src/preprocessor/preprocessor_protect_keys.cpp.
//
// Every input below is written as the real `pragma directive syntax of §22.11.
// The entity the default falls back on is named by §34.5.10's own keyword, the
// design's author by §34.5.5's and the encrypting tool by §34.5.7's, so what
// the default fills a place from and what the entity here is distinct from are
// built the way a source text builds them rather than set up behind the
// reading. Regions are delimited by §34.5.1 and §34.5.2 where a tool's output
// is what is being observed, and by §34.5.3 and §34.5.4 where the input is an
// envelope some other tool wrote.
//
// A sixth claim follows from the spelling §34.5.16.1 gives the expression,
// `digest_keyowner = <string>`. §22.5.1 makes a parenthesized pragma_value a
// list of further expressions rather than one written thing, so a list written
// against the keyword names no entity. The last four cases read what the tool
// wrote rather than what a Preprocessor holds. Issue #3273 is the defect: the
// list was taken as the entity and published on the envelope in the clear.

#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_digest_block.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

// The entity a text names as having provided the key its data are under.
constexpr std::string_view kDataOwner = "acme";

// The third party a text names as having provided the key its digest is under.
// It is neither the design's author nor the tool that does the encrypting,
// which is the arrangement §34.5.16 permits.
constexpr std::string_view kDigestOwner = "veritas-signing";

// The same name spelled as a bare identifier, for the inputs that write the
// value in the other spelling §22.5.1 gives a pragma_value.
constexpr std::string_view kBareDigestOwner = "veritas_signing";

// A second entity, for the inputs that ask what a designation reaches when it
// is read against a list of keys that is not the one it was written under.
constexpr std::string_view kOtherOwner = "globex";

// The name given to one of the digest provider's keys, and the key that name
// reaches.
constexpr std::string_view kDigestKeyName = "digest-2026";
constexpr std::string_view kDigestKey = "veritas-digest-signing-key";

// The public key one of that provider's keys is: the other designation
// §34.5.16 has combined with the entity to reach a single key.
constexpr std::string_view kDigestPublicKey = "veritas-rsa-public-key";

// A name no entity below holds a key under.
constexpr std::string_view kUnheldKeyName = "no-key-of-theirs";

// One value written against two designating names, for the inputs about
// uniqueness. What it is does not matter; that one value stands in two places
// does.
constexpr std::string_view kSharedValue = "one-value-in-two-places";

// The name given to one of the data provider's keys, and the key that name
// reaches. It is a different key of a different party from the digest's, so a
// digest that opened under one of them did not open under the other.
constexpr std::string_view kDataKeyName = "data-2026";
constexpr std::string_view kDataKey = "acme-region-exchange-key";

// A fourth party, named as having provided the key a region's own keys are
// wrapped under, and the name and key that go with it. They build the one
// arrangement §34.5.16's exception is stated for: an envelope carrying its keys
// in blocks of its own.
constexpr std::string_view kKeyProvider = "aegis-custody";
constexpr std::string_view kKeyProviderKeyName = "wrapping-2026";
constexpr std::string_view kKeyProviderKey = "aegis-custody-wrapping-key";

// A pragma_value spelled as a number, which is the third spelling §22.5.1 gives
// one.
constexpr std::string_view kNumericOwner = "1997";

// The design text sealed inside every region below. Nothing of it survives the
// writing of an encrypted block, so finding it in a tool's output is finding a
// region that was never encrypted.
constexpr std::string_view kSealedDesign = "module sealed_m; endmodule\n";

// One protect pragma directive writing `value` against `keyword` as a string,
// which is the spelling §34.5.16.1 defines its own keyword in.
//
// It serves both sides. A source text names an entity with these characters,
// and an encrypting tool required to leave the name unchanged writes the same
// ones back, so what a tool produced is compared against the spelling the
// input was built from rather than against a second spelling of it.
std::string Writes(std::string_view keyword, std::string_view value) {
  std::string text = "`pragma protect ";
  text.append(keyword).append("=\"").append(value).append("\"\n");
  return text;
}

// One encryption envelope: the delimiters of §34.5.1 and §34.5.2 with
// `described` and then `body` between them.
std::string Region(const std::string& described, std::string_view body) {
  std::string text = "`pragma protect begin\n";
  text.append(described).append(body);
  text.append("`pragma protect end\n");
  return text;
}

// A decryption envelope as some other tool wrote it: the delimiters of §34.5.3
// and §34.5.4 with `described` between them.
//
// It is written out here rather than produced, because the expressions an
// envelope of this tool's own making carries always stand in one order, and a
// tool reads envelopes it did not produce. It carries no block, the rules
// observed through it being about which key a digest block would be opened
// with rather than about opening one.
std::string ForeignEnvelope(const std::string& described) {
  std::string text = "`pragma protect begin_protected\n";
  text.append(described);
  text.append("`pragma protect end_protected\n");
  return text;
}

// A user holding one key of `owner`, picked out by `designation`.
ProtectKeyList KeyHeldUnder(std::string_view owner,
                            std::string_view designation,
                            std::string_view key = kDigestKey) {
  ProtectKeyList keys;
  keys.Add({std::string(owner), std::string(designation), std::string(key)});
  return keys;
}

// A user holding the key a region's data are under and, apart from it, the key
// the region's digest names reach. Two keys of two parties, so a block that
// opened under one of them did not open under the other, and which key sealed a
// digest is a thing the reading can tell.
ProtectKeyList KeysForDataAndDigest() {
  ProtectKeyList keys;
  keys.Add({std::string(kDataOwner), std::string(kDataKeyName),
            std::string(kDataKey)});
  keys.Add({std::string(kDigestOwner), std::string(kDigestKeyName),
            std::string(kDigestKey)});
  return keys;
}

// A user holding two keys of one party: the one a region's data name, and the
// one its digest names. One party rather than two, so that an input leaving the
// digest's party unnamed still reaches the second key -- which is what the
// entity standing in the empty place is for, and what tells a reading that
// filled that place from one that left it empty.
ProtectKeyList KeysBothUnderTheDataParty() {
  ProtectKeyList keys;
  keys.Add({std::string(kDataOwner), std::string(kDataKeyName),
            std::string(kDataKey)});
  keys.Add({std::string(kDataOwner), std::string(kDigestKeyName),
            std::string(kDigestKey)});
  return keys;
}

// What a user who supplied `keys` under the names that select them gives the
// tool.
PreprocConfig KeysConfig(const ProtectKeyList& keys) {
  PreprocConfig config;
  config.protect_keys = keys;
  return config;
}

// A reading of `src` by a tool holding `keys`, with the preprocessor kept alive
// afterwards.
//
// What §34.5.16 leaves behind is a pairing rather than output text: which
// entity a digest's designation is read against, and so which of the user's
// keys the digest block is opened with. The pairing belongs to the point the
// reading has reached rather than to any one directive, so it is read off the
// preprocessor once the whole text has passed through, and the diagnostics that
// reading raised are read beside it.
struct ReadUnderKeys {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp;
  std::string text;

  ReadUnderKeys(const std::string& src, const ProtectKeyList& keys)
      : pp(mgr, diag, KeysConfig(keys)) {
    text = pp.Preprocess(mgr.AddFile("<test>", src));
  }

  ProtectKeywordValue ValueOf(std::string_view keyword) const {
    return pp.ProtectKeywords().ValueOf(keyword);
  }

  // The key the entity and the name given to one of its keys reach together.
  std::string_view DigestKey() const { return pp.DigestKeyInEffect(); }

  // The key a digest block is opened with, which is where the designation
  // written as a public key is reached from.
  std::string_view DigestBlockKey() const {
    return pp.DigestBlockKeyInEffect();
  }

  // How the digest block the reading last reached compared against the block it
  // follows. A digest that was sealed under some other key than the one this
  // reading paired the names to reach does not open at all, so this tells a
  // digest encrypted under the key those names select from one encrypted under
  // any other.
  ProtectDigestCheck DigestCheck() const { return pp.LastDigestBlockCheck(); }

  bool Holds(std::string_view needle) const {
    return text.find(needle) != std::string::npos;
  }
};

// The text that stands where the encryption envelopes of `src` were written,
// for an author who supplied keys under the names that select them rather than
// one key of their own. Which key each block of a region is written under is
// then something the region's own names decide.
std::string EncryptedUnderNames(const std::string& src,
                                const ProtectKeyList& keys) {
  return EncryptEnvelopes(src, "", keys);
}

// The expression §34.5.22 makes a request for a digest in what an encrypting
// tool writes out. It stands ahead of the regions below rather than inside
// them, §34.4 making the scope of the request lexical, so the region's own
// lines carry nothing but what it says about its keys.
std::string RequestsDigest() { return "`pragma protect digest_block\n"; }

// The text that stands where the encryption envelopes of `src` were written,
// for an author who supplied one key of their own.
std::string Encrypted(const std::string& src) {
  return EncryptEnvelopes(src, kDataKey);
}

// How many times `needle` is written in `text`.
size_t Occurrences(std::string_view text, std::string_view needle) {
  size_t count = 0;
  size_t pos = text.find(needle);
  while (pos != std::string_view::npos) {
    ++count;
    pos = text.find(needle, pos + needle.size());
  }
  return count;
}

// ---------------------------------------------------------------------------
// The value written against the keyword names the entity.
// ---------------------------------------------------------------------------

// The spelling §34.5.16.1 defines: a string written against the keyword. What
// stands in effect afterwards is that string, and it is there because a
// directive put it there rather than because a default did.
TEST(ProtectDigestKeyownerExpression,
     TheStringAgainstTheKeywordNamesTheEntity) {
  ReadUnderKeys run(Writes("digest_keyowner", kDigestOwner), ProtectKeyList());
  EXPECT_FALSE(run.ValueOf("digest_keyowner").defaulted);
  EXPECT_EQ(run.ValueOf("digest_keyowner").value, kDigestOwner);
}

// §22.5.1 gives a pragma_value more than one spelling, and a keyword recording
// a string is not thereby barred from being written with an identifier against
// it. The entity a bare identifier names is the identifier itself, no quotation
// marks having been written for anything to strip.
TEST(ProtectDigestKeyownerExpression, ABareIdentifierNamesTheEntityItSpells) {
  ReadUnderKeys run("`pragma protect digest_keyowner=veritas_signing\n",
                    ProtectKeyList());
  EXPECT_FALSE(run.ValueOf("digest_keyowner").defaulted);
  EXPECT_EQ(run.ValueOf("digest_keyowner").value, kBareDigestOwner);
}

// The keyword written on a directive of its own and the same keyword written
// as one expression of a list leave the same entity in effect. §22.11 admits
// both, and §34.4 puts a value in effect from where it was written either way.
TEST(ProtectDigestKeyownerExpression, TheKeywordStandsInAListOfExpressions) {
  ReadUnderKeys run(
      "`pragma protect data_method=\"des-cbc\", digest_keyowner=\"acme\"\n",
      ProtectKeyList());
  EXPECT_FALSE(run.ValueOf("digest_keyowner").defaulted);
  EXPECT_EQ(run.ValueOf("digest_keyowner").value, kDataOwner);
}

// The third spelling. A number is a pragma_value like the other two, and what
// the keyword records is the value written against it rather than the shape
// that value happened to take, so a party named by a number is named.
TEST(ProtectDigestKeyownerExpression, ANumberIsAValueLikeTheOtherTwo) {
  ReadUnderKeys run("`pragma protect digest_keyowner=1997\n", ProtectKeyList());
  EXPECT_FALSE(run.ValueOf("digest_keyowner").defaulted);
  EXPECT_EQ(run.ValueOf("digest_keyowner").value, kNumericOwner);
}

// The negative: the entity is named by this keyword and by no name near it. A
// text one letter off the keyword has named no party for its digest, so what
// stands is the default rather than the party that near-miss line spells, and
// the digest is read under the entity the data name.
TEST(ProtectDigestKeyownerExpression, ANameOneLetterOffNamesNoEntity) {
  std::string src = Writes("data_keyowner", kDataOwner);
  src += Writes("digest_keyownr", kOtherOwner);
  src += Writes("digest_keyname", kDigestKeyName);
  ReadUnderKeys run(src, KeyHeldUnder(kDataOwner, kDigestKeyName));
  EXPECT_TRUE(run.ValueOf("digest_keyowner").defaulted);
  EXPECT_EQ(run.DigestKey(), kDigestKey);
}

// ---------------------------------------------------------------------------
// An input naming no entity for its digest is read under the one it named for
// its data.
// ---------------------------------------------------------------------------

// The text names an entity for its data and a key for its digest, and nothing
// at all for whose key that is. The name of the digest's key is a member of one
// entity's list and reaches nothing outside it, so the key it reaches here is
// reached by the entity the data named standing in the place the digest left
// empty.
TEST(ProtectDigestKeyownerDefault,
     TheDataProviderStandsWhereTheDigestNamedNone) {
  std::string src = Writes("data_keyowner", kDataOwner);
  src += Writes("digest_keyname", kDigestKeyName);
  ReadUnderKeys run(src, KeyHeldUnder(kDataOwner, kDigestKeyName));
  EXPECT_EQ(run.DigestKey(), kDigestKey);
}

// The negative: the same text with an entity of the digest's own written into
// it. A specified entity stands on its own, so the name of the digest's key is
// read against that entity's list rather than against the data provider's, and
// a tool holding none of that entity's keys reaches no key at all.
TEST(ProtectDigestKeyownerDefault,
     ANamedEntityIsNotDisplacedByTheDataProvider) {
  std::string src = Writes("data_keyowner", kDataOwner);
  src += Writes("digest_keyowner", kOtherOwner);
  src += Writes("digest_keyname", kDigestKeyName);
  ReadUnderKeys run(src, KeyHeldUnder(kDataOwner, kDigestKeyName));
  EXPECT_TRUE(run.DigestKey().empty());
}

// The keyword written with nothing against it specified no entity, so the
// default fills the place exactly as leaving the keyword out did. What decides
// between the two is whether an entity was named rather than whether the
// keyword was mentioned.
TEST(ProtectDigestKeyownerDefault,
     TheKeywordWithNothingAgainstItNamesNoEntity) {
  std::string src = Writes("data_keyowner", kDataOwner);
  src += "`pragma protect digest_keyowner\n";
  src += Writes("digest_keyname", kDigestKeyName);
  ReadUnderKeys run(src, KeyHeldUnder(kDataOwner, kDigestKeyName));
  EXPECT_EQ(run.DigestKey(), kDigestKey);
}

// What fills the place is the value the data's entity has where the reading
// stands, §34.4 making the scope of both names lexical. A text that named one
// provider for its data and then named another has the second in effect, so the
// digest is read against the second.
TEST(ProtectDigestKeyownerDefault, TheEntityFilledInIsTheOneCurrentlyInEffect) {
  std::string src = Writes("data_keyowner", kOtherOwner);
  src += Writes("data_keyowner", kDataOwner);
  src += Writes("digest_keyname", kDigestKeyName);
  ReadUnderKeys run(src, KeyHeldUnder(kDataOwner, kDigestKeyName));
  EXPECT_EQ(run.DigestKey(), kDigestKey);
}

// The negative of the default: a text naming no entity for its digest and none
// for its data has nothing for the default to fill the place from, so the name
// of the digest's key is read against no list at all and reaches no key. What
// fills the place is the other name's value, not any entity holding the key
// that name happens to spell.
TEST(ProtectDigestKeyownerDefault, WithNeitherNameWrittenNoEntityStands) {
  ReadUnderKeys run(Writes("digest_keyname", kDigestKeyName),
                    KeyHeldUnder(kDataOwner, kDigestKeyName));
  EXPECT_TRUE(run.ValueOf("digest_keyowner").defaulted);
  EXPECT_TRUE(run.DigestKey().empty());
}

// The entity the default supplies is the one a digest key name is held against,
// so a name that is not a member of that entity's list picks out nothing and is
// reported. Nothing in this text names an entity for the digest, so the list
// the name was measured against is the data provider's.
TEST(ProtectDigestKeynameUnderDefaultedEntity, ANameOutsideThatListIsReported) {
  std::string src = Writes("data_keyowner", kDataOwner);
  src += Writes("digest_keyname", kUnheldKeyName);
  ReadUnderKeys run(src, KeyHeldUnder(kDataOwner, kDigestKeyName));
  // §34.5.18 is where the standard puts the name, so that is the rule the
  // report enforces even where the entity it is measured against is this
  // subclause's.
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(),
                            "protect pragma digest_keyname names no key held "
                            "by the digest_keyowner in effect",
                            2, "34.5.18"));
}

// ---------------------------------------------------------------------------
// The three designations are unique for the entity named.
// ---------------------------------------------------------------------------

// One value written under a single entity against two of the three names that
// designate one of its keys would have to pick out two of that entity's keys at
// once, so it picks out neither and is reported.
TEST(ProtectDigestDesignationUniqueness, OneValueAgainstTwoNamesIsReported) {
  std::string src = Writes("digest_keyowner", kDigestOwner);
  src += Writes("digest_keyname", kSharedValue);
  src += Writes("digest_public_key", kSharedValue);
  ReadUnderKeys run(src, ProtectKeyList());
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma writes one value against two of the names that "
      "designate a key of the digest_keyowner in effect",
      3, "34.5.16"));
}

// The session key for the digest is the third of the three names, so a value it
// shares with either of the others under one entity is the same repetition.
TEST(ProtectDigestDesignationUniqueness, TheSessionKeyIsHeldToTheSameRule) {
  std::string src = Writes("digest_keyowner", kDigestOwner);
  src += Writes("digest_keyname", kSharedValue);
  src += Writes("digest_decrypt_key", kSharedValue);
  ReadUnderKeys run(src, ProtectKeyList());
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma writes one value against two of the names that "
      "designate a key of the digest_keyowner in effect",
      3, "34.5.16"));
}

// The entity is what the values are unique for. Written under two entities the
// same value is two designations rather than one repeated, each being read
// against a different list of keys, so it stands.
TEST(ProtectDigestDesignationUniqueness, TwoEntitiesMakeTwoDesignations) {
  std::string src = Writes("digest_keyowner", kDigestOwner);
  src += Writes("digest_keyname", kSharedValue);
  src += Writes("digest_keyowner", kOtherOwner);
  src += Writes("digest_public_key", kSharedValue);
  ReadUnderKeys run(src, ProtectKeyList());
  EXPECT_FALSE(run.diag.HasErrors());
}

// A keyword written again with the value it already had designates the one key
// it designated before. The requirement is on one value reaching two of the
// three names, not on a name being written twice.
TEST(ProtectDigestDesignationUniqueness, ANameRewrittenWithItsOwnValueStands) {
  std::string src = Writes("digest_keyowner", kDigestOwner);
  src += Writes("digest_keyname", kSharedValue);
  src += Writes("digest_keyname", kSharedValue);
  ReadUnderKeys run(src, ProtectKeyList());
  EXPECT_FALSE(run.diag.HasErrors());
}

// The entity the requirement is measured against is the specified one, and an
// input that specified none for its digest specified the one its data name. So
// two designations written across a change of that name are written under two
// entities and repeat nothing, though neither line mentions the digest's
// provider at all.
TEST(ProtectDigestDesignationUniqueness,
     TheDefaultedEntityIsWhatTheyAreUniqueFor) {
  std::string src = Writes("data_keyowner", kDataOwner);
  src += Writes("digest_keyname", kSharedValue);
  src += Writes("data_keyowner", kOtherOwner);
  src += Writes("digest_public_key", kSharedValue);
  ReadUnderKeys run(src, ProtectKeyList());
  EXPECT_FALSE(run.diag.HasErrors());
}

// The pair to it: one data provider standing over both lines leaves both
// designations under one entity, and one value picking out two of that entity's
// keys is reported.
TEST(ProtectDigestDesignationUniqueness, OneDefaultedEntityMakesOneRepetition) {
  std::string src = Writes("data_keyowner", kDataOwner);
  src += Writes("digest_keyname", kSharedValue);
  src += Writes("digest_public_key", kSharedValue);
  ReadUnderKeys run(src, ProtectKeyList());
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma writes one value against two of the names that "
      "designate a key of the digest_keyowner in effect",
      3, "34.5.16"));
}

// The third pair the three names make between them. The requirement ranges over
// all three at once, so the two that are not the name given to a key are held
// to it in the same way as any other pair.
TEST(ProtectDigestDesignationUniqueness, TheSessionKeyAndThePublicKeyPairToo) {
  std::string src = Writes("digest_keyowner", kDigestOwner);
  src += Writes("digest_decrypt_key", kSharedValue);
  src += Writes("digest_public_key", kSharedValue);
  ReadUnderKeys run(src, ProtectKeyList());
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma writes one value against two of the names that "
      "designate a key of the digest_keyowner in effect",
      3, "34.5.16"));
}

// The three names §34.5.16 ranges over are the digest's own. A value shared
// with a name written for the region's data is no repetition here: §34.5.18
// has a digest whose key is the data's key say so by saying nothing, so the two
// names carrying one value is what such a text spells out.
TEST(ProtectDigestDesignationUniqueness, ADataNameIsOutsideTheThree) {
  std::string src = Writes("data_keyowner", kDataOwner);
  src += Writes("data_keyname", kSharedValue);
  src += Writes("digest_keyname", kSharedValue);
  ReadUnderKeys run(src, ProtectKeyList());
  EXPECT_FALSE(run.diag.HasErrors());
}

// ---------------------------------------------------------------------------
// The name is unchanged in what an encrypting tool writes out.
// ---------------------------------------------------------------------------

// A region that named the provider of its digest's key has that name written
// into the envelope standing in its place, in the clear and ahead of the block.
// The design it was formed from is gone, so the text holding the name is an
// envelope rather than a region that was never encrypted.
TEST(ProtectDigestKeyownerEncryptionOutput, TheNameIsWrittenIntoTheEnvelope) {
  std::string described = Writes("digest_keyowner", kDigestOwner);
  std::string encrypted = Encrypted(Region(described, kSealedDesign));
  EXPECT_EQ(encrypted.find(kSealedDesign), std::string::npos);
  EXPECT_NE(encrypted.find(described), std::string::npos);
}

// Unchanged is meant of the value. A name written as a bare identifier comes
// back a bare identifier: returned in quotation marks it would be a different
// pragma_value from the one the author wrote, whatever it still denotes.
TEST(ProtectDigestKeyownerEncryptionOutput,
     TheSpellingComesBackAsItWasWritten) {
  std::string described = "`pragma protect digest_keyowner=veritas_signing\n";
  std::string encrypted = Encrypted(Region(described, kSealedDesign));
  EXPECT_NE(encrypted.find(described), std::string::npos);
  EXPECT_EQ(encrypted.find("digest_keyowner=\""), std::string::npos);
}

// The negative: a region that named no provider for its digest has none named
// for it. A tool writing one there would be stating an entity the input never
// specified, and a reader would then combine a key name with a party the author
// never named.
TEST(ProtectDigestKeyownerEncryptionOutput, ARegionThatNamedNoneGetsNone) {
  std::string encrypted = Encrypted(Region(std::string(), kSealedDesign));
  EXPECT_EQ(encrypted.find(kSealedDesign), std::string::npos);
  EXPECT_EQ(encrypted.find("digest_keyowner"), std::string::npos);
}

// A directive standing ahead of a region is outside the envelope, and the
// characters outside an envelope come back exactly as they were written. So the
// name appears once in what the tool wrote: once where the input put it, and
// nowhere else.
TEST(ProtectDigestKeyownerEncryptionOutput, ANameAheadOfTheRegionIsCopiedOnce) {
  std::string named = Writes("digest_keyowner", kDigestOwner);
  std::string encrypted =
      Encrypted(named + Region(std::string(), kSealedDesign));
  EXPECT_EQ(encrypted.find(kSealedDesign), std::string::npos);
  EXPECT_EQ(Occurrences(encrypted, named), 1U);
}

// A region naming the provider of its digest's key and the name of that key
// has both written out unchanged, the provider ahead of the name read against
// it, and both ahead of the block. That is what leaves a reader able to pair
// them: a name is a member of one entity's list, so learning it after the block
// it is needed for would be learning it too late.
TEST(ProtectDigestKeyownerEncryptionOutput,
     TheEntityStandsAheadOfTheNameAndTheBlock) {
  std::string described = Writes("digest_keyowner", kDigestOwner);
  described += Writes("digest_keyname", kDigestKeyName);
  std::string encrypted = Encrypted(Region(described, kSealedDesign));
  EXPECT_NE(encrypted.find(described), std::string::npos);
  EXPECT_LT(encrypted.find(described), encrypted.find("data_block"));
}

// The one arrangement the subclause makes an exception of: an envelope carrying
// its own keys in blocks, which is where a digital signature puts them.
// §34.5.16 sends the entity's name into a block holding the digest's key there,
// and this implementation writes no such block, so the exception has nowhere to
// send the name and it stays in the clear. A name sealed inside instead would
// have to be read out from behind the very digest it says whose key opens.
TEST(ProtectDigestKeyownerEncryptionOutput, AnEnvelopeCarryingKeysStatesItToo) {
  std::string described = Writes("key_keyowner", kKeyProvider);
  described += Writes("key_keyname", kKeyProviderKeyName);
  std::string named = Writes("digest_keyowner", kDigestOwner);
  std::string encrypted = EncryptedUnderNames(
      Region(described + named, kSealedDesign),
      KeyHeldUnder(kKeyProvider, kKeyProviderKeyName, kKeyProviderKey));
  EXPECT_EQ(encrypted.find(kSealedDesign), std::string::npos);
  EXPECT_NE(encrypted.find("`pragma protect key_block"), std::string::npos);
  EXPECT_NE(encrypted.find(named), std::string::npos);
}

// ---------------------------------------------------------------------------
// A reader combines the entity with a designation of one of its keys.
// ---------------------------------------------------------------------------

// The entity and the name given to one of its keys reach one key together.
// Neither reaches it alone: a key name is a member of one entity's list and
// says nothing outside it.
TEST(ProtectDigestKeyownerDecryptionInput, TheEntityAndTheKeyNameReachOneKey) {
  std::string described = Writes("digest_keyowner", kDigestOwner);
  described += Writes("digest_keyname", kDigestKeyName);
  ReadUnderKeys run(ForeignEnvelope(described),
                    KeyHeldUnder(kDigestOwner, kDigestKeyName));
  EXPECT_EQ(run.DigestKey(), kDigestKey);
}

// The negative: the same key name written under another entity. The list it is
// read against is the one the entity beside it names, so a name belonging to
// one party's list reaches nothing when it is read under a different party.
TEST(ProtectDigestKeyownerDecryptionInput,
     ThatNameUnderAnotherEntityReachesNone) {
  std::string described = Writes("digest_keyowner", kOtherOwner);
  described += Writes("digest_keyname", kDigestKeyName);
  ReadUnderKeys run(ForeignEnvelope(described),
                    KeyHeldUnder(kDigestOwner, kDigestKeyName));
  EXPECT_TRUE(run.DigestKey().empty());
}

// The public key one of that entity's keys is is the other designation the
// entity is combined with, and it reaches the key a digest block is opened
// with. It is an alternative to the name given to the key rather than a
// companion of it, so this text designates its key as fully as one writing the
// name did.
TEST(ProtectDigestKeyownerDecryptionInput,
     TheEntityAndThePublicKeyReachOneKey) {
  std::string described = Writes("digest_keyowner", kDigestOwner);
  described += Writes("digest_public_key", kDigestPublicKey);
  ReadUnderKeys run(ForeignEnvelope(described),
                    KeyHeldUnder(kDigestOwner, kDigestPublicKey));
  EXPECT_EQ(run.DigestBlockKey(), kDigestKey);
}

// That route is read against the entity in effect just as the other one is, so
// an envelope naming a provider for its data and designating its digest's key
// by a public key reaches the key the two select together.
TEST(ProtectDigestKeyownerDecryptionInput,
     ThePublicKeyRouteTakesTheDefaultToo) {
  std::string described = Writes("data_keyowner", kDataOwner);
  described += Writes("digest_public_key", kDigestPublicKey);
  ReadUnderKeys run(ForeignEnvelope(described),
                    KeyHeldUnder(kDataOwner, kDigestPublicKey));
  EXPECT_EQ(run.DigestBlockKey(), kDigestKey);
}

// The negative for the other route, matching the one the key name has: a public
// key is a member of one entity's list too, so read under a party that never
// held it the designation reaches nothing and the digest block has no key.
TEST(ProtectDigestKeyownerDecryptionInput,
     ThatPublicKeyUnderAnotherEntityReachesNone) {
  std::string described = Writes("digest_keyowner", kOtherOwner);
  described += Writes("digest_public_key", kDigestPublicKey);
  ReadUnderKeys run(ForeignEnvelope(described),
                    KeyHeldUnder(kDigestOwner, kDigestPublicKey));
  EXPECT_TRUE(run.DigestBlockKey().empty());
}

// A party the tool holds keys for, under a name that is not among them, is a
// different state from a party it holds none for. There is a list to measure
// the name against here, and the name is missing from it, so the miss is
// reported rather than passed over as it is where no list was supplied at all.
TEST(ProtectDigestKeyownerDecryptionInput,
     ANameMissingFromThatEntitysListIsReported) {
  std::string described = Writes("digest_keyowner", kDigestOwner);
  described += Writes("digest_keyname", kUnheldKeyName);
  ReadUnderKeys run(ForeignEnvelope(described),
                    KeyHeldUnder(kDigestOwner, kDigestKeyName));
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(),
                            "protect pragma digest_keyname names no key held "
                            "by the digest_keyowner in effect",
                            3, "34.5.18"));
  EXPECT_TRUE(run.DigestKey().empty());
}

// The entity may be a third party. This envelope names the design's author
// with §34.5.5's keyword and the encrypting tool with §34.5.7's, and names
// neither of them as the provider of the key its digest is under: the key is
// reached from the party the digest names, and the two other names decide
// nothing about it.
TEST(ProtectDigestKeyownerDecryptionInput,
     TheEntityNeedBeNeitherOfTheOtherTwo) {
  std::string described = Writes("author", kDataOwner);
  described += Writes("encrypt_agent", kOtherOwner);
  described += Writes("digest_keyowner", kDigestOwner);
  described += Writes("digest_keyname", kDigestKeyName);
  ReadUnderKeys run(ForeignEnvelope(described),
                    KeyHeldUnder(kDigestOwner, kDigestKeyName));
  EXPECT_EQ(run.DigestKey(), kDigestKey);
}

// ---------------------------------------------------------------------------
// The entity is what selects the key the digest block is encrypted with.
// ---------------------------------------------------------------------------

// The whole round trip, through both halves of the tool. A region asks for a
// digest, names one party for the key its data are under and another for the
// key its digest is under, and is put through envelope encryption; the envelope
// that comes back is read by a tool holding both parties' keys.
//
// The digest opens and agrees with the block it follows. It could only open
// under the key the digest's own names select, that key being neither the one
// the data are under nor anything derived from it, so the tool that sealed the
// digest selected it by the party the region named for it.
TEST(ProtectDigestKeyownerEncryptionInput, TheEntityNamedSelectsTheDigestKey) {
  std::string described = Writes("data_keyowner", kDataOwner);
  described += Writes("data_keyname", kDataKeyName);
  described += Writes("digest_keyowner", kDigestOwner);
  described += Writes("digest_keyname", kDigestKeyName);
  std::string encrypted =
      EncryptedUnderNames(RequestsDigest() + Region(described, kSealedDesign),
                          KeysForDataAndDigest());
  ReadUnderKeys run(encrypted, KeysForDataAndDigest());
  EXPECT_TRUE(run.Holds("module sealed_m"));
  EXPECT_EQ(run.DigestCheck(), ProtectDigestCheck::kMatched);
}

// The same input with the digest naming no party of its own. There is nothing
// for the entity to select with, so the digest stays under the key the region's
// data are under, which is where the subclauses defining those two names leave
// a region that named neither. The digest still opens, under the other key.
TEST(ProtectDigestKeyownerEncryptionInput, ARegionNamingNoneKeepsTheDataKey) {
  std::string described = Writes("data_keyowner", kDataOwner);
  described += Writes("data_keyname", kDataKeyName);
  std::string encrypted =
      EncryptedUnderNames(RequestsDigest() + Region(described, kSealedDesign),
                          KeysForDataAndDigest());
  ReadUnderKeys run(encrypted, KeysForDataAndDigest());
  EXPECT_TRUE(run.Holds("module sealed_m"));
  EXPECT_EQ(run.DigestCheck(), ProtectDigestCheck::kMatched);
}

// The keyword carrying an empty string named no party, exactly as writing it
// with nothing against it did, so the party the data name fills the place. The
// user here holds a key of that party under the digest's key name, so filling
// the place reaches a key and leaving it empty reaches none: the digest is
// sealed under the key the two names select, and the envelope sends its reader
// to that same key.
//
// Both halves of the tool have to judge the emptiness of the value rather than
// of the expression carrying it for that to hold. Judged apart, one half would
// seal the digest under a key the other never looks for, and the round trip
// below would come back with a digest that does not open.
TEST(ProtectDigestKeyownerEncryptionInput, AnEmptyStringNamesNoPartyEither) {
  std::string described = Writes("data_keyowner", kDataOwner);
  described += Writes("data_keyname", kDataKeyName);
  described += Writes("digest_keyowner", "");
  described += Writes("digest_keyname", kDigestKeyName);
  std::string encrypted =
      EncryptedUnderNames(RequestsDigest() + Region(described, kSealedDesign),
                          KeysBothUnderTheDataParty());
  ReadUnderKeys run(encrypted, KeysBothUnderTheDataParty());
  EXPECT_TRUE(run.Holds("module sealed_m"));
  EXPECT_EQ(run.DigestCheck(), ProtectDigestCheck::kMatched);
}

// The negative: a region naming a party the tool holds no key of. The entity
// selects nothing then -- a name reaches a key only through a list, and there
// is no list for this party -- so the selection falls through to the key the
// data are under rather than leaving the digest sealed under nothing, and a
// reader pairing the same names falls through to the same place.
TEST(ProtectDigestKeyownerEncryptionInput, AnEntityWithNoKeysSelectsNothing) {
  std::string described = Writes("data_keyowner", kDataOwner);
  described += Writes("data_keyname", kDataKeyName);
  described += Writes("digest_keyowner", kOtherOwner);
  described += Writes("digest_keyname", kDigestKeyName);
  std::string encrypted =
      EncryptedUnderNames(RequestsDigest() + Region(described, kSealedDesign),
                          KeysForDataAndDigest());
  ReadUnderKeys run(encrypted, KeysForDataAndDigest());
  EXPECT_TRUE(run.Holds("module sealed_m"));
  EXPECT_EQ(run.DigestCheck(), ProtectDigestCheck::kMatched);
}

// §34.5.16.2 makes the three designations unique for the entity however they
// are spelled, and two of them are not spelled with a value against the
// keyword: §34.5.19.1 and §34.5.20.1 write the keyword standing alone with the
// encoded value on the line beneath it, which the cases above never reach. Such
// a line is read only inside a protected envelope, so these two build one.

// The two lines a designation is spelled over when the value stands beneath the
// keyword.
std::string Announces(std::string_view keyword, std::string_view value) {
  std::string text = "`pragma protect ";
  text.append(keyword).append("\n");
  text.append(EncodeProtectBlock(value, DefaultProtectEncoding())).append("\n");
  return text;
}

// §34.5.16.2: the public key announced on the line beneath its keyword is one
// of the three, so a value it shares with the name written beside it under one
// entity is the repetition the subclause forbids. A rule reading only the value
// written against a keyword never sees this spelling.
TEST(ProtectDigestDesignationUniqueness, AnAnnouncedPublicKeyIsHeldToTheRule) {
  std::string described = Writes("digest_keyowner", kDigestOwner);
  described += Writes("digest_keyname", kSharedValue);
  described += Announces("digest_public_key", kSharedValue);
  std::string src = ForeignEnvelope(described);
  ReadUnderKeys run(src, ProtectKeyList());
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma writes one value against two of the names that "
      "designate a key of the digest_keyowner in effect",
      LineHolding(src, EncodeProtectBlock(std::string(kSharedValue),
                                          DefaultProtectEncoding())),
      "34.5.16"));
}

// §34.5.16.2: the same of the session key, which §34.5.20.1 spells the same way
// and which reaches the rule by its own path.
TEST(ProtectDigestDesignationUniqueness, AnAnnouncedSessionKeyIsHeldToTheRule) {
  std::string described = Writes("digest_keyowner", kDigestOwner);
  described += Writes("digest_keyname", kSharedValue);
  described += Announces("digest_decrypt_key", kSharedValue);
  std::string src = ForeignEnvelope(described);
  ReadUnderKeys run(src, ProtectKeyList());
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      "protect pragma writes one value against two of the names that "
      "designate a key of the digest_keyowner in effect",
      LineHolding(src, EncodeProtectBlock(std::string(kSharedValue),
                                          DefaultProtectEncoding())),
      "34.5.16"));
}

// ---------------------------------------------------------------------------
// A parenthesized list against the keyword names no entity.
// ---------------------------------------------------------------------------

// The parenthesized pragma_value §22.5.1 defines: expressions between
// parentheses rather than the one written thing §34.5.16.1 spells.
constexpr std::string_view kEntityList = "(division=\"notary\", desk=\"emea\")";

// The characters an envelope writes this keyword's directive with. §34.5.16.2
// has the name unchanged, so a list taken as the value goes out between its own
// parentheses rather than in quotation marks, and these characters are what a
// case asking whether the envelope names an entity at all searches for.
constexpr std::string_view kEntityDirectiveHead = "digest_keyowner=";

// One protect pragma directive writing `value` against `keyword` exactly as
// given, so a parenthesized list reaches the reading as the list §22.5.1
// defines rather than as a string that happens to hold parentheses.
std::string WritesUnquoted(std::string_view keyword, std::string_view value) {
  std::string text = "`pragma protect ";
  text.append(keyword).append("=").append(value).append("\n");
  return text;
}

// §34.5.16.1 spells the expression `digest_keyowner = <string>`, so a list
// names no entity. §34.5.16.2 leaves this name in the clear whatever blocks the
// envelope carries -- issue #3429 settled that the digest_key_block its
// exception names is defined nowhere -- so a tool taking the list publishes it
// as the entity. Issue #3273 is that defect.
TEST(ProtectDigestKeyownerEncryptionOutput, AListPutsNoEntityIntoTheEnvelope) {
  std::string encrypted = Encrypted(
      Region(WritesUnquoted("digest_keyowner", kEntityList), kSealedDesign));
  EXPECT_EQ(encrypted.find(kSealedDesign), std::string::npos);
  EXPECT_EQ(Occurrences(encrypted, kEntityDirectiveHead), 0U);
}

// The same region with the string §34.5.16.1 defines standing where the list
// stood. The entity reaches the envelope, so the case above is about the list
// rather than about a tool that writes no entity at all.
TEST(ProtectDigestKeyownerEncryptionOutput,
     AStringPutsItsEntityIntoTheEnvelope) {
  std::string named = Writes("digest_keyowner", kDigestOwner);
  std::string encrypted = Encrypted(Region(named, kSealedDesign));
  EXPECT_EQ(encrypted.find(kSealedDesign), std::string::npos);
  EXPECT_EQ(Occurrences(encrypted, named), 1U);
}

// A list written after a string had already named the entity. Naming no entity
// is not naming an empty one, so the envelope carries the earlier string's
// name: an expression naming nothing takes no name away.
TEST(ProtectDigestKeyownerEncryptionOutput,
     AListLeavesTheEntityTheEnvelopeCarriesStanding) {
  std::string described = Writes("digest_keyowner", kDigestOwner);
  described += WritesUnquoted("digest_keyowner", kEntityList);
  std::string encrypted = Encrypted(Region(described, kSealedDesign));
  EXPECT_EQ(encrypted.find(kSealedDesign), std::string::npos);
  EXPECT_EQ(Occurrences(encrypted, kEntityDirectiveHead), 1U);
  EXPECT_NE(encrypted.find(Writes("digest_keyowner", kDigestOwner)),
            std::string::npos);
}

// §34.5.16 has the entity in effect for a region's data stand where the digest
// named none, and a list names none, so a region writing a list has its digest
// sealed under the key that default reaches. No case here claims that, and the
// reason is worth recording: the key a digest was sealed under is stated
// nowhere a reader can read, the block being encrypted and then encoded, and
// the two envelopes that would be compared instead cannot be equal. A protect
// pragma directive a region writes travels into the data block along with the
// design -- only §34.5.5's author, §34.5.6's author_info and §34.5.30's comment
// are held out of it, in ClosedRegionText
// (src/preprocessor/protect_processing.cpp) -- so a region carrying one more
// directive than another produces a longer block whatever the directive said.
// ProtectDigestKeyownerSyntax.AListNamesNoEntityAndLeavesTheDefault in
// test_preprocessor_subclause_34_05_16_01.cpp makes the claim on the reading
// side, where the entity in effect can be read back.

}  // namespace
