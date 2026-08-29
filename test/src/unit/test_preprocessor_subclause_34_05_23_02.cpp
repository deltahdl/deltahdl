// §34.5.23 key_keyowner, Description.
//
// §34.5.23.2 says four things about the keyword §34.5.23.1 spells.
//
//   The value names the legal entity or tool that provided the keys used for
//   encrypting and decrypting the key information -- the keys a region's own
//   keys travel under, rather than the keys its data are under.
//
//   The value has the same constraints §34.5.10.2 states for the entity whose
//   keys the data are under.
//
//   It is unchanged in the output file. No exception is stated, where the
//   entity of the data, the entity of the digest and the cipher of the digest's
//   key each have one for a digital signature.
//
//   On the way back it is combined with key_keyname or key_public_key to reach
//   the secret or private key that decrypts the key block.
//
// The first is a definition rather than a rule a run can be held to: the value
// is a name selecting a list of keys, and nothing decides whether the name
// denotes a company or a program. The other three are what this file states.
//
// Which spelling of the expression puts which value in effect is §34.5.23.1's
// and is stated in test_preprocessor_subclause_34_05_23_01.cpp, along with the
// two cases asking which key an entity reaches through ProtectKeyBlockKey. What
// is left here is the constraint the value is held to, the spelling it goes out
// in, and the block a reader opens with it.
//
// §34.5.10.2 states the constraint this subclause borrows: the values
// designating a key "shall be unique for the specified" entity. The data have
// three such names and this family has two, §34.4 tabulating no session key for
// it, so where CheckDataKeyDesignationValue in
// src/preprocessor/preprocessor_protect_keynames.cpp reports two of three,
// Preprocessor::CheckKeyBlockDesignation in
// src/preprocessor/preprocessor_protect_keys.cpp reports both of two, and it
// cites §34.5.23 rather than the subclause the constraint was borrowed from.
//
// The last three cases below state what an encrypting run writes for a region
// that named its entity with a parenthesized list. §34.5.23.1 spells the
// expression key_keyowner = <string>, and §22.5.1 makes a parenthesized
// pragma_value a list of further pragma expressions rather than the one written
// thing a string is, so a list names no entity. An envelope therefore carries
// no key_keyowner directive at all where the region wrote only a list, and
// carries the string where one stood before the list. #3273 is the defect they
// close: the list was taken as the value and published on the envelope, where a
// reader pairing it with key_keyname reaches no key of anybody's.
//
// These read the text the tool wrote rather than the value a Preprocessor
// holds. ProtectKeywordScope::Apply in src/preprocessor/protect_keywords.cpp
// already refuses a list, so a case reading the value back off a reading passes
// whatever the writing side does; the cases in
// test_preprocessor_subclause_34_05_23_01.cpp are of that kind.

#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_protect_keys.h"
#include "helpers_reported_error.h"
#include "helpers_text_lines.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

// The entity a region names, spelled the way an identifier is. §34.5.23.2 has
// the value unchanged in what the tool writes out, and a value written bare is
// the one spelling that says so: a name already in quotation marks comes back
// in quotation marks whether the rule was kept or not.
constexpr std::string_view kEntity = "acme_semiconductor";

// A second entity, for the case asking whether the constraint is about the
// characters or about the entity they are unique for.
constexpr std::string_view kOtherEntity = "globex_industries";

// One value written against two of the names that designate a key, and a second
// value for the case that writes a different one against each.
constexpr std::string_view kSharedValue = "one-value-in-two-places";
constexpr std::string_view kOtherValue = "a-value-of-its-own";

// The name picking the key out of the entity's list, and the key itself.
constexpr std::string_view kKeyName = "wrapping-2027";
constexpr std::string_view kEntityKey = "acme-wrapping-key";

// The key an author hands the encrypting half where no key block is asked for.
constexpr std::string_view kAuthorsKey = "one-key-of-the-authors-own";

// A pragma_value written in the parenthesized spelling §22.5.1 defines, which
// is a list of further pragma expressions rather than the one written thing
// §34.5.23.1 writes against this keyword. Its subkeywords are names §34.4
// tabulates nowhere, so what the list says is beside the point and its spelling
// is the whole of what the cases below read.
constexpr std::string_view kEntityList =
    "(chartered_in=\"delaware\", registry=\"dun-and-bradstreet\")";

// The design a region seals.
constexpr std::string_view kSealedDesign = "module sealed_m; endmodule\n";

// The entity written bare, which is the spelling every case here writes it in.
std::string NamesEntity(std::string_view entity) {
  std::string text = "`pragma protect key_keyowner=";
  text.append(entity).append("\n");
  return text;
}

std::string Writes(std::string_view keyword, std::string_view value) {
  std::string text = "`pragma protect ";
  text.append(keyword).append("=\"").append(value).append("\"\n");
  return text;
}

// `value` written under the coding scheme a text that stated none is read in.
// The line beneath an announcing keyword carries the value encoded, and a line
// that cannot be read out of that scheme designates nothing at all, so a case
// writing the characters raw would reach no designation to be held to a rule.
std::string Encoded(std::string_view value) {
  return EncodeProtectBlock(value, DefaultProtectEncoding());
}

// The designation §34.5.26.1 writes as the keyword standing alone with the
// value on the line beneath it. It is read only inside a previously generated
// envelope, so the cases using it wrap their text in one.
std::string DesignatesPublicKey(std::string_view value) {
  std::string text = "`pragma protect key_public_key\n";
  text.append(Encoded(value)).append("\n");
  return text;
}

// A decryption envelope as some other tool wrote it, carrying `described`.
std::string ForeignEnvelope(const std::string& described) {
  std::string text = "`pragma protect begin_protected\n";
  text.append(described);
  text.append("`pragma protect end_protected\n");
  return text;
}

// An encryption region holding `described` and then the design.
std::string Region(const std::string& described) {
  std::string text = "`pragma protect begin\n";
  text.append(described).append(kSealedDesign);
  text.append("`pragma protect end\n");
  return text;
}

// The one key the entity holds, for a region whose keys travel in a key block.
ProtectKeyList TheEntitysKey() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kEntity, kKeyName, kEntityKey));
  return keys;
}

// A reading of `src` with the reports it raised kept beside it.
struct Read {
  SourceManager mgr;
  DiagEngine diag{mgr};

  explicit Read(const std::string& src) {
    Preprocessor pp(mgr, diag, PreprocConfig{});
    pp.Preprocess(mgr.AddFile("<test>", src));
  }
};

// The 1-based line of `src` carrying `value` and nothing else, which is where
// a designation announced by a keyword standing alone is read from and so where
// a report about that designation stands. The same characters stand earlier in
// these sources as the value of an expression, so the line is found by the
// newlines around it rather than by the value alone.
uint32_t LineCarryingOnly(const std::string& src, std::string_view value) {
  std::string alone = "\n";
  alone.append(value).append("\n");
  return LineHolding(src, alone) + 1;
}

// The report §34.5.23 draws from one value written against both of the names.
constexpr std::string_view kBothNamesOneValue =
    "writes one value against both of the names that designate a key of the "
    "key_keyowner in effect";

// -- The constraint the value is held to ------------------------------------

// §34.5.23.2 puts on this value the constraints §34.5.10.2 states, and those
// have the values designating a key unique for the entity they are written
// under. A text writing one value against both of the names has designated one
// of that entity's keys twice.
//
// The report stands on the line the announced value was read from, that being
// where the second designation was made rather than where its keyword stood.
TEST(ProtectKeyKeyownerDescription, OneValueAgainstBothDesignationsIsReported) {
  std::string src = ForeignEnvelope(NamesEntity(kEntity) +
                                    Writes("key_keyname", kSharedValue) +
                                    DesignatesPublicKey(kSharedValue));
  Read run(src);
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(), kBothNamesOneValue,
                            LineCarryingOnly(src, Encoded(kSharedValue)),
                            "34.5.23"));
}

// The constraint is about the entity the values are unique for and not about
// the characters. One value written under two entities designates a key of each
// and repeats nothing, so nothing is reported.
TEST(ProtectKeyKeyownerDescription, TwoEntitiesKeepTheirDesignationsApart) {
  Read run(ForeignEnvelope(
      NamesEntity(kEntity) + Writes("key_keyname", kSharedValue) +
      NamesEntity(kOtherEntity) + DesignatesPublicKey(kSharedValue)));
  EXPECT_FALSE(run.diag.HasErrors());
}

// Two names carrying different values under one entity designate two of that
// entity's keys, which is what the constraint admits. Without this the case
// above would hold of a reading that reported every second designation.
TEST(ProtectKeyKeyownerDescription, DistinctValuesUnderOneEntityAreLeftAlone) {
  Read run(ForeignEnvelope(NamesEntity(kEntity) +
                           Writes("key_keyname", kSharedValue) +
                           DesignatesPublicKey(kOtherValue)));
  EXPECT_FALSE(run.diag.HasErrors());
}

// -- Unchanged in the output file -------------------------------------------

// §34.5.23.2: the value is unchanged in the output file. The region below
// writes it bare, so an envelope returning it in quotation marks has changed
// the pragma_value the author wrote whatever it still denotes.
TEST(ProtectKeyKeyownerDescription, TheEntityGoesOutInTheSpellingItCameInWith) {
  std::string envelope =
      EncryptEnvelopes(Region(NamesEntity(kEntity)), kAuthorsKey);
  EXPECT_FALSE(Holds(envelope, kSealedDesign)) << envelope;
  EXPECT_TRUE(Holds(envelope, NamesEntity(kEntity))) << envelope;
}

// The exception §34.5.23.2 does not state. A region whose keys travel in key
// blocks of its own is the digital signature that excuses the entity of the
// data, the entity of the digest and the cipher of the digest's key from
// standing in the clear; this entity is the one whose key opens those blocks,
// its own subclause states no exception, and it stands in the spelling it came
// in with wherever the tool writes it.
TEST(ProtectKeyKeyownerDescription, TheEntityIsUnchangedInABlocksOwnDirective) {
  std::string envelope = EncryptEnvelopes(
      Region(NamesEntity(kEntity) + Writes("key_keyname", kKeyName)), {},
      TheEntitysKey());
  EXPECT_FALSE(Holds(envelope, kSealedDesign)) << envelope;
  EXPECT_TRUE(Holds(envelope, "`pragma protect key_block")) << envelope;
  EXPECT_EQ(TimesWritten(envelope, "key_keyowner=\""), 0U) << envelope;
  EXPECT_EQ(TimesWritten(envelope, NamesEntity(kEntity)), 2U) << envelope;
}

// -- A parenthesized list names no entity ------------------------------------

// §34.5.23.1 writes a string against this keyword, and §22.5.1 makes a
// parenthesized pragma_value a list of further pragma expressions rather than
// one written thing, so a list names no entity. A region that wrote nothing
// else about the entity whose keys its own keys are under leaves the envelope
// with no key_keyowner directive to carry.
//
// What is counted is the keyword and its '=' rather than a quoted value.
// ProtectKeyKeyownerDirective in src/preprocessor/protect_keywords.cpp writes
// this value as the source spelled it, so a list taken as the value goes out
// with its parentheses bare and a search for the quoted spelling would miss it.
//
// The design is checked gone first because an unencrypted region comes back as
// its own source text, and that text writes the directive under test.
TEST(ProtectKeyKeyownerDescription, AListLeavesNoEntityDirectiveOnTheEnvelope) {
  std::string envelope =
      EncryptEnvelopes(Region(NamesEntity(kEntityList)), kAuthorsKey);
  EXPECT_FALSE(Holds(envelope, kSealedDesign)) << envelope;
  EXPECT_EQ(TimesWritten(envelope, "key_keyowner="), 0U) << envelope;
}

// The control beside it: the spelling §34.5.23.1 does define reaches the
// envelope. Without this the case above would hold of a tool that wrote no
// key_keyowner directive whatever the region named.
TEST(ProtectKeyKeyownerDescription, AStringNamesTheEntityTheEnvelopeCarries) {
  std::string envelope =
      EncryptEnvelopes(Region(Writes("key_keyowner", kEntity)), kAuthorsKey);
  EXPECT_FALSE(Holds(envelope, kSealedDesign)) << envelope;
  EXPECT_TRUE(Holds(envelope, Writes("key_keyowner", kEntity))) << envelope;
}

// A list written after a string has named nobody, so the entity the string
// named still stands and it is that string §34.5.23.2 has unchanged in the
// output file. The list itself appears nowhere, which is also what says the
// region was encrypted rather than handed back.
TEST(ProtectKeyKeyownerDescription, AListLeavesTheStringNamedBeforeItStanding) {
  std::string envelope = EncryptEnvelopes(
      Region(Writes("key_keyowner", kEntity) + NamesEntity(kEntityList)),
      kAuthorsKey);
  EXPECT_TRUE(Holds(envelope, Writes("key_keyowner", kEntity))) << envelope;
  EXPECT_FALSE(Holds(envelope, kEntityList)) << envelope;
}

// -- The key a reader reaches -----------------------------------------------

// §34.5.23.2: on the way back the entity is combined with the name to reach the
// key that decrypts the key block. A reading holding that entity's key opens
// the block, and what the block opens on to is the design the region sealed.
TEST(ProtectKeyKeyownerDescription, TheEntityAndTheNameOpenTheKeyBlock) {
  std::string envelope = EncryptEnvelopes(
      Region(NamesEntity(kEntity) + Writes("key_keyname", kKeyName)), {},
      TheEntitysKey());
  SourceManager mgr;
  DiagEngine diag{mgr};
  PreprocConfig config;
  config.protect_keys = TheEntitysKey();
  Preprocessor pp(mgr, diag, std::move(config));
  std::string text = pp.Preprocess(mgr.AddFile("<test>", envelope));
  EXPECT_FALSE(diag.HasErrors()) << text;
  EXPECT_TRUE(Holds(text, kSealedDesign)) << text;
}

// The same envelope read by a tool holding that key under another entity. The
// key is the one the block was sealed under and the name is the one the block
// designates, so the entity is the only thing left to reach it by.
TEST(ProtectKeyKeyownerDescription, AnotherEntityHoldingTheKeyReachesNothing) {
  std::string envelope = EncryptEnvelopes(
      Region(NamesEntity(kEntity) + Writes("key_keyname", kKeyName)), {},
      TheEntitysKey());
  ProtectKeyList held;
  held.Add(KeyOf(kOtherEntity, kKeyName, kEntityKey));
  SourceManager mgr;
  DiagEngine diag{mgr};
  PreprocConfig config;
  config.protect_keys = held;
  Preprocessor pp(mgr, diag, std::move(config));
  std::string text = pp.Preprocess(mgr.AddFile("<test>", envelope));
  EXPECT_FALSE(Holds(text, kSealedDesign)) << text;
}

}  // namespace
