// §34.5.24 key_method, Description.
//
// §34.5.24.2 says four things about the keyword §34.5.24.1 spells.
//
//   The expression names the encryption algorithm that encrypts the keys the
//   data block is encrypted under.
//
//   The identifiers naming those algorithms are the ones written for the cipher
//   the data are under. The subclause tabulates none of its own.
//
//   The identifier is unchanged in the output file. No exception is stated,
//   where the cipher of the data, the entity of the digest and the algorithm
//   computing a digest each have one for a digital signature.
//
//   On the way back it names the algorithm the key block is decrypted with.
//
// The middle two are what a run can be held to and are what this file states.
// The first and the last are not: nothing in a run reads the identifier, a key
// block being sealed and opened under the one cipher this implementation has
// whatever an envelope says, and #3278 records that along with what stands in
// the way of the obvious remedy. Two cases below stand where that remedy would
// land, stating the round trip a fix has to leave working rather than the rule
// it would implement.
//
// Which spelling of the expression puts which identifier in effect is
// §34.5.24.1's and is stated in test_preprocessor_subclause_34_05_24_01.cpp,
// along with the identifier reaching the envelope as written and a
// parenthesized list reaching it as nothing.

#include <gtest/gtest.h>

#include <span>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_protect_keys.h"
#include "helpers_text_lines.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_digest_key.h"
#include "preprocessor/protect_key_method.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

// The entity a region designates to open its keys, the name picking that
// entity's key out, and the key itself. A region reaching a key this way is
// written a key block, which is the digital signature the keywords beside this
// one are excused from the clear by and this one is not.
constexpr std::string_view kEntity = "meridian-trust";
constexpr std::string_view kKeyName = "wrapping-2027";
constexpr std::string_view kEntityKey = "meridian-trust-wrapping-key";

// The name a region gives the key its data are under. A name with no key held
// for it is what sends the region to a key block rather than to a key of its
// author's.
constexpr std::string_view kDataKeyName = "design-2027";

// The identifier a region names for the cipher its own keys are under, and the
// one it names for the algorithm its digests are computed with. The second is
// there to be looked for and not found: §34.5.21.2 excuses it from the clear
// wherever a digital signature is used and §34.5.24.2 excuses this one from
// nothing.
constexpr std::string_view kKeyCipher = "des-cbc";
constexpr std::string_view kDigestAlgorithm = "md5";

constexpr std::string_view kSealedDesign = "module sealed_m; endmodule\n";

std::string Writes(std::string_view keyword, std::string_view value) {
  std::string text = "`pragma protect ";
  text.append(keyword).append("=\"").append(value).append("\"\n");
  return text;
}

ProtectKeyList TheEntitysKey() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kEntity, kKeyName, kEntityKey));
  return keys;
}

// A region whose keys travel in a key block of its own, stating `described`
// about itself.
std::string SignedRegion(const std::string& described) {
  std::string text = "`pragma protect begin\n";
  text.append(Writes("key_keyowner", kEntity));
  text.append(Writes("key_keyname", kKeyName));
  text.append(Writes("data_keyname", kDataKeyName));
  text.append(described).append(kSealedDesign);
  text.append("`pragma protect end\n");
  return text;
}

// The envelope this tool writes for such a region, checked on the way out to be
// one that sealed its design behind a key block.
std::string SignedEnvelope(const std::string& described) {
  std::string envelope =
      EncryptEnvelopes(SignedRegion(described), {}, TheEntitysKey());
  EXPECT_FALSE(Holds(envelope, kSealedDesign)) << envelope;
  EXPECT_TRUE(Holds(envelope, "`pragma protect key_block")) << envelope;
  return envelope;
}

// What a tool holding that entity's key recovers from `envelope`.
std::string ReadBack(const std::string& envelope) {
  SourceManager mgr;
  DiagEngine diag{mgr};
  PreprocConfig config;
  config.protect_keys = TheEntitysKey();
  Preprocessor pp(mgr, diag, std::move(config));
  return pp.Preprocess(mgr.AddFile("<test>", envelope));
}

// -- The identifiers the keyword admits --------------------------------------

// §34.5.24.2 tabulates no identifiers of its own and sends the reader to the
// ones written for the cipher the data are under. Sixteen rows, in the order
// that table lists them.
TEST(ProtectKeyMethodDescription,
     TheTableIsSixteenIdentifiersInTheOrderListed) {
  std::span<const ProtectEncryptionAlgorithm> rows =
      ProtectEncryptionAlgorithms();
  ASSERT_EQ(rows.size(), 16U);
  EXPECT_EQ(rows[0].identifier, "des-cbc");
  EXPECT_EQ(rows[1].identifier, "3des-cbc");
  EXPECT_EQ(rows[2].identifier, "aes128-cbc");
  EXPECT_EQ(rows[3].identifier, "aes256-cbc");
  EXPECT_EQ(rows[4].identifier, "aes192-cbc");
  EXPECT_EQ(rows[5].identifier, "blowfish-cbc");
  EXPECT_EQ(rows[6].identifier, "twofish256-cbc");
  EXPECT_EQ(rows[7].identifier, "twofish192-cbc");
  EXPECT_EQ(rows[8].identifier, "twofish128-cbc");
  EXPECT_EQ(rows[9].identifier, "serpent256-cbc");
  EXPECT_EQ(rows[10].identifier, "serpent192-cbc");
  EXPECT_EQ(rows[11].identifier, "serpent128-cbc");
  EXPECT_EQ(rows[12].identifier, "cast128-cbc");
  EXPECT_EQ(rows[13].identifier, "rsa");
  EXPECT_EQ(rows[14].identifier, "elgamal");
  EXPECT_EQ(rows[15].identifier, "pgp-rsa");
}

// The required column is part of what the table says rather than an aside about
// it. One row names an algorithm any tool can be handed a block under; the
// other fifteen name algorithms a tool may know, and a text using one of them
// has assumed something about its reader.
TEST(ProtectKeyMethodDescription,
     OneIdentifierIsRequiredOfEveryImplementation) {
  std::span<const ProtectEncryptionAlgorithm> rows =
      ProtectEncryptionAlgorithms();
  ASSERT_EQ(rows.size(), 16U);
  EXPECT_TRUE(IsRequiredProtectEncryptionAlgorithm("des-cbc"));
  size_t required = 0;
  for (const ProtectEncryptionAlgorithm& row : rows) {
    if (row.required) ++required;
  }
  EXPECT_EQ(required, 1U);
}

// Each row names the published algorithm its identifier stands for, which is
// the column that makes the identifier mean one algorithm rather than whichever
// one a tool cared to attach the name to.
TEST(ProtectKeyMethodDescription, EachRowNamesThePublishedAlgorithm) {
  std::span<const ProtectEncryptionAlgorithm> rows =
      ProtectEncryptionAlgorithms();
  ASSERT_EQ(rows.size(), 16U);
  EXPECT_NE(rows[0].algorithm.find("FIPS 46-3"), std::string_view::npos);
  EXPECT_NE(rows[2].algorithm.find("FIPS 197"), std::string_view::npos);
  EXPECT_NE(rows[12].algorithm.find("IETF RFC 2144"), std::string_view::npos);
  EXPECT_NE(rows[13].algorithm.find("IETF RFC 2437"), std::string_view::npos);
  EXPECT_NE(rows[15].algorithm.find("IETF RFC 2440"), std::string_view::npos);
}

// An identifier outside the table is one the standard does not decide rather
// than one it forbids, and what the table answers is whether the standard named
// it. The answer is on the characters written: a name differing only in case is
// a name the table does not list.
TEST(ProtectKeyMethodDescription,
     AnIdentifierOutsideTheTableIsLeftToTheImplementation) {
  EXPECT_FALSE(IsProtectKeyMethodIdentifier("a-cipher-nobody-tabulated"));
  EXPECT_FALSE(IsProtectKeyMethodIdentifier("DES-CBC"));
  EXPECT_FALSE(IsProtectKeyMethodIdentifier(""));
}

// §34.5.24.2 sends this keyword to the identifiers written for another, and
// §34.5.17.2 sends a third keyword to the same place. One table answers for all
// of them, so an identifier admitted for one is admitted for the others, and
// what a case can state is the agreement rather than the list twice over.
TEST(ProtectKeyMethodDescription, TheIdentifiersAreTheOnesTheOtherCiphersUse) {
  for (const ProtectEncryptionAlgorithm& row : ProtectEncryptionAlgorithms()) {
    EXPECT_TRUE(IsProtectKeyMethodIdentifier(row.identifier)) << row.identifier;
    EXPECT_TRUE(IsProtectDigestKeyMethodIdentifier(row.identifier))
        << row.identifier;
  }
  EXPECT_EQ(IsProtectKeyMethodIdentifier("a-cipher-nobody-tabulated"),
            IsProtectDigestKeyMethodIdentifier("a-cipher-nobody-tabulated"));
}

// -- Unchanged in the output file --------------------------------------------

// §34.5.24.2 states no exception, and the envelope below is the one the other
// keywords have theirs for: its keys travel in a key block of its own. The
// algorithm computing the region's digests is kept out of the clear there under
// §34.5.21.2, and the algorithm its keys are under stands in the clear all the
// same. What it is needed for is opening the very block the others hide in, so
// one swept inside would have to be read out of the block it opens.
TEST(ProtectKeyMethodDescription,
     TheAlgorithmStandsUnchangedOnASignedEnvelope) {
  std::string envelope =
      SignedEnvelope(Writes("key_method", kKeyCipher) +
                     Writes("digest_method", kDigestAlgorithm));
  EXPECT_TRUE(Holds(envelope, Writes("key_method", kKeyCipher))) << envelope;
  EXPECT_FALSE(Holds(envelope, "digest_method")) << envelope;
}

// The identifier stands ahead of the blocks it governs. A reader has to hold it
// by the time a key block is reached, so an envelope stating it after the block
// would state it too late to be of use.
TEST(ProtectKeyMethodDescription, TheAlgorithmStandsAheadOfTheBlocksItGoverns) {
  std::string envelope = SignedEnvelope(Writes("key_method", kKeyCipher));
  size_t stated = envelope.find(Writes("key_method", kKeyCipher));
  size_t block = envelope.find("`pragma protect key_block");
  ASSERT_NE(stated, std::string::npos) << envelope;
  ASSERT_NE(block, std::string::npos) << envelope;
  EXPECT_LT(stated, block) << envelope;
}

// -- What an envelope stating one is still read as ---------------------------

// #3278 is where the identifier stops being read, and these two stand where a
// fix for it would land. §34.5.24.2 has the identifier written out unchanged,
// so an envelope this tool produced states whichever algorithm its author named
// rather than the one its blocks are really under. A reading that held a block
// to the stated identifier would turn away this tool's own output, which is
// what makes the remedy a choice rather than an omission.
TEST(ProtectKeyMethodDescription, AnEnvelopeStatingOneIsReadBackAllTheSame) {
  EXPECT_TRUE(Holds(ReadBack(SignedEnvelope(Writes("key_method", kKeyCipher))),
                    kSealedDesign));
}

// The control beside it: the same region naming no algorithm at all is read
// back too, so the case above says the stated identifier did not stop the
// reading rather than that the reading works.
TEST(ProtectKeyMethodDescription, AnEnvelopeStatingNoneIsReadBackToo) {
  EXPECT_TRUE(Holds(ReadBack(SignedEnvelope("")), kSealedDesign));
}

}  // namespace
