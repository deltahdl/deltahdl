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
// The first three are what a run can be held to and are what this file states.
//
// The first two are the pair a tool with one cipher cannot honour together, and
// #3278 settled which gives way. Writing the author's identifier out unchanged
// would state a cipher the block is not under, this tool sealing every key
// block with the one cipher it has; encrypting under the identifier written is
// what it cannot do. So a region naming another cipher is refused, and the
// identifier every accepted source carries is unchanged because the only ones
// accepted are the one this tool writes and none at all.
// ReportUnprovidedKeyMethod in src/preprocessor/protect_processing.cpp is the
// refusal and AppendClearKeyNames in
// src/preprocessor/protect_envelope_output.cpp is the writing.
//
// The last is answerable because of that: an envelope states the cipher its
// blocks are really under, so a reader is told which algorithm decrypts the key
// block. Nothing in a run asks it yet. A block under any other cipher fails to
// open and is passed over in silence, which §34.5.27.2 calls for whatever the
// reason -- several key blocks are alternative ways into one envelope, so a
// block written for some other reader is not an error, and
// ProtectKeyBlockDescription.TwoBlocksAreWaysIntoOneEnvelope in
// test_preprocessor_subclause_34_05_27_02.cpp is what holds that standing.
//
// Which spelling of the expression puts which identifier in effect is
// §34.5.24.1's and is stated in test_preprocessor_subclause_34_05_24_01.cpp,
// along with the identifier reaching the envelope as written and a
// parenthesized list reaching it as nothing.
//
// Whether the table marks an identifier as one every implementation provides is
// §34.5.11.2's, and three cases below state the answer for this keyword.
// §34.5.24.2 sends key_method to the identifiers written for data_method, so
// Table 34-3's required column answers for this keyword as it does for that
// one. That column marks des-cbc required and the other fifteen rows optional.
// §34.5.11.2 says the required methods are standard in every implementation,
// and leaves an additional identifier and the cipher behind it to the
// implementation. IsRequiredProtectEncryptionAlgorithm in
// src/preprocessor/protect_key_method.h is what answers the question, and
// ReportUnprovidedDataMethod in src/preprocessor/protect_processing.cpp asks it
// to say, of a cipher this tool does not provide, whether the standard required
// it. #3270 is where that reading came from.

#include <gtest/gtest.h>

#include <span>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_protect_keys.h"
#include "helpers_reported_error.h"
#include "helpers_text_lines.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_digest_key.h"
#include "preprocessor/protect_envelope_output.h"
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

// An optional identifier of the same table, for the half of the report that
// says the table did not require what was asked for.
constexpr std::string_view kOptionalCipher = "aes256-cbc";

// The identifier this implementation writes for the one cipher it has, which is
// the cipher a key block is really sealed under.
constexpr std::string_view kProvidedCipher = kDataMethod;

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

// Each identifier is answered from the column of its own row. The case above
// states which row carries the mark and that no second row carries it; this one
// states that the answer given for an identifier is the mark standing beside
// it, so a reader asking about any of the fifteen optional rows is told no.
TEST(ProtectKeyMethodDescription, EachRowIsAnsweredFromItsOwnRequiredColumn) {
  for (const ProtectEncryptionAlgorithm& row : ProtectEncryptionAlgorithms()) {
    EXPECT_EQ(IsRequiredProtectEncryptionAlgorithm(row.identifier),
              row.required)
        << row.identifier;
  }
}

// An identifier the table does not list is required of nobody. §34.5.11.2
// leaves an additional identifier and the cipher behind it to the
// implementation, so nothing about such an identifier is standard in every
// implementation. An answer of yes would report a cipher one tool defined as
// one every reader owes its author. The answer is on the characters written, so
// a name differing from a tabulated one only in case is answered the same way.
TEST(ProtectKeyMethodDescription,
     AnIdentifierOutsideTheTableIsRequiredOfNobody) {
  EXPECT_FALSE(
      IsRequiredProtectEncryptionAlgorithm("a-cipher-nobody-tabulated"));
  EXPECT_FALSE(IsRequiredProtectEncryptionAlgorithm("DES-CBC"));
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
      SignedEnvelope(Writes("key_method", kProvidedCipher) +
                     Writes("digest_method", kDigestAlgorithm));
  EXPECT_TRUE(Holds(envelope, Writes("key_method", kProvidedCipher)))
      << envelope;
  EXPECT_FALSE(Holds(envelope, "digest_method")) << envelope;
}

// The identifier stands ahead of the blocks it governs. A reader has to hold it
// by the time a key block is reached, so an envelope stating it after the block
// would state it too late to be of use.
TEST(ProtectKeyMethodDescription, TheAlgorithmStandsAheadOfTheBlocksItGoverns) {
  std::string envelope = SignedEnvelope(Writes("key_method", kProvidedCipher));
  size_t stated = envelope.find(Writes("key_method", kProvidedCipher));
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
  EXPECT_TRUE(
      Holds(ReadBack(SignedEnvelope(Writes("key_method", kProvidedCipher))),
            kSealedDesign));
}

// The control beside it: the same region naming no algorithm at all is read
// back too, so the case above says the stated identifier did not stop the
// reading rather than that the reading works.
TEST(ProtectKeyMethodDescription, AnEnvelopeStatingNoneIsReadBackToo) {
  EXPECT_TRUE(Holds(ReadBack(SignedEnvelope("")), kSealedDesign));
}

// -- The cipher a region asks its keys be put under -------------------------

// §34.5.24.2 has a region's own keys encrypted under the algorithm this
// identifier names and has the identifier unchanged in the output file. A tool
// with one cipher cannot honour both for a region naming another: writing the
// author's identifier out would state a cipher the block is not under, and
// encrypting under it is what the tool cannot do. Refusing the region settles
// it, so every source this tool accepts has its identifier unchanged and every
// envelope states the cipher its keys are really under. Issue #3278 is where
// that was settled, and §34.5.11.2's cipher was settled the same way in #3270.
//
// The report stands at the line the author wrote the expression on.
std::string SignedSourceNaming(std::string_view cipher) {
  std::string text = "`pragma protect begin\n";
  text.append(Writes("key_keyowner", kEntity));
  text.append(Writes("key_method", cipher));
  text.append(Writes("key_keyname", kKeyName));
  text.append(Writes("data_keyname", kDataKeyName));
  text.append(kSealedDesign);
  text.append("`pragma protect end\n");
  return text;
}

// One encrypting run over such a source, with the reports it made kept beside
// the text it wrote.
struct SigningRun {
  SourceManager mgr;
  DiagEngine diag{mgr};
  std::string text;

  explicit SigningRun(const std::string& src)
      : text(EncryptEnvelopes(src, {}, TheEntitysKey(), &diag,
                              mgr.AddFile("<test>", src))) {}
};

// The message the report carries, up to the half naming the table's column.
std::string AsksForCipher(std::string_view cipher) {
  std::string message(
      "protect pragma key_method asks for an encryption algorithm this "
      "implementation does not provide: ");
  message.append(cipher);
  return message;
}

// Table 34-3 marks des-cbc required, which §34.5.11.2 says is standard in every
// implementation, so a text naming it assumed nothing and this tool is what
// falls short. #3430 covers providing that cipher.
//
// The expression stands on the third line, the region opening on the first and
// closing on the seventh, so a report placed at either delimiter fails this.
TEST(ProtectKeyMethodDescription, ARequiredCipherAskedForIsReported) {
  SigningRun run(SignedSourceNaming(kKeyCipher));
  EXPECT_TRUE(ReportedError(
      run.diag.Diagnostics(),
      AsksForCipher(kKeyCipher) +
          ", which IEEE 1800-2023 Table 34-3 requires of every implementation",
      3, "34.5.24.2"))
      << run.text;
}

// The same for one of the fifteen rows the table leaves optional. Which half of
// the table the identifier came from is the whole of what separates this case
// from the one above, so the message is read for that half.
TEST(ProtectKeyMethodDescription, AnOptionalCipherAskedForIsReportedToo) {
  SigningRun run(SignedSourceNaming(kOptionalCipher));
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(),
                            AsksForCipher(kOptionalCipher) +
                                ", which IEEE 1800-2023 Table 34-3 does not "
                                "require of every implementation",
                            3, "34.5.24.2"))
      << run.text;
}

// The identifier this tool writes, asked for by name: the keys really are put
// under that cipher, so nothing is refused and the envelope states it. Without
// this the two cases above would hold of a tool that refused every region.
TEST(ProtectKeyMethodDescription, TheCipherWeProvideAskedForIsSealedInSilence) {
  SigningRun run(SignedSourceNaming(kProvidedCipher));
  EXPECT_FALSE(run.diag.HasErrors()) << run.text;
  EXPECT_TRUE(Holds(run.text, Writes("key_method", kProvidedCipher)))
      << run.text;
}

// A region whose keys travel in no key block is refused nothing, whatever it
// names: none of its keys is encrypted, so no cipher was asked for and none
// describes anything. The envelope states no identifier at all.
TEST(ProtectKeyMethodDescription, ACipherNamedWithNoKeyBlockIsNotReported) {
  std::string src = "`pragma protect begin\n";
  src.append(Writes("key_method", kKeyCipher));
  src.append(kSealedDesign);
  src.append("`pragma protect end\n");
  SourceManager mgr;
  DiagEngine diag{mgr};
  std::string written = EncryptEnvelopes(src, kEntityKey, ProtectKeyList(),
                                         &diag, mgr.AddFile("<test>", src));
  EXPECT_FALSE(diag.HasErrors()) << written;
  EXPECT_FALSE(Holds(written, "`pragma protect key_method")) << written;
}

// A signed region naming no identifier at all still gets one on its envelope,
// and it is the cipher the blocks are under. That is what leaves §34.5.24.2's
// last rule answerable: a reader is told which algorithm to decrypt the key
// block with, where before it was told whichever algorithm the author named or
// nothing.
TEST(ProtectKeyMethodDescription, ASignedEnvelopeStatesTheCipherItsBlocksUse) {
  EXPECT_TRUE(Holds(SignedEnvelope(""), Writes("key_method", kProvidedCipher)));
}

}  // namespace
