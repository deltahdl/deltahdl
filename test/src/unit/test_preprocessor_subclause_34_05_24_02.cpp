// §34.5.24 key_method, Description.
//
// §34.5.24.2 says three things about the keyword §34.5.24.1 spells, and this
// implementation cannot honour the first two at once for a region naming a
// cipher it does not have.
//
//   ENCRYPTION INPUT: the expression indicates the encryption algorithm that
//   shall be used to encrypt the keys used to encrypt the data_block. A region
//   naming one has stated what its own key block is to be sealed with.
//
//   ENCRYPTION OUTPUT: the key_method is unchanged in the output file. No
//   exception is stated, where the cipher of the data, the entity of the digest
//   and the algorithm computing a digest each have one for a digital signature.
//
//   DECRYPTION INPUT: the expression indicates the algorithm that shall be used
//   to decrypt the key_block.
//
// This implementation has one cipher and names it kDataMethod
// (src/preprocessor/protect_envelope_output.h). Sealing a region's key block
// under that while writing out whichever identifier its author named would hand
// back an envelope claiming an algorithm nobody used, so #3278 settled the pair
// the way #3270 settled it for the cipher the data are under. A region naming
// any other identifier is reported where it closes, by
// ReportUnprovidedKeyMethod in src/preprocessor/protect_processing.cpp, and the
// envelope states the cipher its blocks are really under, AppendClearKeyNames
// in src/preprocessor/protect_envelope_output.cpp writing it. Every source this
// tool accepts then has its identifier unchanged, the only identifiers it
// accepts being the one it writes and none at all.
//
// The identifier is written only where the envelope carries key blocks. A
// region whose keys travel in no block has none of them encrypted, so no cipher
// describes anything and none is stated.
//
// DECRYPTION INPUT is answered by the reading side, and the reading side says
// nothing at all: a key block under a cipher this implementation does not
// provide fails to open and is passed over in silence. §34.5.27.2 makes several
// key blocks alternative ways into one envelope, so a block written for some
// other reader is not an error, and
// ProtectKeyBlockDescription.TheBlockThisReaderCannotOpenCostsItNoReport in
// test_preprocessor_subclause_34_05_27_02.cpp is what holds the reading to it.
//
// Which spelling of the expression puts which identifier in effect is
// §34.5.24.1's and is stated in test_preprocessor_subclause_34_05_24_01.cpp,
// along with a parenthesized list reaching the envelope as nothing.
//
// Whether the table marks an identifier as one every implementation provides is
// §34.5.11.2's, and three cases below state the answer for this keyword.
// §34.5.24.2 sends key_method to the identifiers written for data_method, so
// Table 34-3's required column answers for this keyword as it does for that
// one. That column marks des-cbc required and the other fifteen rows optional.
// §34.5.11.2 says the required methods are standard in every implementation,
// and leaves an additional identifier and the cipher behind it to the
// implementation. IsRequiredProtectEncryptionAlgorithm in
// src/preprocessor/protect_key_method.h is what answers the question, and the
// report names the half of the table the identifier came from. #3430 covers
// providing the ciphers the table requires of every implementation, and the
// report is what stands in their place until that lands.

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

// The identifier Table 34-3 requires of every implementation, which is the one
// a region names below to ask for a cipher this implementation does not have,
// and the identifier a region names for the algorithm its digests are computed
// with. The second is there to be looked for and not found: §34.5.21.2 excuses
// it from the clear wherever a digital signature is used and §34.5.24.2 excuses
// this one from nothing.
constexpr std::string_view kKeyCipher = "des-cbc";
constexpr std::string_view kDigestAlgorithm = "md5";

// An optional identifier of the same table, for the half of the report that
// says the table did not require what was asked for.
constexpr std::string_view kOptionalCipher = "aes256-cbc";

// The identifier this implementation writes for the one cipher it has, which is
// the cipher a key block is really sealed under.
constexpr std::string_view kProvidedCipher = kDataMethod;

constexpr std::string_view kSealedDesign = "module sealed_m; endmodule\n";

// A third tabulated identifier, named by the one region below whose keys travel
// in no key block. It is spelled apart from the two above so that the case
// reading that envelope reads for the cipher its own region asked for.
constexpr std::string_view kUnblockedCipher = "cast128-cbc";

// The entity a region names for its data, the name picking that entity's key
// out of its list, and the key itself. A region whose data name reaches a key
// the tool holds is sealed under that key directly, so it designates no key of
// its own and no key block is written for it.
constexpr std::string_view kDirectEntity = "harbour-labs";
constexpr std::string_view kDirectKeyName = "direct-2028";
constexpr std::string_view kDirectKey = "harbour-labs-direct-key";

// The expression announcing a key block, which is how a case below tells an
// envelope carrying one from an envelope carrying none.
constexpr std::string_view kKeyBlockLine = "`pragma protect key_block\n";

// The directive an envelope states this keyword with, up to the value. The case
// claiming no such directive was written searches for this much of it, the
// value being the part it claims is absent.
constexpr std::string_view kKeyMethodDirective = "`pragma protect key_method=";

// The report a region asking for a cipher this implementation cannot seal its
// keys under draws, up to the identifier that region named. The keyword is part
// of it, so the report §34.5.11.2 makes about the cipher the data are under
// does not answer for this one.
constexpr std::string_view kNoCipherOfOurs =
    "protect pragma key_method asks for an encryption algorithm this "
    "implementation does not provide: ";

// The two halves of Table 34-3 as that report names them. Which half the
// identifier came from is the whole of what separates the two reported cases
// below from each other.
constexpr std::string_view kTableObligesEveryTool =
    ", which IEEE 1800-2023 Table 34-3 requires of every implementation";
constexpr std::string_view kTableLeavesItOptional =
    ", which IEEE 1800-2023 Table 34-3 does not require of every "
    "implementation";

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

// The whole of that report for one identifier taken from one half of the table.
std::string AskingFor(std::string_view identifier, std::string_view tabulated) {
  std::string message(kNoCipherOfOurs);
  message.append(identifier).append(tabulated);
  return message;
}

ProtectKeyList TheDirectEntitysKey() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kDirectEntity, kDirectKeyName, kDirectKey));
  return keys;
}

// A region whose data name reaches a key the tool holds, stating `described`
// about itself. Its keys travel in no key block: the key it is sealed under is
// one the reader already holds, so there is nothing to encrypt and nothing to
// carry.
std::string DirectRegion(const std::string& described) {
  std::string text = "`pragma protect begin\n";
  text.append(Writes("data_keyowner", kDirectEntity));
  text.append(Writes("data_keyname", kDirectKeyName));
  text.append(described).append(kSealedDesign);
  text.append("`pragma protect end\n");
  return text;
}

// Envelope encryption over a source an author wrote, with the reports it made
// kept beside the envelope it produced. The source is added to the manager so
// that a report stands at the line of it the author wrote the identifier on,
// which is the line the cases below name.
struct AuthorsRun {
  SourceManager mgr;
  DiagEngine diag{mgr};
  std::string envelope;

  AuthorsRun(const std::string& source, const ProtectKeyList& keys)
      : envelope(EncryptEnvelopes(source, {}, keys, &diag,
                                  mgr.AddFile("<test>", source))) {}
};

// The identifier `envelope` states against `keyword`, with the quotation marks
// it was written with, if any, removed. §22.5.1 gives a pragma_value more than
// one spelling, and what §34.5.24.2 settles is which algorithm the identifier
// names rather than which spelling states it, so what a case reads back is the
// characters naming the algorithm. Empty where the envelope states the keyword
// nowhere.
std::string_view IdentifierStatedFor(std::string_view envelope,
                                     std::string_view keyword) {
  std::string directive = "`pragma protect ";
  directive.append(keyword).append("=");
  size_t at = envelope.find(directive);
  if (at == std::string_view::npos) return {};
  size_t from = at + directive.size();
  size_t end = envelope.find('\n', from);
  return ProtectPragmaValueBody(envelope.substr(from, end - from));
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
//
// The identifier the region names is the one this implementation writes, which
// is what leaves it unchanged: the region asked for the cipher its block was
// going to be sealed under, so neither rule gave way. A region naming any other
// identifier is reported instead, and the cases under
// ProtectKeyMethodEncryptionInput below are where that stands.
TEST(ProtectKeyMethodDescription,
     TheAlgorithmStandsUnchangedOnASignedEnvelope) {
  std::string envelope =
      SignedEnvelope(Writes("key_method", kProvidedCipher) +
                     Writes("digest_method", kDigestAlgorithm));
  EXPECT_EQ(IdentifierStatedFor(envelope, "key_method"), kProvidedCipher)
      << envelope;
  EXPECT_FALSE(Holds(envelope, "digest_method")) << envelope;
}

// §34.5.24.2 has the keys of a signed region encrypted under the algorithm the
// identifier names, so the envelope of a region that named none states the
// cipher its blocks are really under rather than leaving a reader with nothing
// to open them with. That cipher is this implementation's own:
// ProtectKeyBlockDirective in src/preprocessor/protect_key_block.cpp seals a
// key block with EncryptProtectedRegion and with nothing else.
TEST(ProtectKeyMethodDescription,
     ASignedEnvelopeStatesTheCipherItsKeyBlocksAreUnder) {
  std::string envelope = SignedEnvelope("");
  EXPECT_EQ(IdentifierStatedFor(envelope, "key_method"), kProvidedCipher)
      << envelope;
}

// The identifier stands ahead of the blocks it governs. A reader has to hold it
// by the time a key block is reached, so an envelope stating it after the block
// would state it too late to be of use.
TEST(ProtectKeyMethodDescription, TheAlgorithmStandsAheadOfTheBlocksItGoverns) {
  std::string envelope = SignedEnvelope("");
  size_t stated = envelope.find(kKeyMethodDirective);
  size_t block = envelope.find(kKeyBlockLine);
  ASSERT_NE(stated, std::string::npos) << envelope;
  ASSERT_NE(block, std::string::npos) << envelope;
  EXPECT_LT(stated, block) << envelope;
}

// -- What an envelope stating one is still read as ---------------------------

// The round trip §34.5.24.2's DECRYPTION INPUT rests on, and the one the
// reports added for #3278 had to leave standing: a region sealed behind a key
// block is read back by a tool holding the key that opens that block, and the
// design comes out. The identifier the region states is the one this
// implementation writes, so nothing the region asked for was refused.
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

// -- The cipher a region asks for its own keys -------------------------------

// §34.5.24.2's ENCRYPTION INPUT has the identifier indicate "the encryption
// algorithm that shall be used to encrypt the keys used to encrypt the
// data_block", so a region naming des-cbc has stated what its own key block is
// to be sealed with. This implementation seals one under the cipher it names
// kDataMethod and under no other, so the region asked for something it cannot
// be given and is told so. Table 34-3 marks des-cbc Required and the report
// says so, §34.5.11.2 calling a required method standard in every
// implementation and this implementation being the one falling short.
//
// The identifier stands on the fifth line, the region opening on the first and
// closing on the seventh, so a report placed at either delimiter fails this.
TEST(ProtectKeyMethodEncryptionInput,
     ARegionAskingForTheRequiredCipherForItsKeysIsReported) {
  AuthorsRun run(SignedRegion(Writes("key_method", kKeyCipher)),
                 TheEntitysKey());
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(),
                            AskingFor(kKeyCipher, kTableObligesEveryTool), 5,
                            "34.5.24.2"))
      << run.envelope;
}

// §34.5.24.2 sends this keyword to the identifiers written for data_method, and
// Table 34-3 marks aes256-cbc Optional, so the report says the table did not
// require it. An implementation offering that cipher is required to offer it
// under this identifier, and this one offers it under no identifier at all.
// Which half of the table the identifier came from is the whole of what
// separates this case from the one above.
//
// The source writes a design element around the region, so the identifier
// stands on the sixth line here rather than the fifth, and the delimiters stand
// on the second and the eighth.
TEST(ProtectKeyMethodEncryptionInput,
     ARegionAskingForAnOptionalCipherForItsKeysIsToldTheTableDoesNotRequireIt) {
  std::string source = "module bulkhead_m;\n";
  source.append(SignedRegion(Writes("key_method", kOptionalCipher)));
  source.append("endmodule\n");
  AuthorsRun run(source, TheEntitysKey());
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(),
                            AskingFor(kOptionalCipher, kTableLeavesItOptional),
                            6, "34.5.24.2"))
      << run.envelope;
}

// A region naming the identifier this implementation writes has asked for the
// cipher its key block is sealed under, so nothing it asked for is refused and
// the envelope states what the region named. Without this case the two above
// would hold of a tool that reported every region whatever cipher it asked for.
TEST(ProtectKeyMethodEncryptionInput,
     ARegionAskingForTheCipherOurKeyBlocksUseDrawsNoReport) {
  AuthorsRun run(SignedRegion(Writes("key_method", kProvidedCipher)),
                 TheEntitysKey());
  EXPECT_FALSE(run.diag.HasErrors()) << run.envelope;
  EXPECT_EQ(IdentifierStatedFor(run.envelope, "key_method"), kProvidedCipher)
      << run.envelope;
  EXPECT_FALSE(Holds(run.envelope, kSealedDesign)) << run.envelope;
}

// §34.5.24.2 is about the keys that get encrypted, and the region below has
// none of them encrypted: its data name reaches a key the tool holds, so it is
// sealed under that key directly and no key block is written for it. The cipher
// it named describes nothing, so it is neither honoured nor refused, and the
// envelope states no identifier for this keyword at all.
TEST(ProtectKeyMethodEncryptionInput,
     ARegionWhoseKeysTravelInNoBlockStatesNoCipherForThem) {
  AuthorsRun run(DirectRegion(Writes("key_method", kUnblockedCipher)),
                 TheDirectEntitysKey());
  EXPECT_FALSE(run.diag.HasErrors()) << run.envelope;
  EXPECT_EQ(TimesWritten(run.envelope, kKeyBlockLine), 0U) << run.envelope;
  EXPECT_FALSE(Holds(run.envelope, kKeyMethodDirective)) << run.envelope;
  EXPECT_FALSE(Holds(run.envelope, kSealedDesign)) << run.envelope;
}

}  // namespace
