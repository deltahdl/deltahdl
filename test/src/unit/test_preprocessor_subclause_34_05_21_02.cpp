// §34.5.21 digest_method, Description.
//
// §34.5.21.2 says four things about the keyword §34.5.21.1 spells.
//
//   Written in an encrypting tool's input, the expression specifies the message
//   digest algorithm that shall generate the digests of the data_block and
//   key_block output that follows it, and the string is an identifier commonly
//   associated with a specific algorithm.
//
//   Table 34-4 gives the identifiers the standard specifies, two of them
//   required of every implementation and two optional. Further identifiers are
//   admitted and left to the implementation.
//
//   It is unchanged in the output file, except where a digital signature is
//   used, in which case it is encrypted with the key_method and placed in a
//   key_block.
//
//   On the way back, it indicates the algorithm that shall generate the digest
//   from the data_block.
//
// The table is carried by ProtectDigestAlgorithms, IsProtectDigestAlgorithm,
// IsRequiredProtectDigestAlgorithm and ProtectDigestIsAvailable in
// src/preprocessor/protect_digest.cpp, and the computation the identifier picks
// out by ProtectMessageDigest in the same file. The digest an encrypting run
// writes is produced by ProtectDigestBlockDirectives in
// src/preprocessor/protect_digest_block.cpp; where the identifier goes in what
// that run writes out is decided by AppendClearNames in
// src/preprocessor/protect_envelope_output.cpp and by KeyBlockContentFor in
// src/preprocessor/protect_key_block.cpp; and the identifier a reading
// regenerates a digest under is read by Preprocessor::DigestMethodInEffect in
// src/preprocessor/preprocessor_protect_keys.cpp.
//
// Which spelling puts which identifier in effect belongs to §34.5.21.1 and is
// stated in test_preprocessor_subclause_34_05_21_01.cpp. What this file states
// is what the identifier then does.

#include <gtest/gtest.h>

#include <span>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_protect_keys.h"
#include "helpers_protect_keyword_value.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_digest.h"
#include "preprocessor/protect_digest_block.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

// The identifier the regions below state. It is a row Table 34-4 marks
// required, so a reader of the envelope can recompute what was written under
// it, and it is not the identifier a text stating none is read under.
constexpr std::string_view kStated = kMd5DigestMethod;
static_assert(kStated != kDefaultDigestMethod,
              "a region stating the identifier the default already supplies "
              "produces the envelope of a region that stated nothing");

// The keyword as it stands in a directive, for asking whether an envelope wrote
// one. §34.4 tabulates digest_key_method as a separate name, and it does not
// hold these characters, so a search for this one answers about this one.
constexpr std::string_view kIdentifierKeyword = "digest_method";

// The entity that provided the key a region's key blocks are encrypted under,
// the name picking that key out, and the key itself.
constexpr std::string_view kProvider = "meridian-trust";
constexpr std::string_view kBlockKeyName = "wrapping-2027";
constexpr std::string_view kBlockKey = "meridian-trust-wrapping-key";

// The name a region gives the key its data are under. A name with no key held
// for it is what sends a region to a key block rather than to a key of its
// author's, which is the digital signature §34.5.21.2 states its exception for.
constexpr std::string_view kDataKeyName = "design-2027";

// The key an author encrypts with directly, for the envelope that carries no
// key block and so is not signed.
constexpr std::string_view kExchangeKey = "meridian-trust-author-key";

// The design a region seals, and the text a digest is computed over where the
// case computes one for itself.
constexpr std::string_view kSealedDesign = "module sealed_m; endmodule\n";
constexpr std::string_view kDigestedText = "the bytes a digest stands in for";

// The key a hand-built digest block is sealed under.
constexpr std::string_view kDigestKey = "seals-the-digest-of-this-region";

std::string Writes(std::string_view keyword, std::string_view value) {
  std::string text = "`pragma protect ";
  text.append(keyword).append("=\"").append(value).append("\"\n");
  return text;
}

// The expression §34.5.22 makes a request for a digest. It stands ahead of the
// region rather than inside it, §34.4 making the scope of the request lexical.
std::string RequestsDigest() { return "`pragma protect digest_block\n"; }

// A region whose keys travel in key blocks of its own, stating `described`
// about itself. This is the digital signature §34.5.21.2 makes its exception
// for: the region names a key the tool does not hold, so the tool makes one and
// writes a block carrying it.
std::string SignedRegion(const std::string& described) {
  std::string text = "`pragma protect begin\n";
  text.append(Writes("key_keyowner", kProvider));
  text.append(Writes("key_keyname", kBlockKeyName));
  text.append(Writes("data_keyname", kDataKeyName));
  text.append(described);
  text.append(kSealedDesign);
  text.append("`pragma protect end\n");
  return text;
}

// A region encrypted under the author's own key, which carries no key block and
// so is not signed.
std::string UnsignedRegion(const std::string& described) {
  std::string text = "`pragma protect begin\n";
  text.append(described);
  text.append(kSealedDesign);
  text.append("`pragma protect end\n");
  return text;
}

// The one key a reader of the signed envelopes holds: the one those envelopes'
// key blocks are encrypted under.
ProtectKeyList TheBlockKey() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kProvider, kBlockKeyName, kBlockKey));
  return keys;
}

// Whether `envelope` carries a digest block this tool made, which is one
// standing after the block it refers to. The request the source wrote stands
// outside every region and is copied through in the clear, so a search of the
// whole text finds that line and says nothing about whether a digest was
// produced.
//
// The data block is found by the expression announcing it, which §34.5.15.1
// spells as the keyword standing alone and §34.5.15.2 has speak for the next
// line in the file (issue #3272).
bool CarriesAGeneratedDigestBlock(const std::string& envelope) {
  size_t data = envelope.find("`pragma protect data_block\n");
  if (data == std::string::npos) return false;
  return envelope.find("`pragma protect digest_block", data) !=
         std::string::npos;
}

// The envelope this tool writes for a signed region stating `described`,
// checked on the way out to be one: the design is gone, and the envelope
// carries both a key block and a digest block. Without that check the cases
// below would hold of an envelope that sealed nothing.
std::string SignedEnvelope(const std::string& described) {
  std::string envelope = EncryptEnvelopes(
      RequestsDigest() + SignedRegion(described), {}, TheBlockKey());
  EXPECT_EQ(envelope.find(kSealedDesign), std::string::npos) << envelope;
  EXPECT_NE(envelope.find("`pragma protect key_block"), std::string::npos)
      << envelope;
  EXPECT_TRUE(CarriesAGeneratedDigestBlock(envelope)) << envelope;
  return envelope;
}

// The envelope this tool writes for an unsigned region stating `described`,
// checked the same way apart from the key block it does not have.
std::string UnsignedEnvelope(const std::string& described) {
  std::string envelope = EncryptEnvelopes(
      RequestsDigest() + UnsignedRegion(described), kExchangeKey);
  EXPECT_EQ(envelope.find(kSealedDesign), std::string::npos) << envelope;
  EXPECT_EQ(envelope.find("`pragma protect key_block"), std::string::npos)
      << envelope;
  EXPECT_TRUE(CarriesAGeneratedDigestBlock(envelope)) << envelope;
  return envelope;
}

// A reading of `src` by a tool holding `keys`, with the preprocessor kept alive
// so what the reading left in effect can be read off it.
struct ReadUnderKeys {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp;
  std::string text;

  ReadUnderKeys(const std::string& src, const ProtectKeyList& keys)
      : pp(mgr, diag, KeysConfig(keys)) {
    text = pp.Preprocess(mgr.AddFile("<test>", src));
  }

  static PreprocConfig KeysConfig(const ProtectKeyList& keys) {
    PreprocConfig config;
    config.protect_keys = keys;
    return config;
  }

  // The identifier the reading would regenerate a digest under, reported beside
  // whether a default put it there.
  ProtectKeywordValue Identifier() const {
    return ProtectDigestMethodInEffect(pp.ProtectKeywords());
  }

  // How the digest block the reading last reached compared against the block it
  // follows.
  ProtectDigestCheck DigestCheck() const { return pp.LastDigestBlockCheck(); }
};

// -- Table 34-4 -------------------------------------------------------------

// §34.5.21.2: the standard specifies the values in Table 34-4. Four rows, in
// the order the table lists them.
TEST(ProtectDigestMethodTable, TheTableIsFourIdentifiersInTheOrderListed) {
  std::span<const ProtectDigestAlgorithm> rows = ProtectDigestAlgorithms();
  ASSERT_EQ(rows.size(), 4U);
  EXPECT_EQ(rows[0].identifier, "sha1");
  EXPECT_EQ(rows[1].identifier, "md5");
  EXPECT_EQ(rows[2].identifier, "md2");
  EXPECT_EQ(rows[3].identifier, "ripemd-160");
}

// The required/optional column is part of what the table says. These two rows
// name algorithms any tool can be handed a digest under.
TEST(ProtectDigestMethodTable, TheTableRequiresTheFirstTwoIdentifiers) {
  EXPECT_TRUE(IsRequiredProtectDigestAlgorithm("sha1"));
  EXPECT_TRUE(IsRequiredProtectDigestAlgorithm("md5"));
}

// The other two rows are tabulated without being required, which is a different
// state from not being tabulated at all: a text using one has assumed something
// about its reader rather than written something the standard does not name.
TEST(ProtectDigestMethodTable, TheOtherTwoAreTabulatedWithoutBeingRequired) {
  EXPECT_TRUE(IsProtectDigestAlgorithm("md2"));
  EXPECT_FALSE(IsRequiredProtectDigestAlgorithm("md2"));
  EXPECT_TRUE(IsProtectDigestAlgorithm("ripemd-160"));
  EXPECT_FALSE(IsRequiredProtectDigestAlgorithm("ripemd-160"));
}

// Each row names the published algorithm its identifier stands for, which is
// the column that makes the identifier mean one computation rather than
// whichever one a tool cared to attach the name to.
TEST(ProtectDigestMethodTable, EachRowNamesThePublishedAlgorithm) {
  std::span<const ProtectDigestAlgorithm> rows = ProtectDigestAlgorithms();
  ASSERT_EQ(rows.size(), 4U);
  EXPECT_NE(rows[0].algorithm.find("FIPS 180-2"), std::string_view::npos);
  EXPECT_NE(rows[1].algorithm.find("RFC 1321"), std::string_view::npos);
  EXPECT_NE(rows[2].algorithm.find("RFC 1319"), std::string_view::npos);
  EXPECT_NE(rows[3].algorithm.find("ISO/IEC 10118-3:2004"),
            std::string_view::npos);
}

// §34.5.21.2 leaves further identifiers to the implementation, so a value
// outside the table is one the standard does not decide rather than one it
// forbids. What the table answers is whether the standard named it.
TEST(ProtectDigestMethodTable, AnIdentifierOutsideTheTableIsNotTabulated) {
  EXPECT_FALSE(IsProtectDigestAlgorithm("sha256"));
}

// Being in the table and being computable here are two questions, and the
// optional column is why. An identifier this run cannot compute is still one
// the standard named, so a reading that answered both alike would take a
// tabulated identifier for one it could produce a digest under.
TEST(ProtectDigestMethodTable, BeingTabulatedIsNotBeingProvided) {
  EXPECT_TRUE(IsProtectDigestAlgorithm("md2"));
  EXPECT_FALSE(ProtectDigestIsAvailable("md2"));
  EXPECT_TRUE(ProtectDigestIsAvailable("sha1"));
}

// §34.5.21.2 settles no default, so what stands where a text wrote nothing is
// this implementation's choice. It has to be an identifier the table requires:
// a digest is written to be recomputed elsewhere, and a digest under an
// identifier the reader need not provide is one the reader cannot check.
TEST(ProtectDigestMethodTable, TheDefaultIsAnIdentifierTheTableRequires) {
  EXPECT_TRUE(IsRequiredProtectDigestAlgorithm(kDefaultDigestMethod));
}

// -- The identifier decides the computation ---------------------------------

// §34.5.21.2: the identifier specifies the algorithm the digest is generated
// with. Two identifiers are two algorithms, so one text digested under each
// gives two values.
TEST(ProtectDigestMethodEncryptionInput, TwoIdentifiersGiveTwoDigests) {
  std::string under_sha1;
  std::string under_md5;
  ASSERT_TRUE(ProtectMessageDigest(kDigestedText, "sha1", &under_sha1));
  ASSERT_TRUE(ProtectMessageDigest(kDigestedText, "md5", &under_md5));
  EXPECT_NE(under_sha1, under_md5);
}

// An identifier this implementation provides no algorithm for produces no
// digest rather than a digest under whichever algorithm was nearest to hand.
// The value handed in is left as it stands, there being no result to give.
TEST(ProtectDigestMethodEncryptionInput,
     AnIdentifierWithNoAlgorithmHereGivesNothing) {
  std::string digest = "what the caller brought";
  EXPECT_FALSE(ProtectMessageDigest(kDigestedText, "md2", &digest));
  EXPECT_EQ(digest, "what the caller brought");
}

// The block an encrypting run writes for a digest is the identifier's digest:
// one text written out under two identifiers gives two blocks. Without this the
// identifier could be recorded everywhere it is written and used nowhere.
TEST(ProtectDigestMethodEncryptionInput,
     TheBlockWrittenIsTheIdentifiersDigest) {
  ProtectDigestBlockPolicy policy;
  policy.requested = true;
  policy.key = std::string(kDigestKey);
  policy.method = "sha1";
  std::string under_sha1 = ProtectDigestBlockDirectives(
      kDigestedText, policy, DefaultProtectEncoding());
  policy.method = "md5";
  std::string under_md5 = ProtectDigestBlockDirectives(
      kDigestedText, policy, DefaultProtectEncoding());
  EXPECT_FALSE(under_sha1.empty());
  EXPECT_NE(under_sha1, under_md5);
}

// An identifier naming no algorithm available here leaves no digest block at
// all, rather than one written short or written under another algorithm: a
// reader recomputing such a digest would find it disagreeing with a block that
// arrived exactly as it was sealed.
TEST(ProtectDigestMethodEncryptionInput,
     AnIdentifierWithNoAlgorithmHereWritesNoBlock) {
  ProtectDigestBlockPolicy policy;
  policy.requested = true;
  policy.key = std::string(kDigestKey);
  policy.method = "md2";
  EXPECT_EQ(ProtectDigestBlockDirectives(kDigestedText, policy,
                                         DefaultProtectEncoding()),
            "");
}

// -- Unchanged in the output file -------------------------------------------

// §34.5.21.2: the identifier is unchanged in the output file. An envelope
// carrying no key block is not signed, so the exception does not arise and the
// identifier stands in the clear, spelled as the region spelled it.
TEST(ProtectDigestMethodEncryptionOutput, AnUnsignedEnvelopeStatesItAsWritten) {
  std::string envelope = UnsignedEnvelope(Writes(kIdentifierKeyword, kStated));
  std::string directive = "`pragma protect digest_method=\"";
  directive.append(kStated).append("\"");
  EXPECT_NE(envelope.find(directive), std::string::npos) << envelope;
}

// A region that stated no identifier has none to leave unchanged, so the
// envelope states none. Without this the case above would hold of a tool that
// wrote the keyword into every envelope it produced.
TEST(ProtectDigestMethodEncryptionOutput, ARegionStatingNoneGetsNone) {
  std::string envelope = UnsignedEnvelope("");
  EXPECT_EQ(envelope.find(kIdentifierKeyword), std::string::npos) << envelope;
}

// §34.5.21.2's exception: where a digital signature is used the identifier is
// encrypted with the key_method and placed in a key_block, so it stands nowhere
// in the clear. A region whose keys travel in key blocks of its own is that
// case.
TEST(ProtectDigestMethodEncryptionOutput, ASignedEnvelopeKeepsItOutOfTheClear) {
  std::string envelope = SignedEnvelope(Writes(kIdentifierKeyword, kStated));
  EXPECT_EQ(envelope.find(kIdentifierKeyword), std::string::npos) << envelope;
}

// -- What a reading generates the digest under ------------------------------

// The cases below read the identifier a reading was left holding, and so stop
// where the envelope does: §34.5.31.2 has the reset this tool writes beneath an
// envelope restore every protect pragma keyword, so a reading carried past it
// reports the default whether the key block was opened or not.

// The other half of the exception: the identifier the signed envelope kept out
// of the clear is inside the key block, so a reader that opened the block has
// it in effect. The value comes back as the region wrote it, without the
// quotation marks §22.5.1 spelled it with.
TEST(ProtectDigestMethodDecryptionInput, TheKeyBlockYieldsTheIdentifier) {
  ReadUnderKeys run(
      ThroughEndProtected(SignedEnvelope(Writes(kIdentifierKeyword, kStated))),
      TheBlockKey());
  EXPECT_FALSE(run.diag.HasErrors()) << run.text;
  EXPECT_FALSE(run.Identifier().defaulted);
  EXPECT_EQ(run.Identifier().value, kStated);
}

// A reader that never opened the block never reaches the identifier, which is
// what makes the case above about the block rather than about a value standing
// in the envelope's clear text. The reading is left at the default.
TEST(ProtectDigestMethodDecryptionInput, AReaderWithoutTheKeyReachesNone) {
  ReadUnderKeys run(
      ThroughEndProtected(SignedEnvelope(Writes(kIdentifierKeyword, kStated))),
      ProtectKeyList());
  EXPECT_TRUE(run.Identifier().defaulted);
}

// §34.5.21.2: on the way back the identifier indicates the algorithm the digest
// is generated from the data block with. The digest of a block sealed under one
// identifier and regenerated under the same one agrees with what the envelope
// carried.
TEST(ProtectDigestMethodDecryptionInput, TheDigestAgreesUnderTheStatedOne) {
  ReadUnderKeys run(SignedEnvelope(Writes(kIdentifierKeyword, kStated)),
                    TheBlockKey());
  EXPECT_EQ(run.DigestCheck(), ProtectDigestCheck::kMatched);
}

// The same region with no identifier stated, read by the same tool: the digest
// is generated under the default at both ends and agrees as well. Two readings
// that agree for two different identifiers are what say the identifier was
// carried rather than that one algorithm was used throughout.
TEST(ProtectDigestMethodDecryptionInput, TheDigestAgreesUnderTheDefaultToo) {
  ReadUnderKeys run(ThroughEndProtected(SignedEnvelope("")), TheBlockKey());
  EXPECT_TRUE(run.Identifier().defaulted);
  EXPECT_EQ(run.DigestCheck(), ProtectDigestCheck::kMatched);
}

}  // namespace
