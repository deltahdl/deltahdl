// §34.5.22 digest_block, Description.
//
// §34.5.22.2 says these things about the keyword §34.5.22.1 spells.
//
//   A digest_block found in an input file, other than in a begin_protected -
//   end_protected block, is a request to the encrypting tool to generate a
//   message digest in the output file.
//
//   The digest is what says the encrypted data have not been modified. It is
//   generated under the algorithm digest_method specifies and encrypted under
//   digest_key_method with the key digest_keyname, digest_public_key and
//   digest_decrypt_key specify. Where no digest_key_method was specified, the
//   key the current data_method is under is used.
//
//   Where a CBC algorithm requiring an initialization vector is in force, the
//   IV cipher-block is prepended to the encrypted digest before the encoding
//   is applied.
//
//   The digest is encoded under the current encoding pragma expression and
//   written on the line following the digest_block expression. One is
//   generated for each key_block and each data_block generated, and each
//   immediately follows the block it refers to.
//
//   A consuming tool decrypts the data, generates a digest from what it
//   recovered, decrypts the digest the block carries, and compares the two. A
//   disagreement says that either the digest_block or the encrypted data was
//   altered since the data were encrypted.
//
// The middle three are what this file states, the first and the last of them
// having been settled elsewhere. Which algorithm generates the digest is
// §34.5.21.2's and is stated in test_preprocessor_subclause_34_05_21_02.cpp;
// which key encrypts it is §34.5.16's, §34.5.18.2's, §34.5.19.2's and
// §34.5.20.2's, each stated in its own file; which spelling of the keyword
// announces a line is §34.5.22.1's and is stated in
// test_preprocessor_subclause_34_05_22_01.cpp. What is left here is the
// arrangement of blocks in an envelope, the digest's own encoded value, and
// what a reading does when the two digests disagree.
//
// The initialization vector never arises. §34.5.22.2 states the rule for a CBC
// algorithm requiring one, and the cipher this implementation encrypts a block
// under is kDataMethod in src/preprocessor/protect_envelope_output.h, a keyed
// stream named as this implementation's own rather than as one the standard
// reserves. There is no cipher-block to prepend and none to strip, so what the
// block carries is the digest and nothing ahead of it, which is what the case
// reading a digest back out states.
//
// One name in §34.5.22.2 is worth writing down. Where the subclause lists the
// expressions specifying the key, it writes digest_key_keyowner, and §34.4
// tabulates no such keyword: the name it tabulates is digest_keyowner, which
// §34.5.16 defines. This file reads the list as naming that one.

#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_protect_encoding.h"
#include "helpers_protect_keys.h"
#include "helpers_reported_error.h"
#include "helpers_text_lines.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_digest.h"
#include "preprocessor/protect_digest_block.h"
#include "preprocessor/protect_encoding.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

// The two entities a region designates to open its keys, each holding one key.
// A region reaching two of them is written two key blocks, which is what makes
// the arrangement §34.5.22.2 describes something a case can count.
constexpr std::string_view kFirstProvider = "meridian-trust";
constexpr std::string_view kFirstKeyName = "wrapping-2026";
constexpr std::string_view kFirstKey = "meridian-trust-wrapping-key";
constexpr std::string_view kSecondProvider = "cerulean-vault";
constexpr std::string_view kSecondKeyName = "wrapping-2027";
constexpr std::string_view kSecondKey = "cerulean-vault-wrapping-key";

// The name a region gives the key its data are under. A name with no key held
// for it is what sends the region to key blocks rather than to a key of its
// author's.
constexpr std::string_view kDataKeyName = "design-2026";

std::string Writes(std::string_view keyword, std::string_view value) {
  std::string text = "`pragma protect ";
  text.append(keyword).append("=\"").append(value).append("\"\n");
  return text;
}

// One designation of a key block's key: the entity that provided it, the name
// the region's data are under, and the name picking the block's own key out of
// that entity's list. The data key name is written with each designation
// because the blocks of one region are held to agreeing about the data.
std::string Designates(std::string_view provider, std::string_view key_name) {
  std::string text = Writes("key_keyowner", provider);
  text.append(Writes("data_keyname", kDataKeyName));
  text.append(Writes("key_keyname", key_name));
  return text;
}

ProtectKeyList KeysOfBothProviders() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kFirstProvider, kFirstKeyName, kFirstKey));
  keys.Add(KeyOf(kSecondProvider, kSecondKeyName, kSecondKey));
  return keys;
}

// The envelope this tool writes for a region designating both entities and
// asking for `asked`, checked on the way out to be one that sealed its design.
std::string TwoKeyBlockEnvelope(std::string_view asked) {
  std::string described(asked);
  described.append(Designates(kFirstProvider, kFirstKeyName));
  described.append(Designates(kSecondProvider, kSecondKeyName));
  std::string envelope =
      EncryptEnvelopes(RegionHolding(described), {}, KeysOfBothProviders());
  EXPECT_FALSE(Holds(envelope, kEncodingSealedDesign)) << envelope;
  return envelope;
}

// Whether `line` opens a block by naming `keyword`.
//
// A block is looked for by the keyword the line starts with rather than by
// what follows it, because this tool does not write its three blocks alike:
// §34.5.27 has a key block announced by the keyword standing alone with the
// encoded value on the line beneath, which is how ProtectKeyBlockDirectives in
// src/preprocessor/protect_key_block.cpp writes one, while the data block goes
// out with its value written against the keyword. #3272 is that difference and
// what it costs a reader; what this file is about is the order the blocks
// stand in, which either spelling states equally well.
bool Opens(const std::string& line, std::string_view keyword) {
  std::string opening = "`pragma protect ";
  opening.append(keyword);
  return line.rfind(opening, 0) == 0;
}

// The blocks `envelope` carries, in the order it wrote them, each named by the
// keyword that opens it. §34.5.22 has a digest block stand for the block above
// it, so this is the arrangement the subclause asks to be read off an envelope.
std::vector<std::string> BlocksOf(const std::string& envelope) {
  std::vector<std::string> blocks;
  for (const std::string& line : AllLines(envelope)) {
    if (Opens(line, "key_block")) {
      blocks.emplace_back("key");
    } else if (Opens(line, "data_block")) {
      blocks.emplace_back("data");
    } else if (Opens(line, "digest_block")) {
      blocks.emplace_back("digest");
    }
  }
  return blocks;
}

// The coding scheme a text that stated none writes its blocks under.
ProtectEncoding TheScheme() { return DefaultProtectEncoding(); }

// The digest a reader regenerates from `cleartext`, under the algorithm a text
// that named none is read under.
std::string DigestOf(std::string_view cleartext) {
  std::string digest;
  EXPECT_TRUE(ProtectMessageDigest(cleartext, kDefaultDigestMethod, &digest))
      << cleartext;
  return digest;
}

// A data block as some other tool wrote it, holding `sealed` under the key an
// author hands both halves, with the count §34.5.9 puts ahead of it.
std::string DataBlockHolding(std::string_view sealed) {
  std::string text = ProtectEncodedValueDirective(
      TheScheme(), ProtectedRegionBlockSize(sealed));
  text.append("`pragma protect data_block=\"");
  text.append(EncryptProtectedRegion(sealed, kEncodingExchangeKey,
                                     TheScheme().enctype));
  text.append("\"\n");
  return text;
}

// A digest block vouching for `vouched_for`, written by the writer an
// encrypting run uses so that the case varies what the digest was computed
// over and nothing else about how it was written.
std::string DigestBlockVouchingFor(std::string_view vouched_for) {
  ProtectDigestBlockPolicy policy;
  policy.requested = true;
  policy.method = std::string(kDefaultDigestMethod);
  policy.key = std::string(kEncodingExchangeKey);
  return ProtectDigestBlockDirectives(vouched_for, policy, TheScheme());
}

// A decryption envelope as some other tool wrote it, holding `described`.
std::string EnvelopeCarrying(const std::string& described) {
  std::string text(kProtectedOpening);
  text.push_back('\n');
  text.append(described);
  text.append("`pragma protect end_protected\n");
  return text;
}

// A reading of `src` by a tool holding the key the blocks were sealed under,
// with the preprocessor kept alive so the comparison it made can be read off.
struct ReadEnvelope {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp{mgr, diag, HoldingTheKey()};
  std::string text;

  explicit ReadEnvelope(const std::string& src) {
    text = pp.Preprocess(mgr.AddFile("<test>", src));
  }

  ProtectDigestCheck DigestCheck() const { return pp.LastDigestBlockCheck(); }
};

// -- The request ------------------------------------------------------------

// §34.5.22.2: a digest_block found in an input file is a request to generate a
// digest in the output file. A region that made one is written an envelope
// carrying digests.
TEST(ProtectDigestBlockEncryptionInput, ARequestOutsideAProtectedBlockAsks) {
  EXPECT_TRUE(Holds(TwoKeyBlockEnvelope(kDigestBlockLine), kDigestBlockLine));
}

// The parenthesis in that sentence: an expression standing in a
// begin_protected - end_protected block is not the request. Such a block is a
// digest some other tool already produced, and reading it as a request would
// have one tool's finished envelope ask this one for work.
//
// The one writing of the keyword left in what comes back is that block's own,
// copied across untouched. A request would have added three more, one for each
// block the region below it was written.
TEST(ProtectDigestBlockEncryptionInput, ARequestInsideAProtectedBlockAsksNot) {
  std::string source = EnvelopeCarrying(std::string(kDigestBlockLine));
  source.append(RegionHolding(Designates(kFirstProvider, kFirstKeyName) +
                              Designates(kSecondProvider, kSecondKeyName)));
  std::string produced = EncryptEnvelopes(source, {}, KeysOfBothProviders());
  EXPECT_FALSE(Holds(produced, kEncodingSealedDesign)) << produced;
  EXPECT_EQ(TimesWritten(produced, kDigestBlockLine), 1U) << produced;
}

// -- One digest for each block ----------------------------------------------

// §34.5.22.2: a digest_block is generated for each key_block and each
// data_block generated, and each immediately follows the block it refers to.
// A region reaching two entities is written a key block for each and a data
// block for the design, so the envelope holds three blocks and three digests,
// alternating.
TEST(ProtectDigestBlockEncryptionOutput, EachBlockGeneratedGetsItsOwnDigest) {
  EXPECT_EQ(BlocksOf(TwoKeyBlockEnvelope(kDigestBlockLine)),
            (std::vector<std::string>{"key", "digest", "key", "digest", "data",
                                      "digest"}));
}

// The same region asking for no digest, which is what makes the case above
// about the request rather than about an envelope that always carries digests.
TEST(ProtectDigestBlockEncryptionOutput, ARegionAskingForNoneGetsNoneAtAll) {
  EXPECT_EQ(BlocksOf(TwoKeyBlockEnvelope("")),
            (std::vector<std::string>{"key", "key", "data"}));
}

// -- What the block carries -------------------------------------------------

// §34.5.22.2: the digest is encoded under the current encoding pragma
// expression and written on the line following the keyword. Reading that line
// back out of the scheme and out of the key leaves the digest of the region's
// own text, which is also what says nothing was prepended to it: §34.5.22.2
// puts an initialization vector ahead of the digest for a CBC algorithm that
// requires one, and the cipher here requires none.
TEST(ProtectDigestBlockEncryptionOutput, TheLineHoldsTheDigestAndNothingElse) {
  std::string envelope = EnvelopeAround(kDigestBlockLine);
  std::string carried;
  ASSERT_TRUE(DecodeProtectBlock(LineAfter(envelope, kDigestBlockLine),
                                 TheScheme().enctype, &carried))
      << envelope;
  std::string opened;
  ASSERT_TRUE(DecryptProtectedBlock(carried, kEncodingExchangeKey, &opened))
      << envelope;
  EXPECT_EQ(opened, DigestOf(RegionBody(kDigestBlockLine)));
}

// §34.5.9 has a count written ahead of each value an envelope carries, and a
// digest is a value of its own. The count ahead of the digest block is the
// digest's size and not the size of the block the digest stands for.
TEST(ProtectDigestBlockEncryptionOutput, TheDigestIsCountedAsAValueOfItsOwn) {
  std::string envelope = EnvelopeAround(kDigestBlockLine);
  EXPECT_TRUE(Holds(envelope, TheCountOf(ProtectedRegionBlockSize(
                                  DigestOf(RegionBody(kDigestBlockLine))))))
      << envelope;
}

// -- The comparison ---------------------------------------------------------

// §34.5.22.2: the consuming tool generates a digest from the data it recovered
// and compares it against the one the block carries. A digest computed over the
// text the block holds agrees with it.
TEST(ProtectDigestBlockDecryptionInput, ADigestOfTheBlockItFollowsAgrees) {
  ReadEnvelope run(
      EnvelopeCarrying(DataBlockHolding(kEncodingSealedDesign) +
                       DigestBlockVouchingFor(kEncodingSealedDesign)));
  EXPECT_FALSE(run.diag.HasErrors()) << run.text;
  EXPECT_EQ(run.DigestCheck(), ProtectDigestCheck::kMatched);
}

// §34.5.22.2: where the two disagree, either the digest_block or the encrypted
// data was altered after the data were encrypted. The envelope below carries a
// digest of some other text, which is the one thing separating it from the
// envelope above, and the reading reports it.
TEST(ProtectDigestBlockDecryptionInput, ADigestOfOtherTextIsReported) {
  std::string src = EnvelopeCarrying(DataBlockHolding(kEncodingSealedDesign) +
                                     DigestBlockVouchingFor(kSecondDesign));
  ReadEnvelope run(src);
  EXPECT_EQ(run.DigestCheck(), ProtectDigestCheck::kAltered);
  EXPECT_TRUE(ReportedError(run.diag.Diagnostics(),
                            "digest block disagrees with the block it follows",
                            LineHolding(src, LineAfter(src, kDigestBlockLine)),
                            "34.5.22"));
}

// §34.5.22.2 has the digest of a block written in the digest block immediately
// following it, so one block answers one digest. A second digest written after
// the same block follows no block of its own and is checked against nothing:
// it vouches for other text, and a reading that had checked it would report the
// disagreement the case above reports.
TEST(ProtectDigestBlockDecryptionInput, ASecondDigestFollowsNoBlockOfItsOwn) {
  ReadEnvelope run(
      EnvelopeCarrying(DataBlockHolding(kEncodingSealedDesign) +
                       DigestBlockVouchingFor(kEncodingSealedDesign) +
                       DigestBlockVouchingFor(kSecondDesign)));
  EXPECT_FALSE(run.diag.HasErrors()) << run.text;
  EXPECT_EQ(run.DigestCheck(), ProtectDigestCheck::kMatched);
}

// The block a digest can still be owed belongs to the envelope it was recovered
// from. An envelope that closed without a digest leaves nothing for the next
// envelope's digest to stand for, and a digest that reached across the boundary
// would vouch for a block it never followed -- here for text it agrees with, so
// a reading that reached it would report a match where nothing was checked.
TEST(ProtectDigestBlockDecryptionInput,
     ADigestReachesNoBlockOfAnotherEnvelope) {
  ReadEnvelope run(
      EnvelopeCarrying(DataBlockHolding(kEncodingSealedDesign)) +
      EnvelopeCarrying(DigestBlockVouchingFor(kEncodingSealedDesign)));
  EXPECT_EQ(run.DigestCheck(), ProtectDigestCheck::kNotChecked);
}

}  // namespace
