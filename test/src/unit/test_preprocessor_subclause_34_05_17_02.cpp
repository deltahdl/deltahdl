// §34.5.17.2 digest_key_method, Description.
//
// The subclause says four things about the keyword §34.5.17.1 spells.
//
//   Written in an encrypting tool's input, it states the encryption algorithm
//   that shall encrypt the digest_block contents that follow.
//
//   The values that identify an algorithm here are the ones written for the
//   keyword naming the cipher a region's data are under. The subclause
//   tabulates none of its own and sends the reader to that table.
//
//   Where the input states none, the default is the current value of that other
//   keyword.
//
//   It is unchanged in the output file, except under a digital signature, and
//   on the way back it states the algorithm the digest_block is decrypted with.
//
// The middle two are what a run can be held to and are what this file states.
// They are carried by ProtectDigestKeyMethodInEffect and
// IsProtectDigestKeyMethodIdentifier (src/preprocessor/protect_digest_key.h),
// and the identifier set is Table 34-3 as §34.5.11.2 writes it, shared rather
// than copied.
//
// The fourth is stated here as well, at the one place a run can be held to it.
// §34.5.17.2 sends the identifier into the key_block where a digital signature
// is used, so a signed envelope states it nowhere a case can read. An envelope
// sealed under the author's own key carries no key_block, and
// AppendClearDigestNames in src/preprocessor/protect_envelope_output.cpp writes
// the identifier in the clear there, so that is where the cases below
// EnvelopeStating read it.
//
// What those cases read it for is the spelling. §34.5.17.1 spells the
// expression `digest_key_method = <string>`, and §22.5.1 makes a parenthesized
// pragma_value a list of further pragma expressions rather than the one written
// thing a string is, so a list names no cipher and the envelope states none.
// Issue #3277 is the defect: TakeMethodKeywords in
// src/preprocessor/protect_region_lines.cpp read the value through
// KeywordValueOnLine, which hands back whatever stood against the '=',
// parentheses and all, and the list went onto the envelope where the cipher a
// reader opens the digest block with belongs.

#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_text_lines.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_digest_key.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

// What stands in effect for the digest's key cipher after reading `src`.
ProtectKeywordValue InEffectAfter(const std::string& src) {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp(mgr, diag, PreprocConfig{});
  pp.Preprocess(mgr.AddFile("<test>", src));
  EXPECT_FALSE(diag.HasErrors()) << src;
  return ProtectDigestKeyMethodInEffect(pp.ProtectKeywords());
}

std::string StatesDataMethod(std::string_view value) {
  std::string text = "`pragma protect data_method=\"";
  text.append(value).append("\"\n");
  return text;
}

std::string StatesDigestKeyMethod(std::string_view value) {
  std::string text = "`pragma protect digest_key_method=\"";
  text.append(value).append("\"\n");
  return text;
}

// §34.5.17.2: the algorithm a text states for the digest's key is what stands
// in effect, and it stands as something stated rather than defaulted.
TEST(ProtectDigestKeyMethodDescription, TheStatedAlgorithmStandsInEffect) {
  ProtectKeywordValue method = InEffectAfter(StatesDigestKeyMethod("rsa"));
  EXPECT_FALSE(method.defaulted);
  EXPECT_EQ(method.value, "rsa");
}

// §34.5.17.2: where the input states none, the default is the current value of
// the keyword naming the cipher the region's data are under. The place is
// filled from there, and what fills it is reported as a default rather than as
// something the text stated.
TEST(ProtectDigestKeyMethodDescription, TheDataCipherFillsThePlaceLeftEmpty) {
  ProtectKeywordValue method = InEffectAfter(StatesDataMethod("des-cbc"));
  EXPECT_TRUE(method.defaulted);
  EXPECT_EQ(method.value, "des-cbc");
}

// The algorithm stated for the digest's key is not displaced by the one stated
// for the data, the default filling a place left empty rather than overriding
// what stands there. Without this the case above would hold of a reading that
// took the data's cipher whatever the text said.
TEST(ProtectDigestKeyMethodDescription,
     TheDataCipherDoesNotDisplaceAStatedOne) {
  std::string src = StatesDataMethod("des-cbc");
  src += StatesDigestKeyMethod("rsa");
  ProtectKeywordValue method = InEffectAfter(src);
  EXPECT_FALSE(method.defaulted);
  EXPECT_EQ(method.value, "rsa");
}

// A text stating neither leaves nothing to open a digest with, which is a
// different state from stating one: the default fills the place from the data's
// cipher, and there is no data cipher to fill it from.
TEST(ProtectDigestKeyMethodDescription, StatingNeitherLeavesNoCipher) {
  ProtectKeywordValue method = InEffectAfter("`pragma protect author=\"a\"\n");
  EXPECT_TRUE(method.defaulted);
  EXPECT_TRUE(method.value.empty());
}

// §34.5.17.2: the values are the ones written for the other method keyword.
// Table 34-3's required identifier and one of its optional ones are admitted
// here because they are admitted there, and the table is consulted rather than
// copied.
TEST(ProtectDigestKeyMethodDescription, TheValuesAreTheOtherKeywordsValues) {
  EXPECT_TRUE(IsProtectDigestKeyMethodIdentifier("des-cbc"));
  EXPECT_TRUE(IsProtectDigestKeyMethodIdentifier("aes256-cbc"));
  EXPECT_FALSE(IsProtectDigestKeyMethodIdentifier("a-cipher-nobody-tabulated"));
}

// -- Unchanged in the output file -------------------------------------------

// The design a region seals. It is checked gone from every envelope below,
// because a region nothing sealed comes back as its own source text and that
// text writes the very directive these cases read for.
constexpr std::string_view kSealedCore = "module ferrite_m; endmodule\n";

// The key an author hands the encrypting half directly. A region encrypted
// under it carries no key_block, which is what keeps §34.5.17.2's exception for
// a digital signature out of the way.
constexpr std::string_view kAuthorsExchangeKey = "the-authors-own-exchange-key";

// A cipher Table 34-3 tabulates. §34.5.17.2 gives this keyword no values of its
// own and sends the reader to that table, so a row of it is a value here. It is
// not the row the table requires, so it is not what a region naming nothing
// would have been read under either.
constexpr std::string_view kTabulatedCipher = "twofish192-cbc";

// A pragma_value written in the parenthesized spelling §22.5.1 defines. Its
// subkeywords are names §34.4 tabulates nowhere, so what the list says is
// beside the point and its spelling is the whole of what the cases below read.
constexpr std::string_view kCipherList = "(mode=\"ofb\", rounds=\"16\")";

// The keyword with `value` written against it as it stands here.
// StatesDigestKeyMethod above puts quotation marks around what it is given, and
// a list inside quotation marks is a string rather than a list.
std::string StatesDigestKeyMethodAsSpelled(std::string_view value) {
  std::string text = "`pragma protect digest_key_method=";
  text.append(value).append("\n");
  return text;
}

// The envelope this tool writes for a region stating `described` about itself,
// checked on the way out to be one that sealed its design under a key of the
// author's rather than under a block of its own.
std::string EnvelopeStating(const std::string& described) {
  std::string region = "`pragma protect begin\n";
  region.append(described).append(kSealedCore);
  region.append("`pragma protect end\n");
  std::string envelope = EncryptEnvelopes(region, kAuthorsExchangeKey);
  EXPECT_FALSE(Holds(envelope, kSealedCore)) << envelope;
  EXPECT_FALSE(Holds(envelope, "key_block")) << envelope;
  return envelope;
}

// §34.5.17.1 spells the expression with a string, and §22.5.1 makes a
// parenthesized pragma_value a list of further pragma expressions rather than
// one written thing, so a list names no cipher and there is none to leave
// unchanged. Issue #3277 is the defect the case was written for: the list was
// written onto the envelope, where a reader looking for the cipher its digest
// block is under would have found an expression naming no cipher at all.
TEST(ProtectDigestKeyMethodEncryptionOutput, AListNamesNoCipherOnTheEnvelope) {
  EXPECT_FALSE(
      Holds(EnvelopeStating(StatesDigestKeyMethodAsSpelled(kCipherList)),
            "digest_key_method"));
}

// The control beside it: §34.5.17.2 has the identifier unchanged in the output
// file, so the spelling §34.5.17.1 does define reaches the envelope as the
// region wrote it. Without this the case above would hold of a tool that wrote
// no digest_key_method directive whatever a region named.
TEST(ProtectDigestKeyMethodEncryptionOutput,
     AStringNamesTheCipherTheEnvelopeStates) {
  EXPECT_TRUE(Holds(EnvelopeStating(StatesDigestKeyMethod(kTabulatedCipher)),
                    StatesDigestKeyMethod(kTabulatedCipher)));
}

// A list written after a string names no cipher, so the cipher the string named
// still stands and that string is what the envelope states. An expression
// naming no cipher has no standing to take away the one named before it, and
// the list itself reaches the envelope nowhere.
TEST(ProtectDigestKeyMethodEncryptionOutput,
     AListLeavesTheStringBeforeItStanding) {
  std::string envelope =
      EnvelopeStating(StatesDigestKeyMethod(kTabulatedCipher) +
                      StatesDigestKeyMethodAsSpelled(kCipherList));
  EXPECT_TRUE(Holds(envelope, StatesDigestKeyMethod(kTabulatedCipher)))
      << envelope;
  EXPECT_FALSE(Holds(envelope, kCipherList)) << envelope;
}

}  // namespace
