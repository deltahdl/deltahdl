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

#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_digest_key.h"
#include "preprocessor/protect_keywords.h"

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

}  // namespace
