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

TEST(ProtectDigestKeyMethodDescription, TheStatedAlgorithmStandsInEffect) {
  ProtectKeywordValue method = InEffectAfter(StatesDigestKeyMethod("rsa"));
  EXPECT_FALSE(method.defaulted);
  EXPECT_EQ(method.value, "rsa");
}

TEST(ProtectDigestKeyMethodDescription, TheDataCipherFillsThePlaceLeftEmpty) {
  ProtectKeywordValue method = InEffectAfter(StatesDataMethod("des-cbc"));
  EXPECT_TRUE(method.defaulted);
  EXPECT_EQ(method.value, "des-cbc");
}

TEST(ProtectDigestKeyMethodDescription, AnEmptyStringLeavesThePlaceEmpty) {
  std::string src = StatesDataMethod("des-cbc");
  src += StatesDigestKeyMethod("");
  ProtectKeywordValue method = InEffectAfter(src);
  EXPECT_TRUE(method.defaulted);
  EXPECT_EQ(method.value, "des-cbc");
}

TEST(ProtectDigestKeyMethodDescription,
     TheDataCipherDoesNotDisplaceAStatedOne) {
  std::string src = StatesDataMethod("des-cbc");
  src += StatesDigestKeyMethod("rsa");
  ProtectKeywordValue method = InEffectAfter(src);
  EXPECT_FALSE(method.defaulted);
  EXPECT_EQ(method.value, "rsa");
}

TEST(ProtectDigestKeyMethodDescription, StatingNeitherLeavesNoCipher) {
  ProtectKeywordValue method = InEffectAfter("`pragma protect author=\"a\"\n");
  EXPECT_TRUE(method.defaulted);
  EXPECT_TRUE(method.value.empty());
}

TEST(ProtectDigestKeyMethodDescription, TheValuesAreTheOtherKeywordsValues) {
  EXPECT_TRUE(IsProtectDigestKeyMethodIdentifier("des-cbc"));
  EXPECT_TRUE(IsProtectDigestKeyMethodIdentifier("aes256-cbc"));
  EXPECT_FALSE(IsProtectDigestKeyMethodIdentifier("a-cipher-nobody-tabulated"));
}

constexpr std::string_view kSealedCore = "module ferrite_m; endmodule\n";

constexpr std::string_view kAuthorsExchangeKey = "the-authors-own-exchange-key";

constexpr std::string_view kTabulatedCipher = "twofish192-cbc";

constexpr std::string_view kCipherList = "(mode=\"ofb\", rounds=\"16\")";

std::string StatesDigestKeyMethodAsSpelled(std::string_view value) {
  std::string text = "`pragma protect digest_key_method=";
  text.append(value).append("\n");
  return text;
}

std::string EnvelopeStating(const std::string& described) {
  std::string region = "`pragma protect begin\n";
  region.append(described).append(kSealedCore);
  region.append("`pragma protect end\n");
  std::string envelope = EncryptEnvelopes(region, kAuthorsExchangeKey);
  EXPECT_FALSE(Holds(envelope, kSealedCore)) << envelope;
  EXPECT_FALSE(Holds(envelope, "key_block")) << envelope;
  return envelope;
}

TEST(ProtectDigestKeyMethodEncryptionOutput, AListNamesNoCipherOnTheEnvelope) {
  EXPECT_FALSE(
      Holds(EnvelopeStating(StatesDigestKeyMethodAsSpelled(kCipherList)),
            "digest_key_method"));
}

TEST(ProtectDigestKeyMethodEncryptionOutput,
     AStringNamesTheCipherTheEnvelopeStates) {
  EXPECT_TRUE(Holds(EnvelopeStating(StatesDigestKeyMethod(kTabulatedCipher)),
                    StatesDigestKeyMethod(kTabulatedCipher)));
}

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
