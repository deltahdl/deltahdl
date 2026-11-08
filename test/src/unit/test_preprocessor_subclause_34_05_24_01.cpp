#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_preprocessor.h"
#include "helpers_protect_keys.h"
#include "helpers_protect_keyword_value.h"
#include "helpers_reported_error.h"
#include "helpers_text_lines.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_key_method.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

struct ProtectKeyMethodSyntaxTest : ::testing::Test {
 protected:
  std::string Preprocess(const std::string& src) {
    auto fid = mgr_.AddFile("<test>", src);
    Preprocessor pp(mgr_, diag_, config_);
    return pp.Preprocess(fid);
  }

  SourceManager mgr_;
  DiagEngine diag_{mgr_};
  PreprocConfig config_;
};

namespace {

TEST_F(ProtectKeyMethodSyntaxTest, PragmaProtectKeyMethodConsumed) {
  auto result = Preprocess("`pragma protect key_method = \"rsa\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("rsa"), std::string::npos);
}

TEST_F(ProtectKeyMethodSyntaxTest,
       KeyMethodDirectiveStrippedSurroundingTextKept) {
  auto result = Preprocess(
      "module m;\n`pragma protect key_method = \"rsa\"\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

constexpr std::string_view kStated = "des-cbc";

constexpr std::string_view kIdentifierStated = "rsa";

std::string StatesMethod(std::string_view value) {
  std::string directive = "`pragma protect key_method=";
  directive.append(value).append("\n");
  return directive;
}

constexpr std::string_view kSealedDesign = "module sealed_m; endmodule\n";

ProtectKeywordValue MethodAfter(const std::string& src) {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp(mgr, diag, PreprocConfig{});
  pp.Preprocess(mgr.AddFile("<test>", src));
  EXPECT_FALSE(diag.HasErrors()) << src;
  return ProtectKeyMethodInEffect(pp.ProtectKeywords());
}

constexpr std::string_view kBlockProvider = "orrery-labs";
constexpr std::string_view kBlockKeyName = "wrapping-2029";
constexpr std::string_view kBlockProviderKey = "orrery-labs-wrapping-key";

ProtectKeyList TheBlockProvidersKey() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kBlockProvider, kBlockKeyName, kBlockProviderKey));
  return keys;
}

std::string SignedRegionStating(const std::string& described) {
  std::string region = "`pragma protect begin\n";
  region.append("`pragma protect key_keyowner=\"")
      .append(kBlockProvider)
      .append("\"\n");
  region.append("`pragma protect key_keyname=\"")
      .append(kBlockKeyName)
      .append("\"\n");
  region.append("`pragma protect data_keyname=\"design-2029\"\n");
  region.append(described).append(kSealedDesign);
  region.append("`pragma protect end\n");
  return region;
}

TEST(ProtectKeyMethodSyntax, TheStringAgainstTheKeywordStatesTheAlgorithm) {
  EXPECT_EQ(MethodAfter(StatesMethod(InQuotes(kStated))).value, kStated);
}

TEST(ProtectKeyMethodSyntax, AStatedAlgorithmIsNotADefaultedOne) {
  EXPECT_FALSE(MethodAfter(StatesMethod(InQuotes(kStated))).defaulted);
}

TEST(ProtectKeyMethodSyntax, ABareIdentifierIsOneWrittenThingToo) {
  EXPECT_EQ(MethodAfter(StatesMethod(kIdentifierStated)).value,
            kIdentifierStated);
}

TEST(ProtectKeyMethodSyntax, TheWholeOfASpaceBearingStringStandsInEffect) {
  EXPECT_EQ(MethodAfter(StatesMethod(InQuotes("des cbc variant"))).value,
            "des cbc variant");
}

TEST(ProtectKeyMethodSyntax, TheDataCipherDoesNotFillThePlaceLeftEmpty) {
  ProtectKeywordValue method =
      MethodAfter("`pragma protect data_method=\"des-cbc\"\n");
  EXPECT_TRUE(method.defaulted);
  EXPECT_TRUE(method.value.empty());
}

TEST(ProtectKeyMethodSyntax, AListLeavesTheAlgorithmAlreadyStated) {
  std::string src = StatesMethod(InQuotes(kStated));
  src += StatesMethod("(padding=\"pss\")");
  EXPECT_EQ(MethodAfter(src).value, kStated);
}

TEST(ProtectKeyMethodSyntax, AListOnItsOwnStatesNoAlgorithm) {
  ProtectKeywordValue method = MethodAfter(StatesMethod("(padding=\"pss\")"));
  EXPECT_TRUE(method.defaulted);
  EXPECT_TRUE(method.value.empty());
}

TEST(ProtectKeyMethodSyntax, TheKeywordStandingAloneStatesNoAlgorithm) {
  ProtectKeywordValue method = MethodAfter("`pragma protect key_method\n");
  EXPECT_TRUE(method.defaulted);
  EXPECT_TRUE(method.value.empty());
}

TEST(ProtectKeyMethodSyntax, AnEmptyStringStatesNoAlgorithm) {
  ProtectKeywordValue method = MethodAfter(StatesMethod("\"\""));
  EXPECT_TRUE(method.defaulted);
  EXPECT_TRUE(method.value.empty());
}

TEST(ProtectKeyMethodSyntax, AnEqualsWithNoValueAfterItIsNoExpression) {
  PreprocFixture f;
  Preprocess("`pragma protect key_method =\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

TEST(ProtectKeyMethodSyntax, ANameMerelyOpeningWithTheKeywordIsNotIt) {
  EXPECT_TRUE(
      MethodAfter("`pragma protect key_methods=\"des-cbc\"\n").defaulted);
}

TEST(ProtectKeyMethodSyntax, TheAlgorithmStatedInThatSpellingIsHonoured) {
  SourceManager mgr;
  DiagEngine diag{mgr};
  std::string src = SignedRegionStating(StatesMethod(InQuotes(kStated)));
  std::string envelope = EncryptEnvelopes(src, {}, TheBlockProvidersKey(),
                                          &diag, mgr.AddFile("<test>", src));
  EXPECT_FALSE(diag.HasErrors()) << envelope;
  EXPECT_FALSE(Holds(envelope, kSealedDesign)) << envelope;
  std::string stated = "`pragma protect key_method=\"";
  stated.append(kStated).append("\"");
  EXPECT_TRUE(Holds(envelope, stated)) << envelope;
}

TEST(ProtectKeyMethodSyntax, AListAsksForNoAlgorithmAndIsRefusedNothing) {
  SourceManager mgr;
  DiagEngine diag{mgr};
  std::string src = SignedRegionStating(StatesMethod("(padding=\"pss\")"));
  EncryptEnvelopes(src, {}, TheBlockProvidersKey(), &diag,
                   mgr.AddFile("<test>", src));
  EXPECT_FALSE(diag.HasErrors());
}

}  // namespace
