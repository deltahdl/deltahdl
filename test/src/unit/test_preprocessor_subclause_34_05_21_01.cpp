#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_preprocessor.h"
#include "helpers_protect_keyword_value.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_digest.h"
#include "preprocessor/protect_keywords.h"

using namespace delta;

struct ProtectDigestMethodSyntaxTest : ::testing::Test {
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

TEST_F(ProtectDigestMethodSyntaxTest, PragmaProtectDigestMethodConsumed) {
  auto result = Preprocess("`pragma protect digest_method = \"sha256\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("sha256"), std::string::npos);
}

TEST_F(ProtectDigestMethodSyntaxTest,
       DigestMethodDirectiveStrippedSurroundingTextKept) {
  auto result = Preprocess(
      "module m;\n`pragma protect digest_method = \"sha256\"\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

TEST_F(ProtectDigestMethodSyntaxTest,
       DigestMethodStringArgumentWithSpacesConsumed) {
  auto result =
      Preprocess("`pragma protect digest_method = \"sha 512 variant\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("sha 512 variant"), std::string::npos);
}

constexpr std::string_view kStatedMethod = kMd5DigestMethod;
static_assert(kStatedMethod != kDefaultDigestMethod,
              "a case stating the identifier the default already supplies "
              "passes whether the expression was read or not");

ProtectKeywordValue MethodAfter(const std::string& src) {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp(mgr, diag, PreprocConfig{});
  pp.Preprocess(mgr.AddFile("<test>", src));
  EXPECT_FALSE(diag.HasErrors()) << src;
  return ProtectDigestMethodInEffect(pp.ProtectKeywords());
}

std::string StatesMethod(std::string_view value) {
  std::string directive = "`pragma protect digest_method=";
  directive.append(value).append("\n");
  return directive;
}

TEST(ProtectDigestMethodSyntax, TheStringAgainstTheKeywordStatesTheAlgorithm) {
  EXPECT_EQ(MethodAfter(StatesMethod(InQuotes(kStatedMethod))).value,
            kStatedMethod);
}

TEST(ProtectDigestMethodSyntax, AStatedAlgorithmIsNotADefaultedOne) {
  EXPECT_FALSE(MethodAfter(StatesMethod(InQuotes(kStatedMethod))).defaulted);
}

TEST(ProtectDigestMethodSyntax, ABareIdentifierIsOneWrittenThingToo) {
  EXPECT_EQ(MethodAfter(StatesMethod(kStatedMethod)).value, kStatedMethod);
}

TEST(ProtectDigestMethodSyntax, TheWholeOfASpaceBearingStringStandsInEffect) {
  EXPECT_EQ(MethodAfter(StatesMethod(InQuotes("sha 512 variant"))).value,
            "sha 512 variant");
}

TEST(ProtectDigestMethodSyntax, AListLeavesTheAlgorithmAlreadyStated) {
  std::string src = StatesMethod(InQuotes(kStatedMethod));
  src += StatesMethod("(rounds=\"64\")");
  EXPECT_EQ(MethodAfter(src).value, kStatedMethod);
}

TEST(ProtectDigestMethodSyntax, AListOnItsOwnStatesNoAlgorithm) {
  EXPECT_TRUE(MethodAfter(StatesMethod("(rounds=\"64\")")).defaulted);
}

TEST(ProtectDigestMethodSyntax, TheKeywordStandingAloneStatesNoAlgorithm) {
  ProtectKeywordValue in_effect =
      MethodAfter("`pragma protect digest_method\n");
  EXPECT_TRUE(in_effect.defaulted);
  EXPECT_EQ(in_effect.value, kDefaultDigestMethod);
}

TEST(ProtectDigestMethodSyntax, AnEmptyStringStatesNoAlgorithm) {
  ProtectKeywordValue in_effect = MethodAfter(StatesMethod("\"\""));
  EXPECT_TRUE(in_effect.defaulted);
  EXPECT_EQ(in_effect.value, kDefaultDigestMethod);
}

TEST(ProtectDigestMethodSyntax, AnEqualsWithNoValueAfterItIsNoExpression) {
  PreprocFixture f;
  Preprocess("`pragma protect digest_method =\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

TEST(ProtectDigestMethodSyntax, ANameMerelyOpeningWithTheKeywordIsNotIt) {
  std::string src = "`pragma protect digest_method_of_theirs=";
  src.append(InQuotes(kStatedMethod)).append("\n");
  EXPECT_TRUE(MethodAfter(src).defaulted);
}

}  // namespace
