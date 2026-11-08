#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_digest_key.h"
#include "preprocessor/protect_keywords.h"

using namespace delta;

struct ProtectDigestKeyMethodSyntaxTest : ::testing::Test {
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

TEST_F(ProtectDigestKeyMethodSyntaxTest, PragmaProtectDigestKeyMethodConsumed) {
  auto result = Preprocess("`pragma protect digest_key_method = \"sha256\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("sha256"), std::string::npos);
}

TEST_F(ProtectDigestKeyMethodSyntaxTest,
       DigestKeyMethodDirectiveStrippedSurroundingTextKept) {
  auto result = Preprocess(
      "module m;\n`pragma protect digest_key_method = \"sha256\"\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

TEST_F(ProtectDigestKeyMethodSyntaxTest,
       DigestKeyMethodStringArgumentWithSpacesConsumed) {
  auto result =
      Preprocess("`pragma protect digest_key_method = \"rsa pss sha512\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("rsa pss sha512"), std::string::npos);
}

ProtectKeywordValue MethodAfter(const std::string& src) {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp(mgr, diag, PreprocConfig{});
  pp.Preprocess(mgr.AddFile("<test>", src));
  EXPECT_FALSE(diag.HasErrors()) << src;
  return pp.ProtectKeywords().ValueOf(kDigestKeyMethodKeyword);
}

std::string StatesKeyMethod(std::string_view value) {
  std::string directive = "`pragma protect digest_key_method=";
  directive.append(value).append("\n");
  return directive;
}

TEST(ProtectDigestKeyMethodSyntax,
     TheStringAgainstTheKeywordStatesTheAlgorithm) {
  EXPECT_EQ(MethodAfter(StatesKeyMethod("\"rsa\"")).value, "rsa");
}

TEST(ProtectDigestKeyMethodSyntax, ABareIdentifierIsOneWrittenThingToo) {
  EXPECT_EQ(MethodAfter(StatesKeyMethod("rsa")).value, "rsa");
}

TEST(ProtectDigestKeyMethodSyntax, AListLeavesTheAlgorithmAlreadyStated) {
  std::string src = StatesKeyMethod("\"rsa\"");
  src += StatesKeyMethod("(padding=\"pss\")");
  EXPECT_EQ(MethodAfter(src).value, "rsa");
}

TEST(ProtectDigestKeyMethodSyntax, AListOnItsOwnStatesNoAlgorithm) {
  EXPECT_TRUE(MethodAfter(StatesKeyMethod("(padding=\"pss\")")).defaulted);
}

}  // namespace
