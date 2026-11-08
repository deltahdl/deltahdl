#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_preprocessor.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_keywords.h"

using namespace delta;

struct ProtectDigestKeynameSyntaxTest : ::testing::Test {
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

TEST_F(ProtectDigestKeynameSyntaxTest, PragmaProtectDigestKeynameConsumed) {
  auto result = Preprocess("`pragma protect digest_keyname = \"key1\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("key1"), std::string::npos);
}

TEST_F(ProtectDigestKeynameSyntaxTest,
       DigestKeynameDirectiveStrippedSurroundingTextKept) {
  auto result = Preprocess(
      "module m;\n`pragma protect digest_keyname = \"key1\"\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

TEST_F(ProtectDigestKeynameSyntaxTest,
       DigestKeynameStringArgumentWithSpacesConsumed) {
  auto result =
      Preprocess("`pragma protect digest_keyname = \"project alpha key\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("project alpha key"), std::string::npos);
}

ProtectKeywordValue DigestKeynameAfter(const std::string& src) {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Preprocessor pp(mgr, diag, PreprocConfig{});
  pp.Preprocess(mgr.AddFile("<test>", src));
  EXPECT_FALSE(diag.HasErrors()) << src;
  return pp.ProtectKeywords().ValueOf(kDigestKeynameKeyword);
}

std::string NamesDigestKey(std::string_view value) {
  std::string directive = "`pragma protect digest_keyname=";
  directive.append(value).append("\n");
  return directive;
}

TEST(ProtectDigestKeynameSyntax, TheStringAgainstTheKeywordNamesTheKey) {
  EXPECT_EQ(DigestKeynameAfter(NamesDigestKey("\"sigil-7\"")).value, "sigil-7");
}

TEST(ProtectDigestKeynameSyntax, TheStringAgainstTheKeywordIsNoDefault) {
  EXPECT_FALSE(DigestKeynameAfter(NamesDigestKey("\"sigil-7\"")).defaulted);
}

TEST(ProtectDigestKeynameSyntax, ANameHoldingSpacesIsOneValue) {
  EXPECT_EQ(DigestKeynameAfter(NamesDigestKey("\"the winter sigil\"")).value,
            "the winter sigil");
}

TEST(ProtectDigestKeynameSyntax, ABareIdentifierIsOneWrittenThingToo) {
  EXPECT_EQ(DigestKeynameAfter(NamesDigestKey("sigil_7")).value, "sigil_7");
}

TEST(ProtectDigestKeynameSyntax, AListLeavesTheNameAlreadyWrittenStanding) {
  std::string src = NamesDigestKey("\"sigil-7\"");
  src += NamesDigestKey("(held_by=\"acme\")");
  EXPECT_EQ(DigestKeynameAfter(src).value, "sigil-7");
}

TEST(ProtectDigestKeynameSyntax, AListOnItsOwnNamesNoKey) {
  EXPECT_TRUE(
      DigestKeynameAfter(NamesDigestKey("(held_by=\"acme\")")).defaulted);
}

TEST(ProtectDigestKeynameSyntax, AnEqualsWithNoValueAfterItIsNoExpression) {
  PreprocFixture f;
  Preprocess("`pragma protect digest_keyname =\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

}  // namespace
