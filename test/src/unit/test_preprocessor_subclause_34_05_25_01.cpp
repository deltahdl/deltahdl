#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_preprocessor.h"
#include "helpers_protect_keys.h"
#include "helpers_protect_keyword_value.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_keywords.h"

using namespace delta;

struct ProtectKeyKeynameSyntaxTest : ::testing::Test {
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

TEST_F(ProtectKeyKeynameSyntaxTest, PragmaProtectKeyKeynameConsumed) {
  auto result = Preprocess("`pragma protect key_keyname = \"acme-key\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("acme-key"), std::string::npos);
}

TEST_F(ProtectKeyKeynameSyntaxTest,
       KeyKeynameDirectiveStrippedSurroundingTextKept) {
  auto result = Preprocess(
      "module m;\n`pragma protect key_keyname = \"acme-key\"\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

TEST_F(ProtectKeyKeynameSyntaxTest,
       KeyKeynameStringArgumentWithSpacesConsumed) {
  auto result =
      Preprocess("`pragma protect key_keyname = \"acme rsa key 1\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("acme rsa key 1"), std::string::npos);
}

constexpr std::string_view kEntity = "meridian-trust";
constexpr std::string_view kFirstKeyName = "wrapping-2026";
constexpr std::string_view kSecondKeyName = "wrapping-2027";
constexpr std::string_view kFirstKey = "meridian-trust-key-of-2026";
constexpr std::string_view kSecondKey = "meridian-trust-key-of-2027";

constexpr std::string_view kIdentifierKeyName = "wrapping2026";

ProtectKeyList KeysOfOneEntity() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kEntity, kFirstKeyName, kFirstKey));
  keys.Add(KeyOf(kEntity, kSecondKeyName, kSecondKey));
  return keys;
}

std::string NamesKey(std::string_view value) {
  std::string directive = "`pragma protect key_keyname=";
  directive.append(value).append("\n");
  return directive;
}

std::string NamesTheEntity() {
  std::string directive = "`pragma protect key_keyowner=\"";
  directive.append(kEntity).append("\"\n");
  return directive;
}
TEST(ProtectKeyKeynameSyntax, TheStringAgainstTheKeywordNamesTheKey) {
  EXPECT_EQ(ReadKeywordScope(NamesKey(InQuotes(kFirstKeyName)))
                .ValueOf(kKeyKeynameKeyword)
                .value,
            kFirstKeyName);
}

TEST(ProtectKeyKeynameSyntax, ABareIdentifierIsOneWrittenThingToo) {
  EXPECT_EQ(ReadKeywordScope(NamesKey(kIdentifierKeyName))
                .ValueOf(kKeyKeynameKeyword)
                .value,
            kIdentifierKeyName);
}

TEST(ProtectKeyKeynameSyntax, TheWholeOfASpaceBearingStringStandsInEffect) {
  EXPECT_EQ(ReadKeywordScope(NamesKey(InQuotes("acme rsa key 1")))
                .ValueOf(kKeyKeynameKeyword)
                .value,
            "acme rsa key 1");
}

TEST(ProtectKeyKeynameSyntax, AListLeavesTheKeyAlreadyNamed) {
  std::string src = NamesKey(InQuotes(kFirstKeyName));
  src += NamesKey("(held_by=\"meridian-trust\")");
  EXPECT_EQ(ReadKeywordScope(src).ValueOf(kKeyKeynameKeyword).value,
            kFirstKeyName);
}

TEST(ProtectKeyKeynameSyntax, AListOnItsOwnNamesNoKey) {
  EXPECT_TRUE(ReadKeywordScope(NamesKey("(held_by=\"meridian-trust\")"))
                  .ValueOf(kKeyKeynameKeyword)
                  .defaulted);
}

TEST(ProtectKeyKeynameSyntax, TheKeywordStandingAloneNamesNoKey) {
  EXPECT_TRUE(ReadKeywordScope("`pragma protect key_keyname\n")
                  .ValueOf(kKeyKeynameKeyword)
                  .value.empty());
}

TEST(ProtectKeyKeynameSyntax, AnEqualsWithNoValueAfterItIsNoExpression) {
  PreprocFixture f;
  Preprocess("`pragma protect key_keyname =\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

TEST(ProtectKeyKeynameSyntax, ANameMerelyOpeningWithTheKeywordIsNotIt) {
  EXPECT_TRUE(
      ReadKeywordScope("`pragma protect key_keynames=\"wrapping-2026\"\n")
          .ValueOf(kKeyKeynameKeyword)
          .defaulted);
}

TEST(ProtectKeyKeynameSyntax, TheNameDecidesWhichKeyIsReached) {
  ProtectKeyList keys = KeysOfOneEntity();
  EXPECT_EQ(
      ReadKeywordScope(NamesTheEntity() + NamesKey(InQuotes(kFirstKeyName)))
          .KeyBlockKeyReached(keys),
      kFirstKey);
  EXPECT_EQ(
      ReadKeywordScope(NamesTheEntity() + NamesKey(InQuotes(kSecondKeyName)))
          .KeyBlockKeyReached(keys),
      kSecondKey);
}

TEST(ProtectKeyKeynameSyntax, AListLeavesTheKeyTheNameReaches) {
  ProtectKeyList keys = KeysOfOneEntity();
  std::string src = NamesTheEntity();
  src += NamesKey(InQuotes(kFirstKeyName));
  src += NamesKey("(held_by=\"meridian-trust\")");
  EXPECT_EQ(ReadKeywordScope(src).KeyBlockKeyReached(keys), kFirstKey);
}

}  // namespace
