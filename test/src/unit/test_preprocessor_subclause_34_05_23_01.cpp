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

struct ProtectKeyKeyownerSyntaxTest : ::testing::Test {
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

TEST_F(ProtectKeyKeyownerSyntaxTest, PragmaProtectKeyKeyownerConsumed) {
  auto result = Preprocess("`pragma protect key_keyowner = \"Acme Corp\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("Acme Corp"), std::string::npos);
}

TEST_F(ProtectKeyKeyownerSyntaxTest,
       KeyKeyownerDirectiveStrippedSurroundingTextKept) {
  auto result = Preprocess(
      "module m;\n`pragma protect key_keyowner = \"Acme Corp\"\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

constexpr std::string_view kFirstEntity = "meridian-trust";
constexpr std::string_view kSecondEntity = "cerulean-vault";
constexpr std::string_view kSharedKeyName = "wrapping-2027";
constexpr std::string_view kFirstEntityKey = "meridian-trust-wrapping-key";
constexpr std::string_view kSecondEntityKey = "cerulean-vault-wrapping-key";

constexpr std::string_view kIdentifierEntity = "meridiantrust";

ProtectKeyList KeysOfBothEntities() {
  ProtectKeyList keys;
  keys.Add(KeyOf(kFirstEntity, kSharedKeyName, kFirstEntityKey));
  keys.Add(KeyOf(kSecondEntity, kSharedKeyName, kSecondEntityKey));
  return keys;
}

std::string NamesEntity(std::string_view value) {
  std::string directive = "`pragma protect key_keyowner=";
  directive.append(value).append("\n");
  return directive;
}

std::string NamesTheKey() {
  std::string directive = "`pragma protect key_keyname=\"";
  directive.append(kSharedKeyName).append("\"\n");
  return directive;
}
TEST(ProtectKeyKeyownerSyntax, TheStringAgainstTheKeywordNamesTheEntity) {
  EXPECT_EQ(ReadKeywordScope(NamesEntity(InQuotes(kFirstEntity)))
                .ValueOf(kKeyKeyownerKeyword)
                .value,
            kFirstEntity);
}

TEST(ProtectKeyKeyownerSyntax, ABareIdentifierIsOneWrittenThingToo) {
  EXPECT_EQ(ReadKeywordScope(NamesEntity(kIdentifierEntity))
                .ValueOf(kKeyKeyownerKeyword)
                .value,
            kIdentifierEntity);
}

TEST(ProtectKeyKeyownerSyntax, TheWholeOfASpaceBearingStringStandsInEffect) {
  EXPECT_EQ(ReadKeywordScope(NamesEntity(InQuotes("Acme Corp")))
                .ValueOf(kKeyKeyownerKeyword)
                .value,
            "Acme Corp");
}

TEST(ProtectKeyKeyownerSyntax, TheDataEntityDoesNotFillThePlaceLeftEmpty) {
  ProtectKeywordValue entity =
      ReadKeywordScope("`pragma protect data_keyowner=\"meridian-trust\"\n")
          .ValueOf(kKeyKeyownerKeyword);
  EXPECT_TRUE(entity.defaulted);
  EXPECT_TRUE(entity.value.empty());
}

TEST(ProtectKeyKeyownerSyntax, AListLeavesTheEntityAlreadyNamed) {
  std::string src = NamesEntity(InQuotes(kFirstEntity));
  src += NamesEntity("(held_by=\"cerulean-vault\")");
  EXPECT_EQ(ReadKeywordScope(src).ValueOf(kKeyKeyownerKeyword).value,
            kFirstEntity);
}

TEST(ProtectKeyKeyownerSyntax, AListOnItsOwnNamesNoEntity) {
  EXPECT_TRUE(ReadKeywordScope(NamesEntity("(held_by=\"cerulean-vault\")"))
                  .ValueOf(kKeyKeyownerKeyword)
                  .defaulted);
}

TEST(ProtectKeyKeyownerSyntax, TheKeywordStandingAloneNamesNoEntity) {
  EXPECT_TRUE(ReadKeywordScope("`pragma protect key_keyowner\n")
                  .ValueOf(kKeyKeyownerKeyword)
                  .value.empty());
}

TEST(ProtectKeyKeyownerSyntax, AnEqualsWithNoValueAfterItIsNoExpression) {
  PreprocFixture f;
  Preprocess("`pragma protect key_keyowner =\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

TEST(ProtectKeyKeyownerSyntax, ANameMerelyOpeningWithTheKeywordIsNotIt) {
  EXPECT_TRUE(
      ReadKeywordScope("`pragma protect key_keyowners=\"meridian-trust\"\n")
          .ValueOf(kKeyKeyownerKeyword)
          .defaulted);
}

TEST(ProtectKeyKeyownerSyntax, TheEntityNamedDecidesWhichKeyIsReached) {
  ProtectKeyList keys = KeysOfBothEntities();
  EXPECT_EQ(
      ReadKeywordScope(NamesEntity(InQuotes(kFirstEntity)) + NamesTheKey())
          .KeyBlockKeyReached(keys),
      kFirstEntityKey);
  EXPECT_EQ(
      ReadKeywordScope(NamesEntity(InQuotes(kSecondEntity)) + NamesTheKey())
          .KeyBlockKeyReached(keys),
      kSecondEntityKey);
}

TEST(ProtectKeyKeyownerSyntax, AListLeavesTheKeyTheEntityNamedReaches) {
  ProtectKeyList keys = KeysOfBothEntities();
  std::string src = NamesEntity(InQuotes(kFirstEntity));
  src += NamesTheKey();
  src += NamesEntity("(held_by=\"cerulean-vault\")");
  EXPECT_EQ(ReadKeywordScope(src).KeyBlockKeyReached(keys), kFirstEntityKey);
}

}  // namespace
