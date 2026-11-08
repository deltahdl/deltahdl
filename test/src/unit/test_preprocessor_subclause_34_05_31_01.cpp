#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_protect_keyword_value.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_keywords.h"

using namespace delta;

struct ProtectResetSyntaxTest : ::testing::Test {
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

TEST_F(ProtectResetSyntaxTest, PragmaProtectResetConsumed) {
  auto result = Preprocess("`pragma protect reset\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("reset"), std::string::npos);
}

TEST_F(ProtectResetSyntaxTest, ResetDirectiveStrippedSurroundingTextKept) {
  auto result = Preprocess("module m;\n`pragma protect reset\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

constexpr std::string_view kProvider = "Meridian Aerospace";

constexpr std::string_view kProvidersKey = "meridian-2031";

std::string Directive(std::string_view expressions) {
  std::string text = "`pragma protect ";
  text.append(expressions).append("\n");
  return text;
}

std::string NamesTheProvider() {
  std::string expression = "data_keyowner=\"";
  expression.append(kProvider).append("\"");
  return Directive(expression);
}

TEST(ProtectResetSyntax, TheKeywordStandingAloneIsTheSpellingThatRestores) {
  EXPECT_TRUE(ReadKeywordScope(NamesTheProvider() + Directive(kResetKeyword))
                  .ValueOf(kDataKeyownerKeyword)
                  .defaulted);
}

TEST(ProtectResetSyntax, AValueWrittenAgainstTheKeywordRestoresNothing) {
  EXPECT_EQ(ReadKeywordScope(NamesTheProvider() + Directive("reset=\"now\""))
                .ValueOf(kDataKeyownerKeyword)
                .value,
            kProvider);
}

TEST(ProtectResetSyntax, AListWrittenAgainstTheKeywordRestoresNothing) {
  EXPECT_EQ(
      ReadKeywordScope(NamesTheProvider() + Directive("reset=(all=\"yes\")"))
          .ValueOf(kDataKeyownerKeyword)
          .value,
      kProvider);
}

TEST(ProtectResetSyntax, ANameMerelyOpeningWithTheKeywordIsNotIt) {
  EXPECT_EQ(ReadKeywordScope(NamesTheProvider() + Directive("resets"))
                .ValueOf(kDataKeyownerKeyword)
                .value,
            kProvider);
}

TEST(ProtectResetSyntax, AnEscapedSpellingOfTheKeywordIsNotIt) {
  EXPECT_EQ(ReadKeywordScope(NamesTheProvider() + Directive("\\reset"))
                .ValueOf(kDataKeyownerKeyword)
                .value,
            kProvider);
}

TEST(ProtectResetSyntax, TheKeywordIsStillItselfBesideAnotherExpression) {
  std::string expressions = "reset, data_keyname=\"";
  expressions.append(kProvidersKey).append("\"");
  ReadKeywordScope scope(NamesTheProvider() + Directive(expressions));
  EXPECT_TRUE(scope.ValueOf(kDataKeyownerKeyword).defaulted);
  EXPECT_EQ(scope.ValueOf(kDataKeynameKeyword).value, kProvidersKey);
}

}  // namespace
