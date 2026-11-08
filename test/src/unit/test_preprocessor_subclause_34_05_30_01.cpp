#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_protect_keyword_value.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_keywords.h"

using namespace delta;

struct ProtectCommentSyntaxTest : ::testing::Test {
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

TEST_F(ProtectCommentSyntaxTest, PragmaProtectCommentConsumed) {
  auto result = Preprocess("`pragma protect comment = \"acme notice\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("acme notice"), std::string::npos);
}

TEST_F(ProtectCommentSyntaxTest, CommentDirectiveStrippedSurroundingTextKept) {
  auto result = Preprocess(
      "module m;\n`pragma protect comment = \"acme notice\"\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

constexpr std::string_view kFirstNotice = "Copyright 2026 Meridian Aerospace";
constexpr std::string_view kSecondNotice = "Copyright 2031 Vantage Optics";

constexpr std::string_view kNoticeOpeningWithAParenthesis =
    "(c) 2026 Meridian Aerospace";

constexpr std::string_view kNoticeCarryingACommaAndASlashPair =
    "Terms at http://meridian.example/ip, revision 3";

constexpr std::string_view kBareWordNotice = "confidential";

constexpr std::string_view kNumberNotice = "2026";

constexpr std::string_view kSubkeywordList = "(lang=\"en\", charset=\"utf-8\")";

std::string Documents(std::string_view value) {
  std::string directive = "`pragma protect comment=";
  directive.append(value).append("\n");
  return directive;
}

TEST(ProtectCommentSyntax, TheStringAgainstTheKeywordIsTheDocumentation) {
  EXPECT_EQ(ReadKeywordScope(Documents(InQuotes(kFirstNotice)))
                .ValueOf(kCommentKeyword)
                .value,
            kFirstNotice);
}

TEST(ProtectCommentSyntax, ABareIdentifierIsOneWrittenThingToo) {
  EXPECT_EQ(ReadKeywordScope(Documents(kBareWordNotice))
                .ValueOf(kCommentKeyword)
                .value,
            kBareWordNotice);
}

TEST(ProtectCommentSyntax, ANumberIsOneWrittenThingToo) {
  EXPECT_EQ(
      ReadKeywordScope(Documents(kNumberNotice)).ValueOf(kCommentKeyword).value,
      kNumberNotice);
}

TEST(ProtectCommentSyntax, AStringOpeningWithAParenthesisIsStillAString) {
  EXPECT_EQ(
      ReadKeywordScope(Documents(InQuotes(kNoticeOpeningWithAParenthesis)))
          .ValueOf(kCommentKeyword)
          .value,
      kNoticeOpeningWithAParenthesis);
}

TEST(ProtectCommentSyntax, TheWholeOfAStringStandsInEffectPunctuationAndAll) {
  EXPECT_EQ(
      ReadKeywordScope(Documents(InQuotes(kNoticeCarryingACommaAndASlashPair)))
          .ValueOf(kCommentKeyword)
          .value,
      kNoticeCarryingACommaAndASlashPair);
}

TEST(ProtectCommentSyntax, ANoticeWrittenLaterReplacesTheOneBeforeIt) {
  std::string src = Documents(InQuotes(kFirstNotice));
  src += Documents(InQuotes(kSecondNotice));
  EXPECT_EQ(ReadKeywordScope(src).ValueOf(kCommentKeyword).value,
            kSecondNotice);
}

TEST(ProtectCommentSyntax, AListLeavesTheNoticeAlreadyWritten) {
  std::string src = Documents(InQuotes(kFirstNotice));
  src += Documents(kSubkeywordList);
  EXPECT_EQ(ReadKeywordScope(src).ValueOf(kCommentKeyword).value, kFirstNotice);
}

TEST(ProtectCommentSyntax, AListOnItsOwnStatesNoDocumentation) {
  EXPECT_TRUE(ReadKeywordScope(Documents(kSubkeywordList))
                  .ValueOf(kCommentKeyword)
                  .defaulted);
}

TEST(ProtectCommentSyntax, TheLineWritingAListIsConsumedAllTheSame) {
  ReadKeywordScope scope("module m;\n" + Documents(kSubkeywordList) +
                         "endmodule\n");
  EXPECT_EQ(scope.text.find("pragma"), std::string::npos);
  EXPECT_EQ(scope.text.find("charset"), std::string::npos);
  EXPECT_NE(scope.text.find("endmodule"), std::string::npos);
}

TEST(ProtectCommentSyntax, TheKeywordStandingAloneDocumentsNothing) {
  EXPECT_TRUE(ReadKeywordScope("`pragma protect comment\n")
                  .ValueOf(kCommentKeyword)
                  .value.empty());
}

TEST(ProtectCommentSyntax, ANameMerelyOpeningWithTheKeywordIsNotIt) {
  EXPECT_TRUE(ReadKeywordScope("`pragma protect comments=\"Copyright 2026\"\n")
                  .ValueOf(kCommentKeyword)
                  .defaulted);
}

}  // namespace
