#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_protect_region.h"
#include "helpers_text_lines.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_keywords.h"

using namespace delta;

namespace {

constexpr std::string_view kAuthorName = "Ada Lovelace";
constexpr std::string_view kAuthorDirective =
    "`pragma protect author=\"Ada Lovelace\"\n";

constexpr std::string_view kAnyAuthorDirective = "`pragma protect author=";

constexpr std::string_view kListAgainstTheKeyword =
    "`pragma protect author=(first=\"Ada\", last=\"Lovelace\")\n";

std::string EncryptedRegionWriting(std::string_view written) {
  return Encrypted(RegionWriting(written));
}

struct ReadSource {
  static PreprocConfig KeyConfig() {
    PreprocConfig config;
    config.protect_keys = TheRegionsKey();
    return config;
  }

  SourceManager mgr;
  DiagEngine diag{mgr};
  std::string text;

  explicit ReadSource(const std::string& src) {
    Preprocessor pp(mgr, diag, KeyConfig());
    text = pp.Preprocess(mgr.AddFile("<test>", src));
  }

  bool Holds(std::string_view needle) const {
    return text.find(needle) != std::string::npos;
  }
};

TEST(ProtectAuthorSyntax, TheKeywordWithAStringNamesTheAuthor) {
  std::string written = EncryptedRegionWriting(kAuthorDirective);
  EXPECT_FALSE(Holds(written, kSealedDesign));
  EXPECT_EQ(TimesWritten(written, kAuthorDirective), 1U);
}

TEST(ProtectAuthorSyntax, TheKeywordWithAStringIsHeldBackFromTheBlock) {
  std::string opened = OpenedBlockWriting(kAuthorDirective);
  EXPECT_TRUE(Holds(opened, kSealedDesign));
  EXPECT_FALSE(Holds(opened, kAnyAuthorDirective));
}

TEST(ProtectAuthorSyntax, PaddingAroundTheEqualsLeavesTheExpressionStanding) {
  std::string written =
      EncryptedRegionWriting("`pragma  protect  author  =  \"Ada Lovelace\"\n");
  EXPECT_EQ(TimesWritten(written, kAuthorDirective), 1U);
}

TEST(ProtectAuthorSyntax, TheExpressionFirstInAListStillNamesTheAuthor) {
  std::string written = EncryptedRegionWriting(
      "`pragma protect author=\"Ada Lovelace\", comment=\"rev 3\"\n");
  EXPECT_EQ(TimesWritten(written, kAuthorDirective), 1U);
}

TEST(ProtectAuthorSyntax, TheExpressionLastInAListStillNamesTheAuthor) {
  std::string written = EncryptedRegionWriting(
      "`pragma protect comment=\"rev 3\", author=\"Ada Lovelace\"\n");
  EXPECT_EQ(TimesWritten(written, kAuthorDirective), 1U);
}

TEST(ProtectAuthorSyntax, ACommentAfterTheStringLeavesTheExpressionStanding) {
  std::string written = EncryptedRegionWriting(
      "`pragma protect author=\"Ada Lovelace\" // who wrote this\n");
  EXPECT_EQ(TimesWritten(written, kAuthorDirective), 1U);
}

TEST(ProtectAuthorSyntax, AStringHoldingACommaIsOneName) {
  std::string naming = "`pragma protect author=\"Lovelace, Ada\"\n";
  EXPECT_TRUE(Holds(EncryptedRegionWriting(naming), naming));
}

TEST(ProtectAuthorSyntax, AStringHoldingCommentPunctuationIsOneName) {
  std::string naming =
      "`pragma protect author=\"Ada Lovelace // Analytical Engine\"\n";
  EXPECT_TRUE(Holds(EncryptedRegionWriting(naming), naming));
}

TEST(ProtectAuthorSyntax, AStringHoldingTheExpressionIsOneName) {
  std::string naming = "`pragma protect author=\"author=Ada Lovelace\"\n";
  std::string written = EncryptedRegionWriting(naming);
  EXPECT_TRUE(Holds(written, naming));
  EXPECT_EQ(TimesWritten(written, kAnyAuthorDirective), 1U);
}

TEST(ProtectAuthorSyntax, AStringHoldingAnEscapedQuoteIsOneName) {
  std::string naming =
      "`pragma protect author=\"Ada \\\"the Countess\\\" Lovelace\"\n";
  EXPECT_TRUE(Holds(EncryptedRegionWriting(naming), naming));
}

TEST(ProtectAuthorSyntax, AnEmptyStringIsAString) {
  std::string naming = "`pragma protect author=\"\"\n";
  EXPECT_TRUE(Holds(EncryptedRegionWriting(naming), naming));
  EXPECT_FALSE(Holds(OpenedBlockWriting(naming), kAnyAuthorDirective));
}

TEST(ProtectAuthorSyntax, TheKeywordStandingAloneWritesNoString) {
  std::string written = EncryptedRegionWriting("`pragma protect author\n");
  EXPECT_TRUE(Holds(written, kBeginProtected));
  EXPECT_FALSE(Holds(written, kAnyAuthorDirective));
}

TEST(ProtectAuthorSyntax, TheKeywordStandingAloneIsSealed) {
  std::string bare = "`pragma protect author\n";
  EXPECT_TRUE(Holds(OpenedBlockWriting(bare), bare));
}

TEST(ProtectAuthorSyntax, AParenthesizedListAgainstTheKeywordNamesNobody) {
  std::string written = EncryptedRegionWriting(
      "`pragma protect author=(first=\"Ada\", last=\"Lovelace\")\n");
  EXPECT_TRUE(Holds(written, kBeginProtected));
  EXPECT_FALSE(Holds(written, kAnyAuthorDirective));
}

TEST(ProtectAuthorSyntax, AParenthesizedListAgainstTheKeywordIsSealed) {
  std::string listed =
      "`pragma protect author=(first=\"Ada\", last=\"Lovelace\")\n";
  EXPECT_TRUE(Holds(OpenedBlockWriting(listed), listed));
}

TEST(ProtectAuthorSyntax, AListLeavesTheAuthorAlreadyNamedStanding) {
  std::string src(kAuthorDirective);
  src += kListAgainstTheKeyword;
  ReadWithTheKeys run(src);
  EXPECT_FALSE(run.diags.HasErrors());
  EXPECT_FALSE(run.reader.ProtectKeywords().ValueOf(kAuthorKeyword).defaulted);
  EXPECT_EQ(run.reader.ProtectKeywords().ValueOf(kAuthorKeyword).value,
            kAuthorName);
}

TEST(ProtectAuthorSyntax, AListWithNoAuthorNamedBeforeItLeavesTheDefault) {
  ReadWithTheKeys run{std::string(kListAgainstTheKeyword)};
  EXPECT_FALSE(run.diags.HasErrors());
  EXPECT_TRUE(run.reader.ProtectKeywords().ValueOf(kAuthorKeyword).defaulted);
  EXPECT_TRUE(
      run.reader.ProtectKeywords().ValueOf(kAuthorKeyword).value.empty());
}

TEST(ProtectAuthorSyntax, TheLettersInAnotherCaseAreNotTheKeyword) {
  std::string written =
      EncryptedRegionWriting("`pragma protect AUTHOR=\"Ada Lovelace\"\n");
  EXPECT_TRUE(Holds(written, kBeginProtected));
  EXPECT_FALSE(Holds(written, kAnyAuthorDirective));
}

TEST(ProtectAuthorSyntax, TheLettersAsAnEscapedIdentifierAreNotTheKeyword) {
  std::string written =
      EncryptedRegionWriting("`pragma protect \\author =\"Ada Lovelace\"\n");
  EXPECT_TRUE(Holds(written, kBeginProtected));
  EXPECT_FALSE(Holds(written, kAnyAuthorDirective));
}

TEST(ProtectAuthorSyntax, ALongerTabulatedNameIsNotTheKeyword) {
  std::string written =
      EncryptedRegionWriting("`pragma protect author_info=\"Ada Lovelace\"\n");
  EXPECT_TRUE(Holds(written, kBeginProtected));
  EXPECT_FALSE(Holds(written, kAnyAuthorDirective));
}

TEST(ProtectAuthorSyntax, TheLettersWrittenAsAValueAreNotTheKeyword) {
  std::string written =
      EncryptedRegionWriting("`pragma protect comment=author\n");
  EXPECT_TRUE(Holds(written, kBeginProtected));
  EXPECT_FALSE(Holds(written, kAnyAuthorDirective));
}

TEST(ProtectAuthorSyntax, TheExpressionInsideAParenthesizedValueNamesNobody) {
  std::string written = EncryptedRegionWriting(
      "`pragma protect encoding=(enctype=\"base64\", "
      "author=\"Ada Lovelace\")\n");
  EXPECT_TRUE(Holds(written, kBeginProtected));
  EXPECT_FALSE(Holds(written, kAnyAuthorDirective));
}

TEST(ProtectAuthorSyntax, TheExpressionInsideAStringNamesNobody) {
  std::string written = EncryptedRegionWriting(
      "`pragma protect comment=\"author=\\\"Ada Lovelace\\\"\"\n");
  EXPECT_TRUE(Holds(written, kBeginProtected));
  EXPECT_FALSE(Holds(written, kAnyAuthorDirective));
}

TEST(ProtectAuthorSyntax, TheExpressionAfterACommentNamesNobody) {
  std::string written = EncryptedRegionWriting(
      "`pragma protect comment=\"rev 3\" // author=\"Ada Lovelace\"\n");
  EXPECT_TRUE(Holds(written, kBeginProtected));
  EXPECT_FALSE(Holds(written, kAnyAuthorDirective));
}

TEST(ProtectAuthorSyntax, TheKeywordUnderAnotherPragmaNameNamesNobody) {
  std::string written =
      EncryptedRegionWriting("`pragma acme author=\"Ada Lovelace\"\n");
  EXPECT_TRUE(Holds(written, kBeginProtected));
  EXPECT_FALSE(Holds(written, kAnyAuthorDirective));
}

TEST(ProtectAuthorSyntax, TheKeywordAsThePragmaNameNamesNobody) {
  std::string written =
      EncryptedRegionWriting("`pragma author = \"Ada Lovelace\"\n");
  EXPECT_TRUE(Holds(written, kBeginProtected));
  EXPECT_FALSE(Holds(written, kAnyAuthorDirective));
}

TEST(ProtectAuthorSyntax, TheDirectiveCarryingTheExpressionContributesNoText) {
  ReadSource read("module m;\n" + std::string(kAuthorDirective) +
                  "endmodule\n");
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_FALSE(read.Holds(kAuthorName));
  EXPECT_TRUE(read.Holds("module m;"));
  EXPECT_TRUE(read.Holds("endmodule"));
}

TEST(ProtectAuthorSyntax, AMacroExpandingToTheWholeExpressionIsRead) {
  ReadSource read(
      "`define NAMES_THE_AUTHOR author = \"Ada Lovelace\"\n"
      "`pragma protect `NAMES_THE_AUTHOR\n"
      "module m;\nendmodule\n");
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_FALSE(read.Holds(kAuthorName));
  EXPECT_TRUE(read.Holds("module m;"));
}

TEST(ProtectAuthorSyntax, AnEnvelopeCarryingTheExpressionIsReadBack) {
  ReadSource read(EncryptedRegionWriting(kAuthorDirective));
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_TRUE(read.Holds("module sealed_m"));
  EXPECT_FALSE(read.Holds(kAuthorName));
}

TEST(ProtectAuthorSyntax, TheExpressionInsideASealedModelIsRead) {
  std::string envelope = "`pragma protect begin_protected\n";
  envelope.append(kAuthorDirective);
  envelope.append("`pragma protect end_protected\n");
  ReadSource read("module m;\n" + envelope + "endmodule\n");
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_FALSE(read.Holds(kAuthorName));
  EXPECT_TRUE(read.Holds("module m;"));
  EXPECT_TRUE(read.Holds("endmodule"));
}

TEST(ProtectAuthorSyntax, ARegionUnderAStatedEncodingCarriesTheExpression) {
  std::string stated = "`pragma protect encoding=(enctype=\"base64\")\n";
  stated.append(kAuthorDirective);
  std::string envelope = EncryptedRegionWriting(stated);
  ASSERT_TRUE(Holds(envelope, "enctype=\"base64\""));
  EXPECT_EQ(TimesWritten(envelope, kAuthorDirective), 1U);
  ReadSource read(envelope);
  EXPECT_FALSE(read.diag.HasErrors());
  EXPECT_TRUE(read.Holds("module sealed_m"));
}

}  // namespace
