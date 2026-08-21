#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_program.h"
#include "helpers_protect_keyword_value.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_keywords.h"

using namespace delta;

// Exercises the syntax of the `comment` protect pragma keyword (§34.5.30.1).
// The syntax block defines the keyword expression as `comment = <string>`.
// Protect pragmas are processed at the preprocessor stage, where the generic
// `pragma` handler recognizes the keyword expression and consumes the directive
// line, including its string argument.
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

// The `comment = <string>` keyword expression is accepted and the directive
// line is stripped, including its string value.
TEST_F(ProtectCommentSyntaxTest, PragmaProtectCommentConsumed) {
  auto result = Preprocess("`pragma protect comment = \"acme notice\"\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("acme notice"), std::string::npos);
}

// Only the comment directive line is removed; neighboring source text survives,
// confirming it is the comment keyword expression line that the pragma path
// consumes.
TEST_F(ProtectCommentSyntaxTest, CommentDirectiveStrippedSurroundingTextKept) {
  auto result = Preprocess(
      "module m;\n`pragma protect comment = \"acme notice\"\nendmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

// The two cases above observe the directive line going away, which any protect
// pragma directive does whatever it writes, so a value written in a spelling
// §34.5.30.1 does not define brings the line's disappearance about just as
// readily. What §34.5.30.1 defines is the spelling: the keyword with a string
// written against it. The cases below read the value that spelling puts in
// effect back out of the keyword scope, through ReadKeywordScope in
// lib/cpp/test_helpers/helpers_protect_keyword_value.h.

// Two notices, each the documentation §34.5.30.1 writes against the keyword.
// They differ in every character a comparison could rest on, so a reading that
// kept the wrong one of the two reports the wrong one rather than a value
// either could have left.
constexpr std::string_view kFirstNotice = "Copyright 2026 Meridian Aerospace";
constexpr std::string_view kSecondNotice = "Copyright 2031 Vantage Optics";

// A notice whose first character is the one §22.5.1 opens a parenthesized
// pragma_value with, written inside quotation marks. A copyright notice
// ordinarily opens this way, so this is the spelling the keyword is most likely
// to be written in rather than a contrived one.
constexpr std::string_view kNoticeOpeningWithAParenthesis =
    "(c) 2026 Meridian Aerospace";

// A notice carrying the two characters that end a pragma directive's expression
// list when they stand outside quotation marks: the comma §22.5.1 separates
// expressions with, and the pair of slashes a one-line comment opens with.
constexpr std::string_view kNoticeCarryingACommaAndASlashPair =
    "Terms at http://meridian.example/ip, revision 3";

// A notice spelled the way an identifier is, for the case writing the value
// bare. §22.11 reads a directive as tokens, and a space is not a character an
// identifier holds, so the notices above written bare would be several tokens
// rather than the one written thing a pragma_value is.
constexpr std::string_view kBareWordNotice = "confidential";

// A notice spelled as a number, for the case writing that spelling. A year is
// the documentation a copyright notice reduces to when it is reduced at all.
constexpr std::string_view kNumberNotice = "2026";

// A parenthesized pragma_value: a list of further pragma expressions, naming
// parts of a value rather than being one. Neither expression it names repeats
// any word of a notice above, so a reading that took the list as the value
// reports text no notice here could have left.
constexpr std::string_view kSubkeywordList = "(lang=\"en\", charset=\"utf-8\")";

// A directive writing `value` against the keyword, spelled as it stands here.
std::string Documents(std::string_view value) {
  std::string directive = "`pragma protect comment=";
  directive.append(value).append("\n");
  return directive;
}

// §34.5.30.1: the expression is `comment = <string>`, and what stands in effect
// afterwards is what was written inside the quotation marks, without them.
TEST(ProtectCommentSyntax, TheStringAgainstTheKeywordIsTheDocumentation) {
  EXPECT_EQ(ReadKeywordScope(Documents(InQuotes(kFirstNotice)))
                .ValueOf(kCommentKeyword)
                .value,
            kFirstNotice);
}

// §22.5.1 admits a bare identifier as a pragma_value, and one written thing is
// what §34.5.30.1 writes against this keyword.
TEST(ProtectCommentSyntax, ABareIdentifierIsOneWrittenThingToo) {
  EXPECT_EQ(ReadKeywordScope(Documents(kBareWordNotice))
                .ValueOf(kCommentKeyword)
                .value,
            kBareWordNotice);
}

// §22.5.1 admits a number as a pragma_value as well, and a number carries no
// quotation marks to take off, so what stands in effect is the digits as they
// were written.
TEST(ProtectCommentSyntax, ANumberIsOneWrittenThingToo) {
  EXPECT_EQ(
      ReadKeywordScope(Documents(kNumberNotice)).ValueOf(kCommentKeyword).value,
      kNumberNotice);
}

// §22.5.1 settles which spelling a pragma_value was written in by the character
// it opens with, and a value opening with a quotation mark is the string
// spelling however the text inside it opens. A notice reading "(c) 2026 ..." is
// therefore the documentation the keyword carries and not a list.
TEST(ProtectCommentSyntax, AStringOpeningWithAParenthesisIsStillAString) {
  EXPECT_EQ(
      ReadKeywordScope(Documents(InQuotes(kNoticeOpeningWithAParenthesis)))
          .ValueOf(kCommentKeyword)
          .value,
      kNoticeOpeningWithAParenthesis);
}

// The <string> operand of §34.5.30.1 as §22.5.1 admits it: the quotation marks
// enclose one written thing, so the comma that would separate two expressions
// of the directive's list and the slashes that would open a one-line comment
// are documentation here, and the whole of the notice stands in effect rather
// than the part of it before either.
TEST(ProtectCommentSyntax, TheWholeOfAStringStandsInEffectPunctuationAndAll) {
  EXPECT_EQ(
      ReadKeywordScope(Documents(InQuotes(kNoticeCarryingACommaAndASlashPair)))
          .ValueOf(kCommentKeyword)
          .value,
      kNoticeCarryingACommaAndASlashPair);
}

// §34.4 has a keyword's value belong to the position the reading has got to, so
// a second directive writing the keyword in the spelling §34.5.30.1 defines
// replaces what the first wrote. This is what makes the two cases below about
// the parenthesized spelling rather than about the keyword never changing.
TEST(ProtectCommentSyntax, ANoticeWrittenLaterReplacesTheOneBeforeIt) {
  std::string src = Documents(InQuotes(kFirstNotice));
  src += Documents(InQuotes(kSecondNotice));
  EXPECT_EQ(ReadKeywordScope(src).ValueOf(kCommentKeyword).value,
            kSecondNotice);
}

// §34.5.30.1 writes a string against the keyword, and §22.5.1 makes a
// parenthesized pragma_value a list of further expressions rather than one
// written thing, so such an expression states no documentation and the notice
// stated earlier is still what the keyword holds.
TEST(ProtectCommentSyntax, AListLeavesTheNoticeAlreadyWritten) {
  std::string src = Documents(InQuotes(kFirstNotice));
  src += Documents(kSubkeywordList);
  EXPECT_EQ(ReadKeywordScope(src).ValueOf(kCommentKeyword).value, kFirstNotice);
}

// The same list where no notice was written before it, which leaves the keyword
// at the default §34.4 gives it -- what makes the case above about the list
// rather than about the value that happened to precede it.
TEST(ProtectCommentSyntax, AListOnItsOwnStatesNoDocumentation) {
  EXPECT_TRUE(ReadKeywordScope(Documents(kSubkeywordList))
                  .ValueOf(kCommentKeyword)
                  .defaulted);
}

// A list states nothing for the keyword and is still a pragma_expression
// §22.5.1 spells, so the line carrying one is consumed the way every protect
// pragma directive line is and the text around it is left alone. Nothing is
// reported for the line either: ReadKeywordScope fails the case where the
// reading left an error behind.
TEST(ProtectCommentSyntax, TheLineWritingAListIsConsumedAllTheSame) {
  ReadKeywordScope scope("module m;\n" + Documents(kSubkeywordList) +
                         "endmodule\n");
  EXPECT_EQ(scope.text.find("pragma"), std::string::npos);
  EXPECT_EQ(scope.text.find("charset"), std::string::npos);
  EXPECT_NE(scope.text.find("endmodule"), std::string::npos);
}

// §34.5.30.1 writes a string against the keyword, so the keyword standing alone
// is written in a spelling the subclause does not define and it documents
// nothing.
//
// What is asserted is the value and not whether a default put it there. #3271
// records that a keyword written standing alone is kept as having stated an
// empty value, so the two are not told apart here; documenting nothing is what
// this subclause turns on either way.
TEST(ProtectCommentSyntax, TheKeywordStandingAloneDocumentsNothing) {
  EXPECT_TRUE(ReadKeywordScope("`pragma protect comment\n")
                  .ValueOf(kCommentKeyword)
                  .value.empty());
}

// §34.5.30.1 spells one name, and a name that merely opens with those
// characters is a different one. A text writing the longer name has written a
// keyword §34.4 does not tabulate, so nothing is put in effect for the one it
// resembles.
TEST(ProtectCommentSyntax, ANameMerelyOpeningWithTheKeywordIsNotIt) {
  EXPECT_TRUE(ReadKeywordScope("`pragma protect comments=\"Copyright 2026\"\n")
                  .ValueOf(kCommentKeyword)
                  .defaulted);
}

}  // namespace
