#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_preprocessor.h"
#include "helpers_protect_keyword_value.h"
#include "helpers_reported_error.h"
#include "helpers_text_lines.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

// Exercises the syntax of the `decrypt_license` protect pragma keyword
// (§34.5.28.1). The syntax block defines the keyword expression as a
// parenthesized subkeyword list: `decrypt_license = ( library = <string> ,
// entry = <string> , feature = <string> [ , exit = <string> ]
// [ , match = <number> ] )`. Protect pragmas are processed at the preprocessor
// stage, where the generic `pragma` handler recognizes the keyword expression
// and consumes the directive line, including the entire parenthesized value.
struct ProtectDecryptLicenseSyntaxTest : ::testing::Test {
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

// The fully populated keyword expression, carrying both optional subkeywords
// (`exit` and `match`) alongside the three required ones, is accepted and the
// directive line is stripped, including every subkeyword and value.
TEST_F(ProtectDecryptLicenseSyntaxTest, PragmaProtectDecryptLicenseConsumed) {
  auto result = Preprocess(
      "`pragma protect decrypt_license = ( library = \"liblic.so\" , entry = "
      "\"check\" , feature = \"core\" , exit = \"release\" , match = 1 )\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("decrypt_license"), std::string::npos);
  EXPECT_EQ(result.find("liblic.so"), std::string::npos);
}

// Only the decrypt_license directive line is removed; neighboring source text
// survives, confirming it is the decrypt_license keyword expression line that
// the pragma path consumes.
TEST_F(ProtectDecryptLicenseSyntaxTest,
       DecryptLicenseDirectiveStrippedSurroundingTextKept) {
  auto result = Preprocess(
      "module m;\n"
      "`pragma protect decrypt_license = ( library = \"liblic.so\" , entry = "
      "\"check\" , feature = \"core\" )\n"
      "endmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("liblic.so"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

// The optional `exit` and `match` subkeywords may be omitted: the minimal form
// carrying only the three required subkeywords (`library`, `entry`, `feature`)
// is still recognized and the directive line is stripped in full.
TEST_F(ProtectDecryptLicenseSyntaxTest,
       DecryptLicenseRequiredOnlyFormConsumed) {
  auto result = Preprocess(
      "`pragma protect decrypt_license = ( library = \"liblic.so\" , entry = "
      "\"check\" , feature = \"core\" )\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("feature"), std::string::npos);
}

// The two optional subkeywords are independent in the grammar
// (`[ , exit ] [ , match ]`): a form that omits `exit` but supplies `match` is
// a valid keyword expression and is consumed in full.
TEST_F(ProtectDecryptLicenseSyntaxTest,
       DecryptLicenseMatchWithoutExitConsumed) {
  auto result = Preprocess(
      "`pragma protect decrypt_license = ( library = \"liblic.so\" , entry = "
      "\"check\" , feature = \"core\" , match = 0 )\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("match"), std::string::npos);
}

// The mirror image of the previous case: with the optionals independent, a form
// that supplies `exit` but omits `match` is also a valid keyword expression and
// is consumed in full. Together with the both/required-only/match-only forms
// this exhausts the four combinations of the two optional subkeywords.
TEST_F(ProtectDecryptLicenseSyntaxTest,
       DecryptLicenseExitWithoutMatchConsumed) {
  auto result = Preprocess(
      "`pragma protect decrypt_license = ( library = \"liblic.so\" , entry = "
      "\"check\" , feature = \"core\" , exit = \"release\" )\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("release"), std::string::npos);
}

// The five cases above observe the directive line going away, which any
// directive the pragma handler consumes does. What §34.5.28.1 defines is the
// spelling, and it is the first of this family whose value is a list rather
// than a string: five names inside one pair of parentheses, three of them
// required and two optional.
//
//   decrypt_license = ( library = <string> , entry = <string> ,
//       feature = <string> [, exit = <string>] [, match = <number>] )
//
// So the questions are the ones a list raises. Whether the value is kept whole,
// where it may stand among other expressions, and which near misses the reading
// turns away. What is inside it is read by nothing -- #3281 records that the
// five names are never separated from the text around them and that no library
// is ever loaded -- so a case here asks what the reading did with the
// characters and not what it made of them.

// The value in the shape the syntax line writes it: the three required names
// with strings against them, and `after` standing where the two optional names
// go, comma and all, with the parenthesis that closes the list left here.
std::string LicenseList(std::string_view after) {
  std::string list = "(library=\"liblic.so\", entry=\"checkout\", ";
  list.append("feature=\"decrypt\"").append(after).append(")");
  return list;
}

// The directive this subclause defines, carrying `list` as the pragma_value
// written against the keyword. The list is passed in whole, parentheses and
// all, because which characters stand there is the thing being observed.
std::string StatesLicense(std::string_view list) {
  std::string directive = "`pragma protect decrypt_license=";
  directive.append(list).append("\n");
  return directive;
}

// The value in effect for the keyword once `src` has been read.
ProtectKeywordValue LicenseAfter(const std::string& src) {
  return ReadKeywordScope(src).ValueOf("decrypt_license");
}

// §34.5.28.1 writes the value as a list, and §22.5.1 makes a parenthesized
// pragma_value a list of further expressions. What stands in effect afterwards
// is that list as the text wrote it, parentheses and all: the names inside are
// expressions of the value rather than expressions of the directive, so nothing
// separates them from it.
TEST(ProtectDecryptLicenseSyntax, TheValueIsTheListTheSubclauseSpells) {
  EXPECT_EQ(LicenseAfter(StatesLicense(LicenseList(""))).value,
            LicenseList(""));
}

// The two optional names in each of the four ways the brackets admit. The
// syntax line writes them as separately optional, so a text may write both,
// neither, or either one alone, and each is one value.
TEST(ProtectDecryptLicenseSyntax, EitherOptionalNameMayStandAlone) {
  EXPECT_EQ(
      LicenseAfter(StatesLicense(LicenseList(", exit=\"release\""))).value,
      LicenseList(", exit=\"release\""));
  EXPECT_EQ(LicenseAfter(StatesLicense(LicenseList(", match=1"))).value,
            LicenseList(", match=1"));
  EXPECT_EQ(
      LicenseAfter(StatesLicense(LicenseList(", exit=\"release\", match=1")))
          .value,
      LicenseList(", exit=\"release\", match=1"));
}

// §22.11 writes a directive's expressions as a comma-separated list, and this
// value holds commas of its own. The comma ending the value stands outside the
// parentheses and the ones inside belong to the list, so a reading that
// confused them would take the expression after this one for a further name of
// the licence.
TEST(ProtectDecryptLicenseSyntax, TheCommasInsideTheListAreTheValuesOwn) {
  std::string src = "`pragma protect decrypt_license=";
  src.append(LicenseList(", match=1")).append(", author=\"acme\"\n");
  ReadKeywordScope run(src);
  EXPECT_EQ(run.ValueOf("decrypt_license").value, LicenseList(", match=1"));
  EXPECT_EQ(run.ValueOf("author").value, "acme");
}

// The same directive with the licence written last, which is the mirror of the
// case above: the expression before it ends where its own comma does and the
// list that follows is one value.
TEST(ProtectDecryptLicenseSyntax, TheListReadsTheSameWrittenLast) {
  std::string src = "`pragma protect author=\"acme\", decrypt_license=";
  src.append(LicenseList("")).append("\n");
  EXPECT_EQ(ReadKeywordScope(src).ValueOf("decrypt_license").value,
            LicenseList(""));
}

// §34.5.28.1 writes a list against the keyword, and a single string is not one.
// The keyword takes what was written whatever its shape, nothing here reading
// the value for the names it should hold, so what a case can state is that the
// two spellings are told apart rather than that one of them is turned away.
TEST(ProtectDecryptLicenseSyntax, AStringAgainstTheKeywordIsNotTheList) {
  EXPECT_EQ(
      LicenseAfter("`pragma protect decrypt_license=\"liblic.so\"\n").value,
      "liblic.so");
}

// The parenthesized spelling written empty. That spelling holds a list of
// further expressions rather than an optional one, so an empty pair of
// parentheses is no pragma_value at all.
TEST(ProtectDecryptLicenseSyntax, AnEmptyListIsNoValue) {
  PreprocFixture f;
  Preprocess("`pragma protect decrypt_license=()\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

// The '=' written with nothing after it. The spelling this keyword is defined
// with has a value on the right of it, so a directive that wrote the one
// without the other wrote neither of the two spellings §22.5.1 gives a pragma
// expression.
TEST(ProtectDecryptLicenseSyntax, AnEqualsWithNoValueAfterItIsNoExpression) {
  PreprocFixture f;
  Preprocess("`pragma protect decrypt_license =\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

// A list opened and never closed. This is the closest input to the defined
// spelling the reading has to turn away: everything the syntax line writes is
// on the line, and the one character missing is the one that ends the list.
TEST(ProtectDecryptLicenseSyntax, AListLeftUnclosedIsNoValue) {
  PreprocFixture f;
  Preprocess("`pragma protect decrypt_license=(library=\"liblic.so\"\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

// §34.5.28.1 spells one name, and a name that merely opens with those
// characters is a different one. A text writing the longer one has written a
// keyword §34.4 does not tabulate, so nothing is put in effect for the one it
// resembles.
TEST(ProtectDecryptLicenseSyntax, ANameMerelyOpeningWithTheKeywordIsNotIt) {
  EXPECT_TRUE(LicenseAfter("`pragma protect decrypt_licenses=(library=\"l\")\n")
                  .defaulted);
}

}  // namespace
