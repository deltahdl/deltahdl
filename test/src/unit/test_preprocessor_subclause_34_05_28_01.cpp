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
#include "preprocessor/protect_license.h"
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
// turns away, and then what the reading makes of the characters it kept.
// ParseProtectLicense (src/preprocessor/protect_license.h) separates the five
// names, and Preprocessor::ApplyLicense
// (src/preprocessor/preprocessor_protect_license.cpp) reports a value written
// in any other spelling than this one. What is still done with the names is
// nothing: #3443 records that no library is loaded, no entry function is
// called and no return value is compared.

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
// A string names no library to load, so there is no entry function in one for
// a feature to be asked about, and the expression states no licence for a tool
// to be held to.
TEST(ProtectDecryptLicenseSyntax, AStringAgainstTheKeywordIsNotTheList) {
  PreprocFixture f;
  Preprocess("`pragma protect decrypt_license=\"liblic.so\"\n", f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "protect pragma decrypt_license expression is written "
                    "as a library, an entry and a feature, each "
                    "against a string",
                    1, "34.5.28.1"));
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

// §34.5.28.1 defines the keyword with a list, so `decrypt_license` is absent
// from kStringValuedKeywords in src/preprocessor/protect_keywords.cpp. That
// array names the keywords §34.5 defines as `keyword = <string>`, and
// ProtectKeywordScope::Apply records nothing for one of them written with a
// parenthesized value, §22.5.1 making such a value a list of further
// expressions rather than one written thing. #3269 named this keyword among the
// ones to put in that array, and the syntax line is why it is not there: a list
// is the only value the keyword is ever written with, so a membership would
// refuse every spelling the subclause defines. This case is what turns that
// addition red, the five names being recorded here and a keyword in the array
// leaving the value empty and defaulted.
TEST(ProtectDecryptLicenseSyntax, TheFullListOutlivesTheStringValuedArray) {
  const std::string kFiveNames = LicenseList(", exit=\"revoke\", match=7");
  const ProtectKeywordValue kRecorded = LicenseAfter(StatesLicense(kFiveNames));
  EXPECT_FALSE(kRecorded.defaulted);
  EXPECT_EQ(kRecorded.value, kFiveNames);
}

// -- What the names inside the list are read as ------------------------------

// §34.5.28.1 writes five names inside the parentheses, and this is all five
// read back out. ParseProtectLicense (src/preprocessor/protect_license.h) is
// what separates them from the text around them.
//
// The number is 7 rather than 0 because 0 is what ProtectLicense::match holds
// where nothing wrote one, so a reading that never took the value would answer
// this case correctly.
TEST(ProtectDecryptLicenseSyntax, TheFiveNamesAreReadOutOfTheList) {
  ProtectLicense license =
      ParseProtectLicense(LicenseList(", exit=\"revoke\", match=7"));
  ASSERT_TRUE(license.stated);
  EXPECT_EQ(license.library, "liblic.so");
  EXPECT_EQ(license.entry, "checkout");
  EXPECT_EQ(license.feature, "decrypt");
  EXPECT_TRUE(license.has_exit);
  EXPECT_EQ(license.exit, "revoke");
  EXPECT_TRUE(license.has_match);
  EXPECT_EQ(license.match, 7U);
}

// The names are expressions of a list rather than positions in one, so each is
// read for itself. §22.5.1 spells the value as a list of pragma expressions,
// which name what they carry. The order here is the reverse of the syntax
// line's, which is what a reading taking the first string for the library
// would fail.
TEST(ProtectDecryptLicenseSyntax,
     TheNamesAreReadForThemselvesWhateverTheOrder) {
  ProtectLicense license = ParseProtectLicense(
      "(match=7, exit=\"revoke\", feature=\"decrypt\", "
      "entry=\"checkout\", library=\"liblic.so\")");
  ASSERT_TRUE(license.stated);
  EXPECT_EQ(license.library, "liblic.so");
  EXPECT_EQ(license.entry, "checkout");
  EXPECT_EQ(license.feature, "decrypt");
}

// The two optional names left out. §34.4 has a tool use a keyword's default
// value where the keyword is absent, and no default is stated for either of
// these: not in §34.5.28.1, not in the Description beside it, and not in Table
// 34-1, which carries a name and a description and no default column at all.
// So the absence is recorded as an absence rather than filled in.
//
// It matters most for the number. Zero is the value the NOTE in the
// Description has a forged library return in order to pass the check, so a
// licence read as stating zero would be read as asking for exactly the
// comparison that NOTE describes.
TEST(ProtectDecryptLicenseSyntax,
     TheOptionalNamesAreAbsentWhereTheTextOmitsThem) {
  ProtectLicense license = ParseProtectLicense(LicenseList(""));
  ASSERT_TRUE(license.stated);
  EXPECT_FALSE(license.has_exit);
  EXPECT_FALSE(license.has_match);
}

// Each of the three names the syntax line writes outside the brackets, left out
// in turn. The Description spends all three in the one sentence that carries
// the check out -- the tool loads the library, calls the entry function in it,
// and passes that function the feature string -- so a list short of any one of
// them asks for nothing that can be carried out. Taking them one at a time is
// what tells a reading that requires all three from one that requires only the
// first.
TEST(ProtectDecryptLicenseSyntax, AListShortOfARequiredNameStatesNoLicence) {
  EXPECT_FALSE(
      ParseProtectLicense("(entry=\"checkout\", feature=\"decrypt\")").stated);
  EXPECT_FALSE(
      ParseProtectLicense("(library=\"liblic.so\", feature=\"decrypt\")")
          .stated);
  EXPECT_FALSE(
      ParseProtectLicense("(library=\"liblic.so\", entry=\"checkout\")")
          .stated);
}

// §34.5.28.1 writes a <string> against each of the three, and §22.5.1 spells a
// string with the quotation marks around it. A bare word is one of the other
// three spellings a pragma_value has, so a list writing one names no library
// however much the characters read like a file name.
TEST(ProtectDecryptLicenseSyntax, ALibraryWrittenAsABareWordNamesNoLibrary) {
  EXPECT_FALSE(ParseProtectLicense("(library=liblic.so, entry=\"checkout\", "
                                   "feature=\"decrypt\")")
                   .stated);
}

// §34.5.28.1 writes a <number> against match, so a value written as a string
// states none. The licence still stands, match being optional, and what it
// states is a licence with no number to compare against rather than one whose
// number is whatever the string reads like.
TEST(ProtectDecryptLicenseSyntax, AMatchWrittenAsAStringStatesNoNumber) {
  ProtectLicense license = ParseProtectLicense(LicenseList(", match=\"7\""));
  ASSERT_TRUE(license.stated);
  EXPECT_FALSE(license.has_match);
}

// The same list met as a directive rather than handed to the reading, so that
// what the preprocessor does with it is what is observed. §34.5.28.1 is what
// the report cites, the spelling being what the list failed.
TEST(ProtectDecryptLicenseSyntax, AListShortOfARequiredNameIsReported) {
  PreprocFixture f;
  Preprocess(
      "`pragma protect decrypt_license=(library=\"liblic.so\", "
      "entry=\"checkout\")\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "protect pragma decrypt_license expression is written "
                    "as a library, an entry and a feature, each "
                    "against a string",
                    1, "34.5.28.1"));
}

}  // namespace
