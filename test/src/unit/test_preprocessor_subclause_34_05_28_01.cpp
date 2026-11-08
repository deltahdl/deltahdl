#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_preprocessor.h"
#include "helpers_protect_keyword_value.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_keywords.h"
#include "preprocessor/protect_license.h"

using namespace delta;

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

TEST_F(ProtectDecryptLicenseSyntaxTest, PragmaProtectDecryptLicenseConsumed) {
  auto result = Preprocess(
      "`pragma protect decrypt_license = ( library = \"liblic.so\" , entry = "
      "\"check\" , feature = \"core\" , exit = \"release\" , match = 1 )\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("decrypt_license"), std::string::npos);
  EXPECT_EQ(result.find("liblic.so"), std::string::npos);
}

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

TEST_F(ProtectDecryptLicenseSyntaxTest,
       DecryptLicenseRequiredOnlyFormConsumed) {
  auto result = Preprocess(
      "`pragma protect decrypt_license = ( library = \"liblic.so\" , entry = "
      "\"check\" , feature = \"core\" )\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("feature"), std::string::npos);
}

TEST_F(ProtectDecryptLicenseSyntaxTest,
       DecryptLicenseMatchWithoutExitConsumed) {
  auto result = Preprocess(
      "`pragma protect decrypt_license = ( library = \"liblic.so\" , entry = "
      "\"check\" , feature = \"core\" , match = 0 )\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("match"), std::string::npos);
}

TEST_F(ProtectDecryptLicenseSyntaxTest,
       DecryptLicenseExitWithoutMatchConsumed) {
  auto result = Preprocess(
      "`pragma protect decrypt_license = ( library = \"liblic.so\" , entry = "
      "\"check\" , feature = \"core\" , exit = \"release\" )\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("release"), std::string::npos);
}

std::string LicenseList(std::string_view after) {
  std::string list = "(library=\"liblic.so\", entry=\"checkout\", ";
  list.append("feature=\"decrypt\"").append(after).append(")");
  return list;
}

std::string StatesLicense(std::string_view list) {
  std::string directive = "`pragma protect decrypt_license=";
  directive.append(list).append("\n");
  return directive;
}

ProtectKeywordValue LicenseAfter(const std::string& src) {
  return ReadKeywordScope(src).ValueOf("decrypt_license");
}

TEST(ProtectDecryptLicenseSyntax, TheValueIsTheListTheSubclauseSpells) {
  EXPECT_EQ(LicenseAfter(StatesLicense(LicenseList(""))).value,
            LicenseList(""));
}

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

TEST(ProtectDecryptLicenseSyntax, TheCommasInsideTheListAreTheValuesOwn) {
  std::string src = "`pragma protect decrypt_license=";
  src.append(LicenseList(", match=1")).append(", author=\"acme\"\n");
  ReadKeywordScope run(src);
  EXPECT_EQ(run.ValueOf("decrypt_license").value, LicenseList(", match=1"));
  EXPECT_EQ(run.ValueOf("author").value, "acme");
}

TEST(ProtectDecryptLicenseSyntax, TheListReadsTheSameWrittenLast) {
  std::string src = "`pragma protect author=\"acme\", decrypt_license=";
  src.append(LicenseList("")).append("\n");
  EXPECT_EQ(ReadKeywordScope(src).ValueOf("decrypt_license").value,
            LicenseList(""));
}

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

TEST(ProtectDecryptLicenseSyntax, AnEmptyListIsNoValue) {
  PreprocFixture f;
  Preprocess("`pragma protect decrypt_license=()\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

TEST(ProtectDecryptLicenseSyntax, AnEqualsWithNoValueAfterItIsNoExpression) {
  PreprocFixture f;
  Preprocess("`pragma protect decrypt_license =\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

TEST(ProtectDecryptLicenseSyntax, AListLeftUnclosedIsNoValue) {
  PreprocFixture f;
  Preprocess("`pragma protect decrypt_license=(library=\"liblic.so\"\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

TEST(ProtectDecryptLicenseSyntax, ANameMerelyOpeningWithTheKeywordIsNotIt) {
  EXPECT_TRUE(LicenseAfter("`pragma protect decrypt_licenses=(library=\"l\")\n")
                  .defaulted);
}

TEST(ProtectDecryptLicenseSyntax, TheFullListOutlivesTheStringValuedArray) {
  const std::string kFiveNames = LicenseList(", exit=\"revoke\", match=7");
  const ProtectKeywordValue kRecorded = LicenseAfter(StatesLicense(kFiveNames));
  EXPECT_FALSE(kRecorded.defaulted);
  EXPECT_EQ(kRecorded.value, kFiveNames);
}

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

TEST(ProtectDecryptLicenseSyntax,
     TheOptionalNamesAreAbsentWhereTheTextOmitsThem) {
  ProtectLicense license = ParseProtectLicense(LicenseList(""));
  ASSERT_TRUE(license.stated);
  EXPECT_FALSE(license.has_exit);
  EXPECT_FALSE(license.has_match);
}

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

TEST(ProtectDecryptLicenseSyntax, ALibraryWrittenAsABareWordNamesNoLibrary) {
  EXPECT_FALSE(ParseProtectLicense("(library=liblic.so, entry=\"checkout\", "
                                   "feature=\"decrypt\")")
                   .stated);
}

TEST(ProtectDecryptLicenseSyntax, AMatchWrittenAsAStringStatesNoNumber) {
  ProtectLicense license = ParseProtectLicense(LicenseList(", match=\"7\""));
  ASSERT_TRUE(license.stated);
  EXPECT_FALSE(license.has_match);
}

TEST(ProtectDecryptLicenseSyntax, ANameStandingAloneCarriesNothing) {
  EXPECT_FALSE(
      ParseProtectLicense("(library, entry=\"checkout\", feature=\"decrypt\")")
          .stated);
  ProtectLicense license = ParseProtectLicense(LicenseList(", match"));
  ASSERT_TRUE(license.stated);
  EXPECT_FALSE(license.has_match);
}

TEST(ProtectDecryptLicenseSyntax, AMatchThatIsNotAllDigitsStatesNoNumber) {
  EXPECT_FALSE(ParseProtectLicense(LicenseList(", match=7x")).has_match);
  EXPECT_FALSE(ParseProtectLicense(LicenseList(", match=")).has_match);
}

TEST(ProtectDecryptLicenseSyntax, AMatchTooLargeToHoldStatesNoNumber) {
  EXPECT_FALSE(ParseProtectLicense(LicenseList(", match=18446744073709551616"))
                   .has_match);
  ProtectLicense largest =
      ParseProtectLicense(LicenseList(", match=18446744073709551615"));
  ASSERT_TRUE(largest.has_match);
  EXPECT_EQ(largest.match, 18446744073709551615ULL);
}

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
