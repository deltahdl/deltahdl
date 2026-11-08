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

struct ProtectRuntimeLicenseSyntaxTest : ::testing::Test {
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

TEST_F(ProtectRuntimeLicenseSyntaxTest, PragmaProtectRuntimeLicenseConsumed) {
  auto result = Preprocess(
      "`pragma protect runtime_license = ( library = \"liblic.so\" , entry = "
      "\"check\" , feature = \"core\" , exit = \"release\" , match = 1 )\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("runtime_license"), std::string::npos);
  EXPECT_EQ(result.find("liblic.so"), std::string::npos);
}

TEST_F(ProtectRuntimeLicenseSyntaxTest,
       RuntimeLicenseDirectiveStrippedSurroundingTextKept) {
  auto result = Preprocess(
      "module m;\n"
      "`pragma protect runtime_license = ( library = \"liblic.so\" , entry = "
      "\"check\" , feature = \"core\" )\n"
      "endmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("liblic.so"), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

TEST_F(ProtectRuntimeLicenseSyntaxTest,
       RuntimeLicenseMatchWithoutExitConsumed) {
  auto result = Preprocess(
      "`pragma protect runtime_license = ( library = \"liblic.so\" , entry = "
      "\"check\" , feature = \"core\" , match = 0 )\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("match"), std::string::npos);
}

TEST_F(ProtectRuntimeLicenseSyntaxTest,
       RuntimeLicenseExitWithoutMatchConsumed) {
  auto result = Preprocess(
      "`pragma protect runtime_license = ( library = \"liblic.so\" , entry = "
      "\"check\" , feature = \"core\" , exit = \"release\" )\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find("release"), std::string::npos);
}

std::string LicenseList(std::string_view after) {
  std::string list = "(library=\"liblic.so\", entry=\"checkout\", ";
  list.append("feature=\"simulate\"").append(after).append(")");
  return list;
}

std::string StatesLicense(std::string_view list) {
  std::string directive = "`pragma protect runtime_license=";
  directive.append(list).append("\n");
  return directive;
}

ProtectKeywordValue LicenseAfter(const std::string& src) {
  return ReadKeywordScope(src).ValueOf("runtime_license");
}

TEST(ProtectRuntimeLicenseSyntax, TheValueIsTheListTheSubclauseSpells) {
  EXPECT_EQ(LicenseAfter(StatesLicense(LicenseList(""))).value,
            LicenseList(""));
}

TEST(ProtectRuntimeLicenseSyntax, EitherOptionalNameMayStandAlone) {
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

TEST(ProtectRuntimeLicenseSyntax, TheCommasInsideTheListAreTheValuesOwn) {
  std::string src = "`pragma protect runtime_license=";
  src.append(LicenseList(", match=1")).append(", author=\"acme\"\n");
  ReadKeywordScope run(src);
  EXPECT_EQ(run.ValueOf("runtime_license").value, LicenseList(", match=1"));
  EXPECT_EQ(run.ValueOf("author").value, "acme");
}

TEST(ProtectRuntimeLicenseSyntax, TheListReadsTheSameWrittenLast) {
  std::string src = "`pragma protect author=\"acme\", runtime_license=";
  src.append(LicenseList("")).append("\n");
  EXPECT_EQ(ReadKeywordScope(src).ValueOf("runtime_license").value,
            LicenseList(""));
}

TEST(ProtectRuntimeLicenseSyntax, AStringAgainstTheKeywordIsNotTheList) {
  PreprocFixture f;
  Preprocess("`pragma protect runtime_license=\"liblic.so\"\n", f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "protect pragma runtime_license expression is written "
                    "as a library, an entry and a feature, each "
                    "against a string",
                    1, "34.5.29.1"));
}

TEST(ProtectRuntimeLicenseSyntax, AnEmptyListIsNoValue) {
  PreprocFixture f;
  Preprocess("`pragma protect runtime_license=()\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

TEST(ProtectRuntimeLicenseSyntax, AnEqualsWithNoValueAfterItIsNoExpression) {
  PreprocFixture f;
  Preprocess("`pragma protect runtime_license =\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

TEST(ProtectRuntimeLicenseSyntax, AListLeftUnclosedIsNoValue) {
  PreprocFixture f;
  Preprocess("`pragma protect runtime_license=(library=\"liblic.so\"\n", f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "malformed pragma_expression after pragma_name", 1,
                            "22.11"));
}

TEST(ProtectRuntimeLicenseSyntax, ANameMerelyOpeningWithTheKeywordIsNotIt) {
  EXPECT_TRUE(LicenseAfter("`pragma protect runtime_licenses=(library=\"l\")\n")
                  .defaulted);
}

TEST(ProtectRuntimeLicenseSyntax, EveryNameOfTheListSurvivesTheKeywordArray) {
  constexpr std::string_view kSpelledOut =
      "(library=\"libgrant.so\", entry=\"acquire\", feature=\"execute\", "
      "exit=\"surrender\", match=9)";
  EXPECT_EQ(LicenseAfter(StatesLicense(kSpelledOut)).value, kSpelledOut);
  EXPECT_FALSE(LicenseAfter(StatesLicense(kSpelledOut)).defaulted);
}

TEST(ProtectRuntimeLicenseSyntax, TheFiveNamesAreReadOutOfTheList) {
  ProtectLicense license =
      ParseProtectLicense(LicenseList(", exit=\"revoke\", match=7"));
  ASSERT_TRUE(license.stated);
  EXPECT_EQ(license.library, "liblic.so");
  EXPECT_EQ(license.entry, "checkout");
  EXPECT_EQ(license.feature, "simulate");
  EXPECT_TRUE(license.has_exit);
  EXPECT_EQ(license.exit, "revoke");
  EXPECT_TRUE(license.has_match);
  EXPECT_EQ(license.match, 7U);
}

TEST(ProtectRuntimeLicenseSyntax,
     TheNamesAreReadForThemselvesWhateverTheOrder) {
  ProtectLicense license = ParseProtectLicense(
      "(match=7, exit=\"revoke\", feature=\"simulate\", "
      "entry=\"checkout\", library=\"liblic.so\")");
  ASSERT_TRUE(license.stated);
  EXPECT_EQ(license.library, "liblic.so");
  EXPECT_EQ(license.entry, "checkout");
  EXPECT_EQ(license.feature, "simulate");
}

TEST(ProtectRuntimeLicenseSyntax,
     TheOptionalNamesAreAbsentWhereTheTextOmitsThem) {
  ProtectLicense license = ParseProtectLicense(LicenseList(""));
  ASSERT_TRUE(license.stated);
  EXPECT_FALSE(license.has_exit);
  EXPECT_FALSE(license.has_match);
}

TEST(ProtectRuntimeLicenseSyntax, AListShortOfARequiredNameStatesNoLicence) {
  EXPECT_FALSE(
      ParseProtectLicense("(entry=\"checkout\", feature=\"simulate\")").stated);
  EXPECT_FALSE(
      ParseProtectLicense("(library=\"liblic.so\", feature=\"simulate\")")
          .stated);
  EXPECT_FALSE(
      ParseProtectLicense("(library=\"liblic.so\", entry=\"checkout\")")
          .stated);
}

TEST(ProtectRuntimeLicenseSyntax, ALibraryWrittenAsABareWordNamesNoLibrary) {
  EXPECT_FALSE(ParseProtectLicense("(library=liblic.so, entry=\"checkout\", "
                                   "feature=\"simulate\")")
                   .stated);
}

TEST(ProtectRuntimeLicenseSyntax, AMatchWrittenAsAStringStatesNoNumber) {
  ProtectLicense license = ParseProtectLicense(LicenseList(", match=\"7\""));
  ASSERT_TRUE(license.stated);
  EXPECT_FALSE(license.has_match);
}

TEST(ProtectRuntimeLicenseSyntax, AListShortOfARequiredNameIsReported) {
  PreprocFixture f;
  Preprocess(
      "`pragma protect runtime_license=(library=\"liblic.so\", "
      "entry=\"checkout\")\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "protect pragma runtime_license expression is written "
                    "as a library, an entry and a feature, each "
                    "against a string",
                    1, "34.5.29.1"));
}

}  // namespace
