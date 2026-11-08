#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "helpers_protect_viewport.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

struct ProtectViewportSyntaxTest : ::testing::Test {
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

constexpr std::string_view kObject = "top.dut.mem";
constexpr std::string_view kAccess = "read-only";

constexpr std::string_view kOpensEnvelope = "`pragma protect begin_protected\n";

constexpr std::string_view kNotTheSpelling =
    "viewport expression is written as an object and an access";

constexpr uint32_t kDirectiveLine = 2;

std::string InsideAnEnvelope(std::string_view expressions) {
  std::string src(kOpensEnvelope);
  src.append(ProtectDirective(expressions));
  return src;
}

std::string ViewportWriting(std::string_view items) {
  std::string expression = "viewport = ( ";
  expression.append(items).append(" )");
  return expression;
}

std::string BothNames() {
  std::string items = "object = \"";
  items.append(kObject).append("\" , access = \"").append(kAccess).append("\"");
  return items;
}

::testing::AssertionResult NotTheSpelling(std::string_view expressions) {
  ReadingViewports reading(InsideAnEnvelope(expressions));
  return ReportedError(reading.diag.Diagnostics(), kNotTheSpelling,
                       kDirectiveLine, "34.5.32.1");
}

TEST(ProtectViewportSyntax, TheParenthesizedObjectAndAccessIsTheSpelling) {
  ReadingViewports reading(InsideAnEnvelope(ViewportWriting(BothNames())));
  ASSERT_EQ(reading.Count(), 1U) << reading.text;
  EXPECT_EQ(reading.Viewports().front().object, kObject);
  EXPECT_EQ(reading.Viewports().front().access, kAccess);
}

TEST_F(ProtectViewportSyntaxTest,
       ViewportDirectiveStrippedSurroundingTextKept) {
  std::string result =
      Preprocess("module m;\n" + std::string(kOpensEnvelope) +
                 ViewportOf(kObject, kAccess) +
                 "`pragma protect end_protected\n" + "endmodule\n");
  EXPECT_FALSE(diag_.HasErrors());
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_EQ(result.find(kObject), std::string::npos);
  EXPECT_NE(result.find("module m;"), std::string::npos);
  EXPECT_NE(result.find("endmodule"), std::string::npos);
}

TEST(ProtectViewportSyntax, TheSpellingIsItselfBesideAnotherExpression) {
  ReadingViewports reading(
      InsideAnEnvelope("author=\"acme\", " + ViewportWriting(BothNames())));
  ASSERT_EQ(reading.Count(), 1U) << reading.text;
  EXPECT_EQ(reading.Viewports().front().object, kObject);
}

TEST(ProtectViewportSyntax, TheTwoNamesAreReadInEitherOrder) {
  std::string items = "access = \"";
  items.append(kAccess).append("\" , object = \"").append(kObject).append("\"");
  ReadingViewports reading(InsideAnEnvelope(ViewportWriting(items)));
  ASSERT_EQ(reading.Count(), 1U) << reading.text;
  EXPECT_EQ(reading.Viewports().front().object, kObject);
  EXPECT_EQ(reading.Viewports().front().access, kAccess);
}

TEST(ProtectViewportSyntax, AThirdNameLeavesTheTwoTheSubclauseWrites) {
  ReadingViewports reading(InsideAnEnvelope(
      ViewportWriting(BothNames() + " , retention = \"forever\"")));
  ASSERT_EQ(reading.Count(), 1U) << reading.text;
  EXPECT_EQ(reading.Viewports().front().access, kAccess);
}

TEST(ProtectViewportSyntax, AValueHoldingASpaceIsOneValue) {
  ReadingViewports reading(std::string(kOpensEnvelope) +
                           ViewportOf("top.dut.mem array", kAccess));
  ASSERT_EQ(reading.Count(), 1U) << reading.text;
  EXPECT_EQ(reading.Viewports().front().object, "top.dut.mem array");
}

TEST(ProtectViewportSyntax, AValueHoldingACommaIsStillOneValue) {
  ReadingViewports reading(std::string(kOpensEnvelope) +
                           ViewportOf(kObject, "read, write"));
  ASSERT_EQ(reading.Count(), 1U) << reading.text;
  EXPECT_EQ(reading.Viewports().front().access, "read, write");
}

TEST(ProtectViewportSyntax, AnEmptyStringIsAValueTheSpellingAdmits) {
  ReadingViewports reading(std::string(kOpensEnvelope) +
                           ViewportOf("", kAccess));
  ASSERT_EQ(reading.Count(), 1U) << reading.text;
  EXPECT_TRUE(reading.Viewports().front().object.empty());
}

TEST(ProtectViewportSyntax, TheKeywordStandingAloneIsReported) {
  EXPECT_TRUE(NotTheSpelling("viewport"));
}

TEST(ProtectViewportSyntax, ASingleStringAgainstTheKeywordIsReported) {
  EXPECT_TRUE(NotTheSpelling("viewport=\"" + std::string(kObject) + "\""));
}

TEST(ProtectViewportSyntax, AListLeavingTheObjectOutIsReported) {
  EXPECT_TRUE(NotTheSpelling(
      ViewportWriting("access = \"" + std::string(kAccess) + "\"")));
}

TEST(ProtectViewportSyntax, AListLeavingTheAccessOutIsReported) {
  EXPECT_TRUE(NotTheSpelling(
      ViewportWriting("object = \"" + std::string(kObject) + "\"")));
}

TEST(ProtectViewportSyntax, AnObjectWrittenBareIsReported) {
  EXPECT_TRUE(NotTheSpelling(ViewportWriting("object = top , access = \"" +
                                             std::string(kAccess) + "\"")));
}

TEST(ProtectViewportSyntax, AnObjectStandingAloneIsReported) {
  EXPECT_TRUE(NotTheSpelling(
      ViewportWriting("object , access = \"" + std::string(kAccess) + "\"")));
}

TEST(ProtectViewportSyntax, AnAccessWrittenAsANumberIsReported) {
  EXPECT_TRUE(NotTheSpelling(ViewportWriting(
      "object = \"" + std::string(kObject) + "\" , access = 3")));
}

TEST(ProtectViewportSyntax, ANameMerelyOpeningWithTheKeywordIsNotIt) {
  ReadingViewports reading(
      InsideAnEnvelope("viewports = ( " + BothNames() + " )"));
  EXPECT_EQ(reading.Count(), 0U) << reading.text;
  EXPECT_FALSE(reading.diag.HasErrors());
}

TEST(ProtectViewportSyntax, AnEscapedSpellingOfTheKeywordIsNotIt) {
  ReadingViewports reading(InsideAnEnvelope("\\viewport"));
  EXPECT_EQ(reading.Count(), 0U) << reading.text;
  EXPECT_FALSE(reading.diag.HasErrors());
}

}  // namespace
