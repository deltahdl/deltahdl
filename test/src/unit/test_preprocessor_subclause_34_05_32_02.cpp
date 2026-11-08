#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "helpers_protect_viewport.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr std::string_view kObject = "dut.mem";
constexpr std::string_view kAccess = "read-only";

constexpr std::string_view kOtherObject = "dut.ctrl";

constexpr std::string_view kOwnAccess = "x-meridian-scan";

constexpr std::string_view kOpensDecryption =
    "`pragma protect begin_protected\n";
constexpr std::string_view kOpensEncryption = "`pragma protect begin\n";

constexpr std::string_view kClosesDecryption =
    "`pragma protect end_protected\n";

constexpr std::string_view kNoEnvelope =
    "viewport expression stands in no protected envelope";

constexpr std::string_view kGrantsNothing = "is not one this tool defines";

TEST(ProtectViewportDescription, ADecryptionEnvelopeIsDescribedByOneInside) {
  ReadingViewports reading(std::string(kOpensDecryption) +
                           ViewportOf(kObject, kAccess));
  ASSERT_EQ(reading.Count(), 1U) << reading.text;
  EXPECT_EQ(reading.Viewports().front().object, kObject);
}

TEST(ProtectViewportDescription, AnEncryptionRegionIsDescribedByOneInside) {
  ReadingViewports reading(std::string(kOpensEncryption) +
                           ViewportOf(kObject, kAccess));
  ASSERT_EQ(reading.Count(), 1U) << reading.text;
  EXPECT_EQ(reading.Viewports().front().object, kObject);
}

TEST(ProtectViewportDescription, TwoObjectsAreDescribedInTheOrderWritten) {
  ReadingViewports reading(std::string(kOpensDecryption) +
                           ViewportOf(kObject, kAccess) +
                           ViewportOf(kOtherObject, kAccess));
  ASSERT_EQ(reading.Count(), 2U) << reading.text;
  EXPECT_EQ(reading.Viewports().front().object, kObject);
  EXPECT_EQ(reading.Viewports().back().object, kOtherObject);
}

TEST(ProtectViewportDescription, AnExpressionInNoEnvelopeIsReported) {
  ReadingViewports reading(ViewportOf(kObject, kAccess));
  EXPECT_TRUE(
      ReportedError(reading.diag.Diagnostics(), kNoEnvelope, 1, "34.5.32.2"));
}

TEST(ProtectViewportDescription, AnExpressionInNoEnvelopeDescribesNothing) {
  ReadingViewports reading(ViewportOf(kObject, kAccess));
  EXPECT_EQ(reading.Count(), 0U) << reading.text;
  EXPECT_TRUE(
      ReportedError(reading.diag.Diagnostics(),
                    "protect pragma viewport expression stands in no protected "
                    "envelope for its object to be contained within",
                    1, "34.5.32.2"));
}

TEST(ProtectViewportDescription, TheDescriptionEndsWithTheEnvelopeItWasIn) {
  ReadingViewports reading(std::string(kOpensDecryption) +
                           ViewportOf(kObject, kAccess) +
                           std::string(kClosesDecryption));
  EXPECT_EQ(reading.Count(), 0U) << reading.text;
}

TEST(ProtectViewportDescription, AnEnvelopeOpeningInsideOneDescribesNothing) {
  ReadingViewports reading(std::string(kOpensDecryption) +
                           ViewportOf(kObject, kAccess) +
                           std::string(kOpensDecryption));
  EXPECT_EQ(reading.Count(), 0U) << reading.text;
}

TEST(ProtectViewportDescription, TheInnerEnvelopeIsDescribedByItsOwn) {
  ReadingViewports reading(
      std::string(kOpensDecryption) + ViewportOf(kObject, kAccess) +
      std::string(kOpensDecryption) + ViewportOf(kOtherObject, kAccess));
  ASSERT_EQ(reading.Count(), 1U) << reading.text;
  EXPECT_EQ(reading.Viewports().front().object, kOtherObject);
}

TEST(ProtectViewportDescription, AResetLeavesWhatTheEnvelopeWasDescribedBy) {
  ReadingViewports reading(std::string(kOpensDecryption) +
                           ViewportOf(kObject, kAccess) +
                           "`pragma protect reset\n");
  ASSERT_EQ(reading.Count(), 1U) << reading.text;
  EXPECT_EQ(reading.Viewports().front().object, kObject);
}

TEST(ProtectViewportDescription, TheAccessIsCarriedAsWritten) {
  ReadingViewports reading(std::string(kOpensDecryption) +
                           ViewportOf(kObject, kAccess));
  ASSERT_EQ(reading.Count(), 1U) << reading.text;
  EXPECT_EQ(reading.Viewports().front().access, kAccess);
}

TEST(ProtectViewportDescription, AnAccessTheStandardNeverNamesIsCarriedToo) {
  ReadingViewports reading(std::string(kOpensDecryption) +
                           ViewportOf(kObject, kOwnAccess));
  ASSERT_EQ(reading.Count(), 1U) << reading.text;
  EXPECT_EQ(reading.Viewports().front().access, kOwnAccess);
}

TEST(ProtectViewportDescription, AReadAccessDrawsNoReport) {
  ReadingViewports reading(std::string(kOpensDecryption) +
                           ViewportOf(kObject, "r"));
  EXPECT_TRUE(reading.diag.Diagnostics().empty()) << reading.text;
}

TEST(ProtectViewportDescription, AReadWriteAccessDrawsNoReport) {
  ReadingViewports reading(std::string(kOpensDecryption) +
                           ViewportOf(kObject, "rw"));
  EXPECT_TRUE(reading.diag.Diagnostics().empty()) << reading.text;
}

TEST(ProtectViewportDescription, AnUndefinedAccessIsReportedAsGrantingNothing) {
  ReadingViewports reading(std::string(kOpensDecryption) +
                           ViewportOf(kObject, kOwnAccess));
  EXPECT_TRUE(ReportedWarning(reading.diag.Diagnostics(), kGrantsNothing, 2,
                              "34.5.32.2"));
}

TEST(ProtectViewportDescription, TheReportLeavesTheViewportGathered) {
  ReadingViewports reading(std::string(kOpensDecryption) +
                           ViewportOf(kObject, kOwnAccess));
  ASSERT_EQ(reading.Count(), 1U) << reading.text;
  EXPECT_FALSE(reading.diag.HasErrors());
}

TEST(ProtectViewportDescription, AnEnvelopeAskingForNoAccessIsToldNothing) {
  ReadingViewports reading(std::string(kOpensDecryption) +
                           ProtectDirective("author = \"acme\""));
  EXPECT_TRUE(reading.diag.Diagnostics().empty()) << reading.text;
}

TEST(ProtectViewportDescription, EachUndefinedAccessIsReportedAtItsOwnLine) {
  ReadingViewports reading(std::string(kOpensDecryption) +
                           ViewportOf(kObject, kAccess) +
                           ViewportOf(kOtherObject, kOwnAccess));
  EXPECT_TRUE(ReportedWarning(reading.diag.Diagnostics(), kGrantsNothing, 2,
                              "34.5.32.2"));
  EXPECT_TRUE(ReportedWarning(reading.diag.Diagnostics(), kGrantsNothing, 3,
                              "34.5.32.2"));
}

TEST(ProtectViewportDescription, AnExpressionInNoEnvelopeIsNotAnsweredTwice) {
  ReadingViewports reading(ViewportOf(kObject, kOwnAccess));
  EXPECT_FALSE(ReportedWarning(reading.diag.Diagnostics(), kGrantsNothing, 1,
                               "34.5.32.2"));
}

TEST(ProtectViewportDescription, AnInnerEnvelopeDoesNotWipeTheOuters) {
  ReadingViewports reading(
      std::string(kOpensDecryption) + ViewportOf(kObject, kAccess) +
      std::string(kOpensDecryption) + std::string(kClosesDecryption));
  ASSERT_EQ(reading.Count(), 1U) << reading.text;
  EXPECT_EQ(reading.Viewports().front().object, kObject);
}

TEST(ProtectViewportDescription, AnInnerEnvelopeIsDescribedByItsOwnAlone) {
  ReadingViewports reading(
      std::string(kOpensDecryption) + ViewportOf(kObject, kAccess) +
      std::string(kOpensDecryption) + ViewportOf(kOtherObject, kAccess));
  ASSERT_EQ(reading.Count(), 1U) << reading.text;
  EXPECT_EQ(reading.Viewports().front().object, kOtherObject);
}

TEST(ProtectViewportDescription, TheOutersViewportsReturnWhenTheInnerCloses) {
  ReadingViewports reading(
      std::string(kOpensDecryption) + ViewportOf(kObject, kAccess) +
      std::string(kOpensDecryption) + ViewportOf(kOtherObject, kAccess) +
      std::string(kClosesDecryption));
  ASSERT_EQ(reading.Count(), 1U) << reading.text;
  EXPECT_EQ(reading.Viewports().front().object, kObject);
}

}  // namespace
