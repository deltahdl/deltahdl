#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

constexpr std::string_view kSetupViolation = "$setup violation: data signal";

constexpr std::string_view kWidthViolation = "$width violation: signal";

bool DrivenToCompletion(const std::string& design, SimFixture& f) {
  auto* rtl = ElaborateSrc(design, f);
  if (rtl == nullptr || f.has_errors) return false;
  LowerAndRun(rtl, f);
  return true;
}

std::string VectorReferenceDesign(const std::string& stimulus) {
  return std::string(
             "module top(\n"
             "    output logic d,\n"
             "    output logic [5:4] clk);\n"
             "  specify\n"
             "    $setup(d, posedge clk, 73);\n"
             "  endspecify\n"
             "  initial begin\n"
             "    d = 1'b0;\n"
             "    clk = 2'b00;\n") +
         stimulus +
         "  end\n"
         "endmodule\n";
}

std::string VectorDataDesign(const std::string& stimulus) {
  return std::string(
             "module top(\n"
             "    output logic [7:4] d,\n"
             "    output logic clk);\n"
             "  specify\n"
             "    $setup(d, posedge clk, 79);\n"
             "  endspecify\n"
             "  initial begin\n"
             "    d = 4'b0000;\n"
             "    clk = 1'b0;\n") +
         stimulus +
         "  end\n"
         "endmodule\n";
}

TEST(VectorSignalsInTimingChecksDriven,
     VectorReferenceUpperBitRisingAloneIsReported) {
  SimFixture f;
  const std::string kDesign = VectorReferenceDesign(
      "    #223 d = 1'b1;\n"
      "    #11 clk = 2'b10;\n");
  ASSERT_TRUE(DrivenToCompletion(kDesign, f));
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(), kSetupViolation,
                              LineHolding(kDesign, "$setup(d, posedge clk,"),
                              "31.3.1"));
}

TEST(VectorSignalsInTimingChecksDriven,
     VectorReferenceLowerBitRisingAloneIsReported) {
  SimFixture f;
  const std::string kDesign = VectorReferenceDesign(
      "    #229 d = 1'b1;\n"
      "    #13 clk = 2'b01;\n");
  ASSERT_TRUE(DrivenToCompletion(kDesign, f));
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(), kSetupViolation,
                              LineHolding(kDesign, "$setup(d, posedge clk,"),
                              "31.3.1"));
}

TEST(VectorSignalsInTimingChecksDriven,
     VectorReferenceBothBitsRisingAtOnceReportsOnce) {
  SimFixture f;
  const std::string kDesign = VectorReferenceDesign(
      "    #233 d = 1'b1;\n"
      "    #17 clk = 2'b11;\n");
  ASSERT_TRUE(DrivenToCompletion(kDesign, f));
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(), kSetupViolation,
                              LineHolding(kDesign, "$setup(d, posedge clk,"),
                              "31.3.1"));
  std::size_t first = PositionOfFirstDiag(f, kSetupViolation);
  EXPECT_EQ(FindDiagFrom(f, first + 1, kSetupViolation), nullptr);
}

TEST(VectorSignalsInTimingChecksDriven,
     VectorDataUpperBitTransitioningAloneIsReported) {
  SimFixture f;
  const std::string kDesign = VectorDataDesign(
      "    #239 d = 4'b1000;\n"
      "    #23 clk = 1'b1;\n");
  ASSERT_TRUE(DrivenToCompletion(kDesign, f));
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(), kSetupViolation,
                              LineHolding(kDesign, "$setup(d, posedge clk,"),
                              "31.3.1"));
}

TEST(VectorSignalsInTimingChecksDriven,
     VectorDataSeveralBitsTransitioningAtOnceReportsOnce) {
  SimFixture f;
  const std::string kDesign = VectorDataDesign(
      "    #241 d = 4'b1110;\n"
      "    #29 clk = 1'b1;\n");
  ASSERT_TRUE(DrivenToCompletion(kDesign, f));
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(), kSetupViolation,
                              LineHolding(kDesign, "$setup(d, posedge clk,"),
                              "31.3.1"));
  std::size_t first = PositionOfFirstDiag(f, kSetupViolation);
  EXPECT_EQ(FindDiagFrom(f, first + 1, kSetupViolation), nullptr);
}

TEST(VectorSignalsInTimingChecksDriven,
     VectorWidthPulseOnUpperBitAloneIsReported) {
  SimFixture f;
  const std::string kDesign =
      "module top(\n"
      "    output logic [3:2] clk);\n"
      "  specify\n"
      "    $width(posedge clk, 89, 0);\n"
      "  endspecify\n"
      "  initial begin\n"
      "    clk = 2'b00;\n"
      "    #251 clk = 2'b10;\n"
      "    #31 clk = 2'b00;\n"
      "  end\n"
      "endmodule\n";
  ASSERT_TRUE(DrivenToCompletion(kDesign, f));
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(), kWidthViolation,
                              LineHolding(kDesign, "$width(posedge clk,"),
                              "31.4.4"));
}

}  // namespace
