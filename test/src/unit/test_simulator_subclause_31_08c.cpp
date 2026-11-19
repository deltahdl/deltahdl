#include <gtest/gtest.h>

#include <cstddef>
#include <string>

#include "common/diagnostic.h"
#include "fixture_simulator.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

constexpr std::size_t kNotRun = 1000;

std::size_t ReportsIn(const std::string& design, const std::string& report) {
  SimFixture f;
  auto* rtl = ElaborateSrc(design, f);
  if (rtl == nullptr || f.has_errors) return kNotRun;
  LowerAndRun(rtl, f);
  std::size_t count = 0;
  for (const Diagnostic& diag : f.diag.Diagnostics()) {
    if (diag.message.rfind(report, 0) == 0) ++count;
  }
  return count;
}

std::string VectorDesign(const std::string& ports, const std::string& check,
                         const std::string& stimulus) {
  return "module top(" + ports +
         ");\n"
         "  specify\n"
         "    " +
         check +
         "\n"
         "  endspecify\n"
         "  initial begin\n"
         "    " +
         stimulus +
         "\n"
         "  end\n"
         "endmodule\n";
}

constexpr const char* kVectorPorts =
    "output logic [3:0] d, output logic [1:0] clk";

std::size_t VectorReports(const std::string& check, const std::string& stimulus,
                          const std::string& report) {
  return ReportsIn(VectorDesign(kVectorPorts, check,
                                "d = 4'b0000; clk = 2'b00; " + stimulus),
                   report);
}

constexpr const char* kReferenceThenData = "#10 clk = 2'b11; #3 d = 4'b0110;";

TEST(VectorSignalsInTimingChecksRun, BothVectorOperandsGiveOneSetupReport) {
  EXPECT_EQ(VectorReports("$setup(d, posedge clk, 50);",
                          "#10 d = 4'b1011; #3 clk = 2'b11;",
                          "$setup violation: data signal"),
            1u);
}

TEST(VectorSignalsInTimingChecksRun, HoldOverVectorsReportsOnce) {
  EXPECT_EQ(VectorReports("$hold(posedge clk, d, 10);", kReferenceThenData,
                          "$hold violation: data signal"),
            1u);
}

TEST(VectorSignalsInTimingChecksRun, SetupholdOverVectorsReportsOnce) {
  EXPECT_EQ(
      VectorReports("$setuphold(posedge clk, d, 10, 10);", kReferenceThenData,
                    "$setuphold violation: data signal"),
      1u);
}

TEST(VectorSignalsInTimingChecksRun, RecoveryOverVectorsReportsOnce) {
  EXPECT_EQ(VectorReports("$recovery(posedge clk, d, 10);", kReferenceThenData,
                          "$recovery violation: data signal"),
            1u);
}

TEST(VectorSignalsInTimingChecksRun, RemovalOverVectorsReportsOnce) {
  EXPECT_EQ(VectorReports("$removal(posedge clk, d, 10);",
                          "#10 d = 4'b0110; #3 clk = 2'b11;",
                          "$removal violation: data signal"),
            1u);
}

TEST(VectorSignalsInTimingChecksRun, RecremOverVectorsReportsOnce) {
  EXPECT_EQ(VectorReports("$recrem(posedge clk, d, 10, 10);",
                          kReferenceThenData, "$recrem violation: data signal"),
            1u);
}

TEST(VectorSignalsInTimingChecksRun, SkewOverVectorsReportsOnce) {
  EXPECT_EQ(VectorReports("$skew(posedge clk, d, 2);", kReferenceThenData,
                          "$skew violation: data signal"),
            1u);
}

TEST(VectorSignalsInTimingChecksRun, TimeskewOverVectorsReportsOnce) {
  EXPECT_EQ(
      VectorReports("$timeskew(posedge clk, d, 2, , 1, 0);", kReferenceThenData,
                    "$timeskew violation: data signal"),
      1u);
}

TEST(VectorSignalsInTimingChecksRun, FullskewOverVectorsReportsOnce) {
  EXPECT_EQ(ReportsIn(VectorDesign("output logic [3:0] d = 4'b0000, "
                                   "output logic [1:0] clk = 2'b00",
                                   "$fullskew(posedge clk, d, 2, 2, , 1, 0);",
                                   kReferenceThenData),
                      "$fullskew violation: signals"),
            1u);
}

TEST(VectorSignalsInTimingChecksRun, NochangeOverVectorsReportsOnce) {
  EXPECT_EQ(VectorReports("$nochange(posedge clk, d, 0, 0);",
                          "#10 clk = 2'b11; #3 d = 4'b0110; #3 clk = 2'b00;",
                          "$nochange violation: data signal"),
            1u);
}

TEST(VectorSignalsInTimingChecksRun, PeriodSeesAnEdgeOnAnyBit) {
  EXPECT_EQ(VectorReports("$period(posedge clk, 20);",
                          "#10 clk = 2'b01; #3 clk = 2'b00; #3 clk = 2'b10;",
                          "$period violation: signal"),
            1u);
  EXPECT_EQ(VectorReports("$period(posedge clk, 20);",
                          "#10 clk = 2'b01; #3 clk = 2'b00; #30 clk = 2'b10;",
                          "$period violation: signal"),
            0u);
}

TEST(VectorSignalsInTimingChecksRun, WidthWithAllBitsChangingReportsOnce) {
  EXPECT_EQ(VectorReports("$width(posedge clk, 20);",
                          "#10 clk = 2'b11; #5 clk = 2'b00;",
                          "$width violation: signal"),
            1u);
}

TEST(VectorSignalsInTimingChecksRun, BitsRisingAndFallingTogetherAreOneChange) {
  EXPECT_EQ(VectorReports("$setup(d, posedge clk, 50);",
                          "d = 4'b0011; #10 d = 4'b1100; #3 clk = 2'b01;",
                          "$setup violation: data signal"),
            1u);
}

TEST(VectorSignalsInTimingChecksRun, DffExampleReportsOneViolation) {
  const std::string kDesign =
      "module DFF (Q, CLK, DAT);\n"
      "  input CLK;\n"
      "  input [7:0] DAT;\n"
      "  output [7:0] Q;\n"
      "  reg [7:0] Q;\n"
      "  always @(posedge CLK)\n"
      "    Q = DAT;\n"
      "  specify\n"
      "    $setup (DAT, posedge CLK, 10);\n"
      "  endspecify\n"
      "endmodule\n"
      "module top;\n"
      "  reg clk;\n"
      "  reg [7:0] dat;\n"
      "  wire [7:0] q;\n"
      "  DFF ff(q, clk, dat);\n"
      "  initial begin\n"
      "    clk = 1'b0;\n"
      "    dat = 'b00101110;\n"
      "    #100 dat = 'b01010011;\n"
      "    #5 clk = 1'b1;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(ReportsIn(kDesign, "$setup violation: data signal"), 1u);
}

TEST(VectorSignalsInTimingChecksRun, NotifierTogglesOnceForSeveralBits) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top(output logic [7:0] d, output logic clk);\n"
                       "  reg n = 1'b0;\n"
                       "  specify\n"
                       "    $setup(d, posedge clk, 10, n);\n"
                       "  endspecify\n"
                       "  initial begin\n"
                       "    d = 'b00101110;\n"
                       "    clk = 1'b0;\n"
                       "    #100 d = 'b01010011;\n"
                       "    #5 clk = 1'b1;\n"
                       "    #10 $display(\"%b\", n);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1\n");
}

std::string PartSelectDesign(const std::string& change) {
  return VectorDesign(
      "output logic [7:0] d, output logic clk",
      "$setup(d[3:0], posedge clk, 10);",
      "d = 8'h00; clk = 1'b0; #20 d = " + change + "; #5 clk = 1'b1;");
}

TEST(VectorSignalsInTimingChecksRun, PartSelectSeesOnlyItsBits) {
  EXPECT_EQ(ReportsIn(PartSelectDesign("8'b0000_1110"),
                      "$setup violation: data signal"),
            1u);
  EXPECT_EQ(ReportsIn(PartSelectDesign("8'b1110_0000"),
                      "$setup violation: data signal"),
            0u);
}

std::string ConditionedVectorDesign(const std::string& e) {
  return "module top(output logic [3:0] d, output logic clk);\n"
         "  logic e;\n"
         "  wire en = e;\n"
         "  specify\n"
         "    $setup(d, posedge clk &&& en, 50);\n"
         "  endspecify\n"
         "  initial begin\n"
         "    d = 4'b0000; clk = 1'b0; e = " +
         e +
         ";\n"
         "    #10 d = 4'b1011; #3 clk = 1'b1;\n"
         "  end\n"
         "endmodule\n";
}

TEST(VectorSignalsInTimingChecksRun, ConditionedVectorCheckReportsOnce) {
  EXPECT_EQ(ReportsIn(ConditionedVectorDesign("1'b1"),
                      "$setup violation: data signal"),
            1u);
  EXPECT_EQ(ReportsIn(ConditionedVectorDesign("1'b0"),
                      "$setup violation: data signal"),
            0u);
}

}  // namespace
