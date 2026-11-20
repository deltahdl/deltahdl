#include <gtest/gtest.h>

#include <cstdint>
#include <fstream>
#include <ios>
#include <string>

#include "fixture_sdf_design.h"
#include "fixture_simulator.h"
#include "simulator/sdf_parser.h"
#include "simulator/specify.h"
#include "simulator/specify_sdf.h"

using namespace delta;

namespace {

const char* const kTwoDriversOneLoadSrc =
    "module drv_cell(out);\n"
    "  output out;\n"
    "  reg out;\n"
    "endmodule\n"
    "module load_cell(in);\n"
    "  input in;\n"
    "  wire in;\n"
    "endmodule\n"
    "module board;\n"
    "  wire n;\n"
    "  drv_cell i13(.out(n));\n"
    "  drv_cell i11(.out(n));\n"
    "  load_cell i15(.in(n));\n"
    "endmodule\n";

struct Limits {
  bool found = false;
  uint64_t delay = 0;
  uint64_t reject = 0;
  uint64_t error = 0;
};

struct WireLimits : SdfDesign {
  bool Ready() {
    if (!Lower(kTwoDriversOneLoadSrc)) return false;
    mgr.BindDesignInterconnect(CollectInterconnectTopology(*cu, Top()));
    return true;
  }

  void Annotate(const std::string& delay_sections) {
    SdfFile parsed;
    ASSERT_TRUE(
        ParseSdf("(DELAYFILE (CELL (CELLTYPE \"board\") (INSTANCE u1) " +
                     delay_sections + "))",
                 parsed));
    AnnotateSdfToManager(parsed, mgr, SdfMtm::kTypical);
  }

  Limits From(const char* source) const {
    Limits got;
    const InterconnectDelay* wire = mgr.FindInterconnectDelay(source, "i15/in");
    if (wire == nullptr) return got;
    got.found = true;
    got.delay = wire->delays[0];
    got.reject = wire->reject_limit[0];
    got.error = wire->error_limit[0];
    return got;
  }
};

std::string AbsoluteThenIncrement(const std::string& absolute,
                                  const std::string& increment) {
  return "(DELAY (ABSOLUTE " + absolute + ")) (DELAY (INCREMENT " + increment +
         "))";
}

void ExpectLimits(const Limits& got, uint64_t delay, uint64_t reject,
                  uint64_t error) {
  ASSERT_TRUE(got.found);
  EXPECT_EQ(got.delay, delay);
  EXPECT_EQ(got.reject, reject);
  EXPECT_EQ(got.error, error);
}

TEST(SdfInterconnectPulseLimitIncrement,
     DISABLED_InterconnectBelowZeroStopsAtZero) {
  WireLimits w;
  ASSERT_TRUE(w.Ready());
  w.Annotate(
      AbsoluteThenIncrement("(INTERCONNECT i13/out i15/in ((10) (4) (6)))",
                            "(INTERCONNECT i13/out i15/in (() (-6) (-8)))"));
  ExpectLimits(w.From("i13/out"), 10, 0, 0);
}

TEST(SdfInterconnectPulseLimitIncrement,
     DISABLED_InterconnectWithinRangeSubtracts) {
  WireLimits w;
  ASSERT_TRUE(w.Ready());
  w.Annotate(
      AbsoluteThenIncrement("(INTERCONNECT i13/out i15/in ((10) (4) (6)))",
                            "(INTERCONNECT i13/out i15/in (() (-1) (-2)))"));
  ExpectLimits(w.From("i13/out"), 10, 3, 4);
}

TEST(SdfInterconnectPulseLimitIncrement, InterconnectAddsToTheLimits) {
  WireLimits w;
  ASSERT_TRUE(w.Ready());
  w.Annotate(
      AbsoluteThenIncrement("(INTERCONNECT i13/out i15/in ((10) (4) (6)))",
                            "(INTERCONNECT i13/out i15/in (() (1) (2)))"));
  ExpectLimits(w.From("i13/out"), 10, 5, 8);
}

TEST(SdfInterconnectPulseLimitIncrement, InterconnectWithADelayAmountMovesAll) {
  WireLimits w;
  ASSERT_TRUE(w.Ready());
  w.Annotate(
      AbsoluteThenIncrement("(INTERCONNECT i13/out i15/in ((10) (4) (6)))",
                            "(INTERCONNECT i13/out i15/in ((2) (1) (2)))"));
  ExpectLimits(w.From("i13/out"), 12, 5, 8);
}

TEST(SdfInterconnectPulseLimitIncrement,
     DISABLED_PortHoldsOnlyTheLimitGoingNegative) {
  WireLimits w;
  ASSERT_TRUE(w.Ready());
  w.Annotate(AbsoluteThenIncrement("(PORT i15/in ((10) (4) (6)))",
                                   "(PORT i15/in (() (-6) (-1)))"));
  ExpectLimits(w.From("i13/out"), 10, 0, 5);
  ExpectLimits(w.From("i11/out"), 10, 0, 5);
}

TEST(SdfInterconnectPulseLimitIncrement,
     DISABLED_NetdelayOnTheNetBelowZeroStopsAtZero) {
  WireLimits w;
  ASSERT_TRUE(w.Ready());
  w.Annotate(AbsoluteThenIncrement("(NETDELAY n ((10) (4) (6)))",
                                   "(NETDELAY n (() (-5) (-7)))"));
  ExpectLimits(w.From("i13/out"), 10, 0, 0);
  ExpectLimits(w.From("i11/out"), 10, 0, 0);
}

TEST(SdfInterconnectPulseLimitIncrement,
     DISABLED_NetdelayOnThePortWithinRangeSubtracts) {
  WireLimits w;
  ASSERT_TRUE(w.Ready());
  w.Annotate(AbsoluteThenIncrement("(NETDELAY i15/in ((10) (4) (6)))",
                                   "(NETDELAY i15/in (() (-2) (-3)))"));
  ExpectLimits(w.From("i13/out"), 10, 2, 3);
  ExpectLimits(w.From("i11/out"), 10, 2, 3);
}

TEST(SdfInterconnectPulseLimitIncrement,
     DISABLED_SourceSeededFromAPortBelowZeroStopsAtZero) {
  WireLimits w;
  ASSERT_TRUE(w.Ready());
  w.Annotate(
      AbsoluteThenIncrement("(PORT i15/in ((10) (4) (6)))",
                            "(INTERCONNECT i13/out i15/in (() (-6) (-8)))"));
  ExpectLimits(w.From("i13/out"), 10, 0, 0);
  ExpectLimits(w.From("i11/out"), 10, 4, 6);
}

void ExpectPercentLimitsFrom(const std::string& entry) {
  WireLimits w;
  ASSERT_TRUE(w.Ready());
  w.mgr.SetGlobalPulseLimitPercents(40, 80);
  w.Annotate("(DELAY (ABSOLUTE " + entry + "))");
  ExpectLimits(w.From("i13/out"), 10, 4, 8);
  ExpectLimits(w.From("i11/out"), 10, 4, 8);
}

TEST(SdfInterconnectPulseLimitPercent, PortDerivesTheLimitsFromThePercentages) {
  ExpectPercentLimitsFrom("(PORT i15/in (10))");
}

TEST(SdfInterconnectPulseLimitPercent,
     NetdelayOnThePortDerivesTheLimitsFromThePercentages) {
  ExpectPercentLimitsFrom("(NETDELAY i15/in (10))");
}

TEST(SdfInterconnectPulseLimitPercent,
     NetdelayOnTheNetDerivesTheLimitsFromThePercentages) {
  ExpectPercentLimitsFrom("(NETDELAY n (10))");
}

std::string PulseThroughPath(const std::string& stem,
                             const std::string& pathpulse) {
  const std::string kPath = "/tmp/delta_c32_07b_" + stem + ".sdf";
  std::ofstream out(kPath, std::ios::trunc);
  out << "(DELAYFILE (CELL (CELLTYPE \"buf_cell\") (INSTANCE top/c) "
         "(DELAY (ABSOLUTE (PATHPULSE a y " +
             pathpulse + ")))))\n";
  out.close();
  SimFixture f;
  return RunCapture(
      "module buf_cell(input a, output y);\n"
      "  assign y = a;\n"
      "  specify\n"
      "    (a => y) = 7;\n"
      "  endspecify\n"
      "endmodule\n"
      "module top;\n"
      "  logic in;\n"
      "  wire out;\n"
      "  buf_cell c(.a(in), .y(out));\n"
      "  always @(out) if ($time > 0) $display(\"t=%0t y=%b\", $time, out);\n"
      "  initial begin\n"
      "    $sdf_annotate(\"" +
          kPath +
          "\");\n"
          "    in = 1;\n"
          "    #10 in = 0;\n"
          "    #4 in = 1;\n"
          "  end\n"
          "endmodule\n",
      f);
}

TEST(SdfPulseLimitRun, LimitsAboveTheDelayRejectAsLimitsAtTheDelay) {
  const std::string kAtTheDelay = PulseThroughPath("at", "(7) (7)");
  EXPECT_EQ(kAtTheDelay, "t=7 y=1\n");
  EXPECT_EQ(PulseThroughPath("above", "(10) (20)"), kAtTheDelay);
}

TEST(SdfPulseLimitRun, AnErrorLimitAboveTheDelayFiltersAsOneAtTheDelay) {
  const std::string kAtTheDelay = PulseThroughPath("err_at", "(3) (7)");
  EXPECT_EQ(kAtTheDelay, "t=7 y=1\nt=17 y=x\nt=21 y=1\n");
  EXPECT_EQ(PulseThroughPath("err_above", "(3) (12)"), kAtTheDelay);
}

TEST(SdfPulseLimitRun, LimitsBelowThePulseLetItThrough) {
  EXPECT_EQ(PulseThroughPath("below", "(2) (3)"),
            "t=7 y=1\nt=17 y=0\nt=21 y=1\n");
}

}  // namespace
