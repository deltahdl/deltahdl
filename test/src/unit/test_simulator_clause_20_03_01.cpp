// §20.3.1 $time — the system function that reports the current simulation time
// as a 64-bit integer scaled to the time unit of the invoking module, with the
// scaled value rounded to the nearest integer because the return type is
// integral. $time's behavior depends on how its two inputs are produced: the
// current simulation time (advanced by real `#` delays) and the invoking
// module's time unit (established by a `timeunit`/`timeprecision` declaration —
// the §3.14.2.1/.2/.3 machinery this pass depends on). These tests therefore
// build that time unit from real source and drive the module through the full
// pipeline (parse → elaborate → lower → run), reading back what $time prints
// rather than stubbing the timescale or hand-scheduling a tick.
#include <sstream>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// Runs a single-module source through elaboration and simulation while
// capturing everything the run writes to stdout.
std::string RunCapture(const std::string& src, SimFixture& f) {
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  auto* design = ElaborateSrc(src, f);
  if (design != nullptr) {
    LowerAndRun(design, f);
  }
  std::cout.rdbuf(old_buf);
  return captured.str();
}

// §20.3.1: at simulation time zero $time reports zero, and it does so as an
// integer. This anchors the reported value before any delay advances the
// scheduler.
TEST(SysTaskTime, ReportsZeroAtTimeZero) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ns;\n"
      "  initial $display(\"%0d\", $time);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0\n");
}

// §20.3.1 (LRM worked example, first value): with a 10 ns unit over a 1 ns
// precision, a `#1.6` delay reaches simulation time 16 ns. Scaled to the 10 ns
// unit that is 1.6, and because $time returns an integer the value is rounded
// to the nearest integer — 2. The scaling and rounding are observed on the real
// module time unit produced by the `timeunit` declaration, not a stubbed scale.
TEST(SysTaskTime, ScalesAndRoundsUpLikeLrmExample) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 10ns;\n"
      "  timeprecision 1ns;\n"
      "  initial begin\n"
      "    #1.6;\n"
      "    $display(\"%0d\", $time);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2\n");
}

// §20.3.1 (LRM worked example, second value): a further `#1.6` delay brings the
// scheduler to 32 ns, which scaled to the 10 ns unit is 3.2 and rounds down to
// 3 — the second reported value in the LRM's example.
TEST(SysTaskTime, ScalesAndRoundsDownLikeLrmExample) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 10ns;\n"
      "  timeprecision 1ns;\n"
      "  initial begin\n"
      "    #1.6;\n"
      "    #1.6;\n"
      "    $display(\"%0d\", $time);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3\n");
}

// §20.3.1 (nearest-integer tie-break): a scaled value landing exactly halfway
// between two integers exercises the rounding conversion. `#1.5` under a 10 ns
// unit reaches 15 ns, which scaled is 1.5 and resolves upward to 2.
TEST(SysTaskTime, RoundsHalfwayValueUp) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 10ns;\n"
      "  timeprecision 1ns;\n"
      "  initial begin\n"
      "    #1.5;\n"
      "    $display(\"%0d\", $time);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2\n");
}

// §20.3.1: the time unit that governs the scaling is the *invoking module's*.
// With a 1 ns unit equal to the 1 ns precision no scaling occurs, so the same
// 16 ns simulation time that reports as 2 under a 10 ns unit reports as its
// full tick count, 16, here — showing the module's declared unit, not a fixed
// factor, controls the result.
TEST(SysTaskTime, InvokingModuleUnitControlsScaling) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ns;\n"
      "  initial begin\n"
      "    #16;\n"
      "    $display(\"%0d\", $time);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "16\n");
}

// §20.3.1 (scaling beyond a single decade): a microsecond unit over a
// nanosecond precision means a thousand ticks make one unit. `#3.6` reaches 3.6
// us, which scales and rounds to 4 — a scale factor far larger than the factor
// of ten in the worked example.
TEST(SysTaskTime, ScalesAcrossMultipleDecades) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 1us;\n"
      "  timeprecision 1ns;\n"
      "  initial begin\n"
      "    #3.6;\n"
      "    $display(\"%0d\", $time);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4\n");
}

// §20.3.1 (64-bit return type): unlike the 32-bit $stime, $time returns a full
// 64-bit time and does not truncate to the low 32 bits. With a 1 ns unit no
// scaling occurs, so a delay past 2^32 makes $time report a value that only
// fits in 64 bits (a 32-bit result would collapse it to 1). The oversized delay
// is written as a sized literal so it survives to the scheduler intact.
TEST(SysTaskTime, ReturnsFull64BitTimeNotTruncated) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ns;\n"
      "  initial begin\n"
      "    #(64'd4294967297);\n"
      "    $display(\"%0d\", $time);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4294967297\n");
}

// §20.3.1 (syntactic position: right-hand side of a procedural assignment):
// $time's scaled, rounded value is what flows out of the function wherever it
// appears, not just as a display argument. Captured into a variable at 16 ns
// under a 10 ns unit, the variable holds 2 — the same 1.6→2 result observed
// through the assignment path rather than a direct print.
TEST(SysTaskTime, ScaledValueFlowsThroughProceduralAssignment) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 10ns;\n"
      "  timeprecision 1ns;\n"
      "  integer captured;\n"
      "  initial begin\n"
      "    #1.6 captured = $time;\n"
      "    $display(\"%0d\", captured);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2\n");
}

// §20.3.1 (syntactic position: operand of an equality comparison): the scaled,
// rounded value is likewise what a relational/equality operator sees. At 16 ns
// under a 10 ns unit, `$time == 2` holds — comparing against the raw tick count
// 16 would fail, so the branch firing shows the scaling applied in operand
// position.
TEST(SysTaskTime, ScaledValueUsedAsComparisonOperand) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 10ns;\n"
      "  timeprecision 1ns;\n"
      "  initial begin\n"
      "    #1.6;\n"
      "    if ($time == 2) $display(\"scaled_match\");\n"
      "    if ($time == 16) $display(\"unscaled_match\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "scaled_match\n");
}

}  // namespace
