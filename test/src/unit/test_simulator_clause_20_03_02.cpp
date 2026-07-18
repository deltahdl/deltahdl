// §20.3.2 $stime — the system function that reports the current simulation time
// as an unsigned 32-bit integer scaled to the time unit of the invoking module,
// returning only the low-order 32 bits when the scaled time does not fit in 32
// bits. Like $time, $stime's result depends on how its two inputs are produced:
// the current simulation time (advanced by real `#` delays) and the invoking
// module's time unit (established by a `timeunit`/`timeprecision` declaration —
// the §3.14.2.1/.2/.3 machinery this pass depends on). These tests therefore
// build that time unit from real source and drive the module through the full
// pipeline (parse → elaborate → lower → run), reading back what $stime prints
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

// §20.3.2: at simulation time zero $stime reports zero. This anchors the
// reported value before any delay advances the scheduler.
TEST(SysTaskStime, ReportsZeroAtTimeZero) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ns;\n"
      "  initial $display(\"%0d\", $stime);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0\n");
}

// §20.3.2 (scaled to the invoking module's unit, like $time): with a 10 ns unit
// over a 1 ns precision, ten ticks make one unit, so a `#2` delay reaches 20 ns
// (20 ticks) and $stime reports 2 — the scaled value — rather than the raw tick
// count 20. The scaling is observed on the real module unit produced by the
// `timeunit` declaration, not a stubbed scale.
TEST(SysTaskStime, ScaledToInvokingModuleUnit) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 10ns;\n"
      "  timeprecision 1ns;\n"
      "  initial begin\n"
      "    #2;\n"
      "    $display(\"%0d\", $stime);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2\n");
}

// §20.3.2: the unit that governs the scaling is the *invoking module's*. With a
// 1 ns unit equal to the 1 ns precision no scaling occurs, so a 20 ns time that
// reports as 2 under a 10 ns unit reports as its full tick count, 20, here —
// showing the module's declared unit, not a fixed factor, controls the result.
TEST(SysTaskStime, InvokingModuleUnitControlsScaling) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ns;\n"
      "  initial begin\n"
      "    #20;\n"
      "    $display(\"%0d\", $stime);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "20\n");
}

// §20.3.2 (scaling input produced via the combined timeunit/timeprecision
// declaration): a module's unit and precision may be established in one
// `timeunit <unit> / <precision>;` declaration instead of two separate
// declarations — a distinct real-source path for producing the very timescale
// $stime scales by. With a combined 10 ns / 1 ns declaration a `#3` delay
// reaches 30 ns (30 ticks), which $stime reports as the scaled 3, proving the
// scale factor is taken from the combined declaration's unit and precision
// driven through the full pipeline, not from the two-declaration form alone.
TEST(SysTaskStime, ScalesWhenUnitFromCombinedTimeunitDecl) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 10ns / 1ns;\n"
      "  initial begin\n"
      "    #3;\n"
      "    $display(\"%0d\", $stime);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3\n");
}

// §20.3.2 (32-bit return, low-order truncation — the defining property vs
// $time): with a 1 ns unit no scaling occurs, so a delay reaching 2^32 + 5
// makes the raw simulation time exceed 32 bits. $time returns the full 64-bit
// value (4294967301), while $stime returns only the low-order 32 bits (5).
// Printing both side by side pins $stime's 32-bit narrowing against $time's
// untruncated width. The oversized delay is written as a sized literal so it
// survives to the scheduler intact.
TEST(SysTaskStime, TruncatesToLow32BitsUnlikeTime) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ns;\n"
      "  initial begin\n"
      "    #(64'd4294967301);\n"
      "    $display(\"%0d %0d\", $time, $stime);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4294967301 5\n");
}

// §20.3.2 (truncation boundary edge): a time of exactly 2^32 has all of its
// low-order 32 bits clear, so $stime reports 0 rather than anything derived
// from the discarded high bit. This pins the result to precisely the low 32
// bits at the wrap boundary, complementing the just-past-boundary case.
TEST(SysTaskStime, WrapsToZeroAtExact32BitBoundary) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ns;\n"
      "  initial begin\n"
      "    #(64'd4294967296);\n"
      "    $display(\"%0d\", $stime);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0\n");
}

// §20.3.2 (scaling precedes the 32-bit narrowing): when the raw tick count
// exceeds 32 bits but the value scaled to the module unit fits, the full scaled
// value is reported. 5e9 ticks (above 2^32) reached by a `#500000000` delay
// under a 10 ns unit / 1 ns precision scales to 500,000,000, which fits in 32
// bits. Truncating the raw ticks first would instead yield 705,032,704, so the
// reported 500,000,000 proves scaling happens before the low-32-bit narrowing.
TEST(SysTaskStime, ScalesLargeTimeBeforeTruncating) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 10ns;\n"
      "  timeprecision 1ns;\n"
      "  initial begin\n"
      "    #500000000;\n"
      "    $display(\"%0d\", $stime);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "500000000\n");
}

// §20.3.2 (unsigned return, high-bit boundary): $stime returns an *unsigned*
// 32-bit quantity. A time whose top 32-bit bit is set (0x80000001) is reported
// in full as 2147483649, not sign-folded to a negative value as a signed 32-bit
// read would produce. With a 1 ns unit no scaling occurs, so the delay lands
// the scheduler exactly on that value.
TEST(SysTaskStime, ReportsFullUnsigned32BitRange) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ns;\n"
      "  initial begin\n"
      "    #(64'd2147483649);\n"
      "    $display(\"%0d\", $stime);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2147483649\n");
}

// §20.3.2 (syntactic position: right-hand side of a procedural assignment): the
// scaled value is what flows out of the function wherever it appears, not just
// as a display argument. Captured into a variable at 20 ns under a 10 ns unit,
// the variable holds 2 — the same scaled result observed through the assignment
// path rather than a direct print.
TEST(SysTaskStime, ScaledValueFlowsThroughProceduralAssignment) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 10ns;\n"
      "  timeprecision 1ns;\n"
      "  integer captured;\n"
      "  initial begin\n"
      "    #2 captured = $stime;\n"
      "    $display(\"%0d\", captured);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2\n");
}

// §20.3.2 (syntactic position: operand of an equality comparison): the scaled
// value is likewise what a relational/equality operator sees. At 20 ns under a
// 10 ns unit, `$stime == 2` holds — comparing against the raw tick count 20
// would fail, so the branch firing shows the scaling applied in operand
// position.
TEST(SysTaskStime, ScaledValueUsedAsComparisonOperand) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 10ns;\n"
      "  timeprecision 1ns;\n"
      "  initial begin\n"
      "    #2;\n"
      "    if ($stime == 2) $display(\"scaled_match\");\n"
      "    if ($stime == 20) $display(\"unscaled_match\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "scaled_match\n");
}

}  // namespace
