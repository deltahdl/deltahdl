// §20.3.3 $realtime — the system function that reports the current simulation
// time as a real number scaled to the time unit of the invoking module, exactly
// as $time is scaled but without the rounding to an integer that $time's
// integral return type imposes. $realtime's result depends on how its two
// inputs are produced: the current simulation time (advanced by real `#`
// delays) and the invoking module's time unit (established by a
// `timeunit`/`timeprecision` declaration — the §3.14.2.1/.2/.3 machinery this
// pass depends on). These tests therefore build that time unit from real source
// and drive the module through the full pipeline (parse → elaborate → lower →
// run), reading back what $realtime prints rather than stubbing the timescale
// or hand-scheduling a tick. A real value is displayed with %g, which renders
// the natural decimal form (1.6, 3.2) so the preserved fraction is directly
// observable.
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

// §20.3.3: at simulation time zero $realtime reports zero, and it does so as a
// real number — rendered by %g as "0". This anchors the reported value before
// any delay advances the scheduler.
TEST(SysTaskRealtime, ReportsZeroAtTimeZero) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ns;\n"
      "  initial $display(\"%g\", $realtime);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0\n");
}

// §20.3.3 (LRM worked example, second value): a further `#1.6` delay brings the
// scheduler to 32 ns, which scaled to the 10 ns unit is 3.2 — again kept as a
// real fraction, the second reported value in the LRM's example. (The first
// value, 1.6, is observed by the $time-vs-$realtime contrast test below.)
TEST(SysTaskRealtime, ScalesToRealFractionSecondValue) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 10ns;\n"
      "  timeprecision 1ns;\n"
      "  initial begin\n"
      "    #1.6;\n"
      "    #1.6;\n"
      "    $display(\"%g\", $realtime);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3.2\n");
}

// §20.3.3 (the defining distinction from $time): $realtime keeps the fraction
// that $time rounds away. At the same 16 ns simulation time under a 10 ns unit,
// $time reports the rounded integer 2 while $realtime reports 1.6. Printing
// both side by side pins $realtime's real-number result against $time's
// integral rounding — the whole reason the two functions differ.
TEST(SysTaskRealtime, KeepsFractionThatTimeRoundsAway) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 10ns;\n"
      "  timeprecision 1ns;\n"
      "  initial begin\n"
      "    #1.6;\n"
      "    $display(\"%0d %g\", $time, $realtime);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2 1.6\n");
}

// §20.3.3: the time unit that governs the scaling is the *invoking module's*.
// With a 1 ns unit equal to the 1 ns precision no scaling occurs, so the same
// 16 ns simulation time that reports as 1.6 under a 10 ns unit reports as its
// full tick count, 16, here — still a real number, showing the module's
// declared unit, not a fixed factor, controls the result.
TEST(SysTaskRealtime, InvokingModuleUnitControlsScaling) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ns;\n"
      "  initial begin\n"
      "    #16;\n"
      "    $display(\"%g\", $realtime);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "16\n");
}

// §20.3.3 (scaling input produced via the combined timeunit/timeprecision
// declaration): a module's unit and precision may be established in one
// `timeunit <unit> / <precision>;` declaration instead of two separate
// declarations — a distinct real-source path for producing the very timescale
// $realtime scales by. With a combined 10 ns / 1 ns declaration a `#2.3` delay
// reaches 23 ns, which $realtime reports as the scaled real 2.3, proving the
// scale factor is taken from the combined declaration's unit and precision
// driven through the full pipeline, not from the two-declaration form alone.
TEST(SysTaskRealtime, ScalesWhenUnitFromCombinedTimeunitDecl) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 10ns / 1ns;\n"
      "  initial begin\n"
      "    #2.3;\n"
      "    $display(\"%g\", $realtime);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2.3\n");
}

// §20.3.3 (scaling beyond a single decade): a microsecond unit over a
// nanosecond precision means a thousand ticks make one unit. `#2.5` reaches
// 2.5 us (2500 ns), which scales to the real 2.5 — a scale factor far larger
// than the factor of ten in the worked example, with the fraction preserved.
TEST(SysTaskRealtime, ScalesAcrossMultipleDecades) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 1us;\n"
      "  timeprecision 1ns;\n"
      "  initial begin\n"
      "    #2.5;\n"
      "    $display(\"%g\", $realtime);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2.5\n");
}

// §20.3.3 (syntactic position: right-hand side of a procedural assignment): the
// scaled real value is what flows out of the function wherever it appears, not
// just as a display argument. Captured into a real variable at 16 ns under a
// 10 ns unit, the variable holds 1.6 — the same real result observed through
// the assignment path rather than a direct print, and it survives in a real
// variable without losing its fraction.
TEST(SysTaskRealtime, RealValueFlowsThroughProceduralAssignment) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 10ns;\n"
      "  timeprecision 1ns;\n"
      "  real captured;\n"
      "  initial begin\n"
      "    #1.6 captured = $realtime;\n"
      "    $display(\"%g\", captured);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1.6\n");
}

// §20.3.3 (syntactic position: operand of an equality comparison): the scaled
// real value is likewise what a relational/equality operator sees, not just
// what a display or assignment consumes. Under a 10 ns unit a `#2.5` delay
// reaches 25 ns, so $realtime is the real 2.5 (exactly representable, keeping
// the comparison free of floating-point slack). `$realtime == 2.5` therefore
// holds while `$realtime == 25` — comparing against the raw tick count — does
// not, so the branch that fires shows the scaling applied in operand position.
TEST(SysTaskRealtime, RealValueUsedAsComparisonOperand) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  timeunit 10ns;\n"
      "  timeprecision 1ns;\n"
      "  initial begin\n"
      "    #2.5;\n"
      "    if ($realtime == 2.5) $display(\"scaled_match\");\n"
      "    if ($realtime == 25) $display(\"unscaled_match\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "scaled_match\n");
}

}  // namespace
