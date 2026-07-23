#include <algorithm>
#include <string>
#include <utility>
#include <vector>

#include "fixture_simulator.h"
#include "fixture_vcd.h"
#include "helpers_vcd_dump.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"
#include "simulator/vcd_writer.h"

namespace delta {
namespace {

// §21.7.1.3: suspending and resuming the dump with $dumpoff/$dumpon. Each test
// drives real source through parse, elaboration, lowering, and the scheduler,
// with the design's own variables registered on a real writer and the driver's
// per-timestep recording loop installed (timestamp + changed values at the end
// of each time unit, the way the simulation driver dumps). This is what lets
// the suspend window, the all-x checkpoint, the value-at-resume checkpoint,
// and the start-of-dumping time be observed as the production task path and
// writer apply them, rather than by hand-driving the writer.
class DumpOffOnSysTask : public VcdTestBase {
 protected:
  std::string RunVcd(const std::string& src) {
    SimFixture f;
    auto* design = ElaborateSrc(src, f);
    if (design == nullptr) return "<elaboration-failed>";
    Lowerer lowerer(f.ctx, f.arena, f.diag);
    lowerer.Lower(design);
    {
      VcdWriter vcd(tmp_path_);
      vcd.WriteHeader("1ns");
      // Register in name order so identifier codes are deterministic: the
      // alphabetically first variable gets '!', the next '"', and so on.
      std::vector<std::pair<std::string_view, Variable*>> vars(
          f.ctx.GetVariables().begin(), f.ctx.GetVariables().end());
      std::sort(vars.begin(), vars.end(),
                [](const auto& a, const auto& b) { return a.first < b.first; });
      for (const auto& [name, var] : vars) {
        vcd.RegisterSignal(name, var->value.width, var);
      }
      vcd.EndDefinitions();
      // Value change dumping starts once the source's $dumpvars executes.
      vcd.ArmDumpvarsStart();
      f.ctx.SetVcdWriter(&vcd);
      f.scheduler.SetPostTimestepCallback([&vcd, &f]() {
        vcd.WriteTimestamp(f.ctx.CurrentTime().ticks);
        vcd.DumpChangedValues(0);
      });
      f.scheduler.Run();
    }  // writer destructor flushes the dump to tmp_path_ before ReadVcd
    return ReadVcd();
  }
};

// Executing $dumpvars causes the value change dumping to start at the end of
// the current simulation time unit: a change made after the $dumpvars call but
// within the same time unit is still recorded at that time.
TEST_F(DumpOffOnSysTask, DumpingStartsAtEndOfCurrentTimeUnit) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h11;\n"
      "    #10 data = 8'h22;\n"
      "    $dumpvars;\n"
      "    data = 8'h33;\n"
      "    #10 data = 8'h44;\n"
      "  end\n"
      "endmodule\n");
  // The checkpoint records the value at execution (8'h22)...
  auto cp = content.find("$dumpvars");
  ASSERT_NE(cp, std::string::npos);
  EXPECT_NE(content.find("b100010 !", cp), std::string::npos);
  // ...and the end of time unit 10 records the later same-unit value 8'h33.
  EXPECT_NE(content.find("#10"), std::string::npos);
  EXPECT_NE(content.find("b110011 !"), std::string::npos);
}

// The dump has not started before $dumpvars executes: a value change in an
// earlier time unit is not recorded, and no earlier simulation time appears.
TEST_F(DumpOffOnSysTask, NoChangesRecordedBeforeDumpvarsExecutes) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h11;\n"
      "    #5 data = 8'h45;\n"
      "    #5 data = 8'h22;\n"
      "    $dumpvars;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(content.find("#5"), std::string::npos);         // pre-start time
  EXPECT_EQ(content.find("b1000101"), std::string::npos);   // 8'h45 never seen
  EXPECT_NE(content.find("b100010 !"), std::string::npos);  // checkpoint value
}

// The argumented form of $dumpvars starts the dump the same way: a scoped
// selection (§21.7.1.2's level/scope-list syntax) takes a different checkpoint
// path than the no-argument call, and dumping likewise begins at the end of
// its time unit with nothing earlier recorded.
TEST_F(DumpOffOnSysTask, ScopedDumpvarsAlsoStartsTheDump) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h11;\n"
      "    #5 data = 8'h45;\n"
      "    #5 data = 8'h22;\n"
      "    $dumpvars(0, data);\n"
      "    data = 8'h33;\n"
      "    #10 data = 8'h44;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(content.find("#5"), std::string::npos);        // pre-start time
  EXPECT_EQ(content.find("b1000101"), std::string::npos);  // 8'h45 never seen
  auto cp = content.find("$dumpvars");
  ASSERT_NE(cp, std::string::npos);
  EXPECT_NE(content.find("b100010 !", cp), std::string::npos);  // at execution
  EXPECT_NE(content.find("#10"), std::string::npos);
  EXPECT_NE(content.find("b110011 !"), std::string::npos);  // end-of-unit value
}

// When $dumpoff executes, a checkpoint is made in which every selected
// variable is dumped as an x value: a scalar as x<ident>, a vector as
// bx <ident>, delimited by the $dumpoff/$end keywords.
TEST_F(DumpOffOnSysTask, DumpoffCheckpointRecordsEveryVariableAsX) {
  auto content = RunVcd(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    clk = 1; data = 8'hA5;\n"
      "    $dumpvars;\n"
      "    #10 $dumpoff;\n"
      "  end\n"
      "endmodule\n");
  auto off = content.find("$dumpoff");
  ASSERT_NE(off, std::string::npos);
  auto end = content.find("$end", off);
  ASSERT_NE(end, std::string::npos);
  // clk registered first (name order) -> ident '!', data -> '"'.
  auto xs = content.find("x!", off);
  auto xv = content.find("bx \"", off);
  EXPECT_LT(off, xs);
  EXPECT_LT(xs, end);
  EXPECT_LT(off, xv);
  EXPECT_LT(xv, end);
}

// The checkpoint records x regardless of the variable's actual value: a
// variable holding z is still written as x, showing the $dumpoff record is an
// all-x snapshot and not a copy of the current value.
TEST_F(DumpOffOnSysTask, DumpoffRecordsZValuedVariableAsX) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'bz;\n"
      "    $dumpvars;\n"
      "    #10 $dumpoff;\n"
      "  end\n"
      "endmodule\n");
  // The $dumpvars checkpoint shows the true value (z)...
  auto cp = content.find("$dumpvars");
  ASSERT_NE(cp, std::string::npos);
  EXPECT_NE(content.find("bz !", cp), std::string::npos);
  // ...while the suspend checkpoint replaces it with x.
  auto off = content.find("$dumpoff");
  ASSERT_NE(off, std::string::npos);
  auto end = content.find("$end", off);
  auto xv = content.find("bx !", off);
  EXPECT_LT(off, xv);
  EXPECT_LT(xv, end);
  EXPECT_EQ(content.find("bz", off), std::string::npos);
}

// A real variable has no x state and its VCD value form is the r-prefixed real
// number, so the suspend checkpoint records it as r0 rather than a bit-form x.
TEST_F(DumpOffOnSysTask, DumpoffRecordsRealVariableAsRealZero) {
  auto content = RunVcd(
      "module t;\n"
      "  real r;\n"
      "  initial begin\n"
      "    r = 1.5;\n"
      "    $dumpvars;\n"
      "    #10 $dumpoff;\n"
      "  end\n"
      "endmodule\n");
  auto off = content.find("$dumpoff");
  ASSERT_NE(off, std::string::npos);
  EXPECT_NE(content.find("r0 !", off), std::string::npos);
  EXPECT_EQ(content.find("bx", off), std::string::npos);
}

// In the interval between $dumpoff and $dumpon, no value changes are dumped:
// the suspended-window change appears at no simulation time of its own, and
// its value surfaces only in the later $dumpon checkpoint.
TEST_F(DumpOffOnSysTask, NoValueChangesDumpedWhileSuspended) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h11;\n"
      "    $dumpvars;\n"
      "    #10 data = 8'h22;\n"
      "    #10 $dumpoff;\n"
      "    #10 data = 8'h33;\n"
      "    #10 $dumpon;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(content.find("#30"), std::string::npos);  // suspended time unit
  auto on = content.find("$dumpon");
  ASSERT_NE(on, std::string::npos);
  // 8'h33 first appears inside the $dumpon checkpoint, not as an earlier
  // recorded change.
  EXPECT_GT(content.find("b110011"), on);
}

// The closest accepting counterpart: the same changes with no $dumpoff in
// force are dumped normally, so the suppression above is the tasks' doing.
TEST_F(DumpOffOnSysTask, SameChangesAreDumpedWhenNotSuspended) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h11;\n"
      "    $dumpvars;\n"
      "    #10 data = 8'h22;\n"
      "    #20 data = 8'h33;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("#30"), std::string::npos);
  EXPECT_NE(content.find("b110011 !"), std::string::npos);
}

// When $dumpon is executed, each variable is dumped with its value at that
// time -- including one that changed while the dump was suspended -- and
// dumping then resumes, so a later change is recorded normally.
TEST_F(DumpOffOnSysTask, DumponResumesWithValueAtThatTime) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h11;\n"
      "    $dumpvars;\n"
      "    #10 $dumpoff;\n"
      "    #10 data = 8'h33;\n"
      "    #20 $dumpon;\n"
      "    #10 data = 8'h44;\n"
      "  end\n"
      "endmodule\n");
  auto on = content.find("$dumpon");
  ASSERT_NE(on, std::string::npos);
  auto end = content.find("$end", on);
  ASSERT_NE(end, std::string::npos);
  // The value at resume time (8'h33) is in the checkpoint...
  auto val = content.find("b110011 !", on);
  EXPECT_LT(on, val);
  EXPECT_LT(val, end);
  // ...and recording is live again: the post-resume change is dumped.
  EXPECT_NE(content.find("#50"), std::string::npos);
  EXPECT_NE(content.find("b1000100 !"), std::string::npos);
}

// The value-at-resume rule holds for a real variable too: a real assigned
// while suspended is re-dumped in the r-prefixed form with its value at the
// time $dumpon executes, and the suspended-interval time never appears.
TEST_F(DumpOffOnSysTask, DumponRecordsRealValueAtResumeTime) {
  auto content = RunVcd(
      "module t;\n"
      "  real r;\n"
      "  initial begin\n"
      "    r = 1.5;\n"
      "    $dumpvars;\n"
      "    #10 $dumpoff;\n"
      "    #10 r = 2.25;\n"
      "    #10 $dumpon;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(content.find("#20"), std::string::npos);  // suspended time unit
  auto on = content.find("$dumpon");
  ASSERT_NE(on, std::string::npos);
  auto end = content.find("$end", on);
  ASSERT_NE(end, std::string::npos);
  auto val = content.find("r2.25 !", on);
  EXPECT_LT(on, val);
  EXPECT_LT(val, end);
}

// The $dumpon checkpoint covers each variable, not only the ones that changed
// while suspended: a variable holding its pre-suspension value is re-dumped
// with that same value.
TEST_F(DumpOffOnSysTask, DumponCheckpointIncludesUnchangedVariables) {
  auto content = RunVcd(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    clk = 1; data = 8'h11;\n"
      "    $dumpvars;\n"
      "    #10 $dumpoff;\n"
      "    #10 data = 8'h33;\n"
      "    #10 $dumpon;\n"
      "  end\n"
      "endmodule\n");
  auto on = content.find("$dumpon");
  ASSERT_NE(on, std::string::npos);
  auto end = content.find("$end", on);
  ASSERT_NE(end, std::string::npos);
  auto steady = content.find("1!", on);         // clk unchanged, still dumped
  auto moved = content.find("b110011 \"", on);  // data's value at resume
  EXPECT_LT(on, steady);
  EXPECT_LT(steady, end);
  EXPECT_LT(on, moved);
  EXPECT_LT(moved, end);
}

// The LRM's example shape: the two tasks bound the simulation period during
// which the dump takes place, over repeated windows. Dumping runs in
// [10, 210) and [1010, 1910); changes inside a window are recorded, changes
// while suspended or after the final $dumpoff are not.
TEST_F(DumpOffOnSysTask, ExampleWindowsBoundTheDumpPeriod) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h01;\n"
      "    #10   $dumpvars;\n"
      "    #200  $dumpoff;\n"
      "    #800  $dumpon;\n"
      "    #900  $dumpoff;\n"
      "  end\n"
      "  initial begin\n"
      "    #100 data = 8'h0A;\n"  // t=100: inside the first window
      "    #400 data = 8'h0B;\n"  // t=500: suspended
      "    #600 data = 8'h0C;\n"  // t=1100: inside the second window
      "    #900 data = 8'h0D;\n"  // t=2000: after the final $dumpoff
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(CountOccurrences(content, "$dumpoff"), 2u);
  EXPECT_EQ(CountOccurrences(content, "$dumpon"), 1u);
  // First window records the t=100 change.
  EXPECT_NE(content.find("#100"), std::string::npos);
  EXPECT_NE(content.find("b1010 !"), std::string::npos);
  // The suspended-interval change is not recorded at its own time; its value
  // first surfaces in the $dumpon checkpoint.
  EXPECT_EQ(content.find("#500"), std::string::npos);
  EXPECT_GT(content.find("b1011"), content.find("$dumpon"));
  // Second window records the t=1100 change.
  EXPECT_NE(content.find("#1100"), std::string::npos);
  EXPECT_NE(content.find("b1100 !"), std::string::npos);
  // After the final $dumpoff nothing further is dumped.
  EXPECT_EQ(content.find("#2000"), std::string::npos);
  EXPECT_EQ(content.find("b1101"), std::string::npos);
}

// The tasks are ordinary task enables: invoked from a task body, $dumpoff
// still suspends the dump from that point on.
TEST_F(DumpOffOnSysTask, DumpoffInvokedFromTaskBodySuspends) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  task stopdump;\n"
      "    $dumpoff;\n"
      "  endtask\n"
      "  initial begin\n"
      "    data = 8'h11;\n"
      "    $dumpvars;\n"
      "    #10 stopdump;\n"
      "    #10 data = 8'h22;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("$dumpoff"), std::string::npos);
  EXPECT_EQ(content.find("#20"), std::string::npos);
  EXPECT_EQ(content.find("b100010"), std::string::npos);
}

// Repeated suspend/resume cycles each emit their own checkpoint, opening and
// closing a fresh window every time.
TEST_F(DumpOffOnSysTask, RepeatedSuspendResumeCycles) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h11;\n"
      "    $dumpvars;\n"
      "    #10 $dumpoff;\n"
      "    #10 $dumpon;\n"
      "    #10 $dumpoff;\n"
      "    #10 $dumpon;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(CountOccurrences(content, "$dumpoff"), 2u);
  EXPECT_EQ(CountOccurrences(content, "$dumpon"), 2u);
}

// With no dump file in place, executing the suspend/resume tasks is harmless:
// the design still runs to completion without errors.
TEST_F(DumpOffOnSysTask, WithoutDumpFileTasksAreHarmless) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h11;\n"
      "    #10 $dumpoff;\n"
      "    #10 $dumpon;\n"
      "    #10 data = 8'h22;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.GetVcdWriter(), nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
}  // namespace delta
