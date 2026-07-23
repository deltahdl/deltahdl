#include <algorithm>
#include <string>
#include <utility>
#include <vector>

// Completes the CoverageDB type that sim_context.h only forward-declares;
// included ahead of the fixtures so SimContext's inline constructor (whose
// unwind path destroys the owned coverage database) is well-formed in this TU.
#include "fixture_simulator.h"
#include "fixture_vcd.h"
#include "helpers_vcd_dump.h"
#include "simulator/coverage.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"
#include "simulator/vcd_writer.h"

namespace delta {
namespace {

// §21.7.1.4: generating a checkpoint with $dumpall. Each test drives real
// source through parse, elaboration, lowering, and the scheduler, with the
// design's own variables registered on a real writer and the driver's
// per-timestep recording loop installed (timestamp + changed values at the end
// of each time unit, the way the simulation driver dumps). This is what lets
// the checkpoint contents -- current values, unchanged variables included --
// and the changed-only recording it contrasts with be observed as the
// production task path and writer apply them, rather than by hand-driving the
// writer or hand-seeding previous values.
class DumpallSysTask : public VcdTestBase {
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

// $dumpall creates a checkpoint delimited by the $dumpall/$end keywords whose
// contents are the current values: the value the variable holds when the task
// executes appears inside the window, and the superseded earlier value does
// not.
TEST_F(DumpallSysTask, DumpallEmitsDelimitedCheckpointOfCurrentValues) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h11;\n"
      "    $dumpvars;\n"
      "    #10 data = 8'h22;\n"
      "    #10 $dumpall;\n"
      "  end\n"
      "endmodule\n");
  auto pos = content.find("$dumpall");
  ASSERT_NE(pos, std::string::npos);
  auto end = content.find("$end", pos);
  ASSERT_NE(end, std::string::npos);
  auto val = content.find("b100010 !", pos);  // current value 8'h22
  EXPECT_LT(pos, val);
  EXPECT_LT(val, end);
  // The stale initial value (8'h11) is not what the checkpoint records.
  EXPECT_EQ(content.find("b10001 !", pos), std::string::npos);
}

// The checkpoint shows the value of ALL selected variables: one that never
// changed after the starting checkpoint is still re-dumped, alongside the one
// that did change.
TEST_F(DumpallSysTask, DumpallCheckpointIncludesUnchangedVariables) {
  auto content = RunVcd(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    clk = 1; data = 8'h11;\n"
      "    $dumpvars;\n"
      "    #10 data = 8'h22;\n"
      "    #10 $dumpall;\n"
      "  end\n"
      "endmodule\n");
  auto pos = content.find("$dumpall");
  ASSERT_NE(pos, std::string::npos);
  auto end = content.find("$end", pos);
  ASSERT_NE(end, std::string::npos);
  // clk registered first (name order) -> ident '!', data -> '"'.
  auto steady = content.find("1!", pos);         // clk: unchanged, still dumped
  auto moved = content.find("b100010 \"", pos);  // data: current value
  EXPECT_LT(pos, steady);
  EXPECT_LT(steady, end);
  EXPECT_LT(pos, moved);
  EXPECT_LT(moved, end);
}

// "Current value" means the value at the moment the task executes: an
// assignment earlier in the same simulation time unit is what the checkpoint
// records.
TEST_F(DumpallSysTask, DumpallRecordsValueAssignedInSameTimeUnit) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h11;\n"
      "    $dumpvars;\n"
      "    #10 data = 8'h55;\n"
      "    $dumpall;\n"
      "  end\n"
      "endmodule\n");
  auto pos = content.find("$dumpall");
  ASSERT_NE(pos, std::string::npos);
  auto end = content.find("$end", pos);
  ASSERT_NE(end, std::string::npos);
  auto val = content.find("b1010101 !", pos);  // 8'h55, assigned this time unit
  EXPECT_LT(pos, val);
  EXPECT_LT(val, end);
}

// The checkpoint copies the genuine 4-state value: x and z bits pass through
// unlike the all-x snapshot of $dumpoff (§21.7.1.3), so a partly-z vector and
// an all-z vector keep their states.
TEST_F(DumpallSysTask, DumpallPreservesUnknownAndHighImpedanceStates) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  logic [7:0] hiz;\n"
      "  initial begin\n"
      "    data = 8'b1010zzzz;\n"
      "    hiz = 8'bz;\n"
      "    $dumpvars;\n"
      "    #10 $dumpall;\n"
      "  end\n"
      "endmodule\n");
  auto pos = content.find("$dumpall");
  ASSERT_NE(pos, std::string::npos);
  auto end = content.find("$end", pos);
  ASSERT_NE(end, std::string::npos);
  // data registered first (name order) -> ident '!', hiz -> '"'.
  auto mixed = content.find("b1010zzzz !", pos);
  auto allz = content.find("bz \"", pos);
  EXPECT_LT(pos, mixed);
  EXPECT_LT(mixed, end);
  EXPECT_LT(pos, allz);
  EXPECT_LT(allz, end);
}

// A real variable is checkpointed in its r-prefixed real form with its current
// value.
TEST_F(DumpallSysTask, DumpallRecordsRealCurrentValue) {
  auto content = RunVcd(
      "module t;\n"
      "  real r;\n"
      "  initial begin\n"
      "    r = 3.5;\n"
      "    $dumpvars;\n"
      "    #10 r = 4.25;\n"
      "    #10 $dumpall;\n"
      "  end\n"
      "endmodule\n");
  auto pos = content.find("$dumpall");
  ASSERT_NE(pos, std::string::npos);
  auto end = content.find("$end", pos);
  ASSERT_NE(end, std::string::npos);
  auto val = content.find("r4.25 !", pos);
  EXPECT_LT(pos, val);
  EXPECT_LT(val, end);
}

// While dumping is enabled, the value change dumper records the variables that
// change during each time increment; a variable that does not change during an
// increment is not re-dumped at that increment.
TEST_F(DumpallSysTask, EnabledDumpRecordsOnlyChangedVariablesPerIncrement) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] moving;\n"
      "  logic [7:0] steady;\n"
      "  initial begin\n"
      "    moving = 8'h11; steady = 8'hA5;\n"
      "    $dumpvars;\n"
      "    #10 moving = 8'h22;\n"
      "    #10 moving = 8'h33;\n"
      "  end\n"
      "endmodule\n");
  // moving registered first (name order) -> ident '!', steady -> '"'.
  auto pos10 = content.find("#10");
  ASSERT_NE(pos10, std::string::npos);
  // Each increment records the changed variable...
  EXPECT_NE(content.find("b100010 !", pos10), std::string::npos);
  EXPECT_NE(content.find("#20"), std::string::npos);
  EXPECT_NE(content.find("b110011 !", pos10), std::string::npos);
  // ...but never re-dumps the one that did not change.
  EXPECT_EQ(content.find("b10100101 \"", pos10), std::string::npos);
}

// The closest accepting counterpart of the changed-only rule: the same steady
// variable that per-increment recording skips is surfaced again the moment a
// $dumpall checkpoint runs, showing the checkpoint -- not the increments --
// re-records unchanged state.
TEST_F(DumpallSysTask, DumpallSurfacesVariableSkippedByChangeRecording) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] moving;\n"
      "  logic [7:0] steady;\n"
      "  initial begin\n"
      "    moving = 8'h11; steady = 8'hA5;\n"
      "    $dumpvars;\n"
      "    #10 moving = 8'h22;\n"
      "    #10 $dumpall;\n"
      "  end\n"
      "endmodule\n");
  auto pos10 = content.find("#10");
  ASSERT_NE(pos10, std::string::npos);
  auto all = content.find("$dumpall");
  ASSERT_NE(all, std::string::npos);
  // steady's value appears nowhere between the increment and the checkpoint...
  auto resurfaced = content.find("b10100101 \"", pos10);
  ASSERT_NE(resurfaced, std::string::npos);
  // ...its first reappearance is inside the $dumpall window.
  EXPECT_GT(resurfaced, all);
  EXPECT_LT(resurfaced, content.find("$end", all));
}

// Each $dumpall invocation emits its own checkpoint, and every checkpoint
// carries the values current at its own time.
TEST_F(DumpallSysTask, RepeatedDumpallCallsEachEmitACheckpoint) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h11;\n"
      "    $dumpvars;\n"
      "    #10 $dumpall;\n"
      "    #10 data = 8'h22;\n"
      "    #10 $dumpall;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(CountOccurrences(content, "$dumpall"), 2u);
  auto first = content.find("$dumpall");
  auto second = content.find("$dumpall", first + 1);
  ASSERT_NE(second, std::string::npos);
  // First checkpoint re-records the unchanged initial value; the second
  // records the value current at its later time.
  auto v1 = content.find("b10001 !", first);
  EXPECT_LT(first, v1);
  EXPECT_LT(v1, second);
  EXPECT_NE(content.find("b100010 !", second), std::string::npos);
}

// The full source idiom of the dump-task family: $dumpfile (§21.7.1.1) names
// the file and $dumpvars (§21.7.1.2) selects and starts the dump, both from
// real source syntax, before $dumpall generates its checkpoint. The checkpoint
// lands with the current value even with the whole sequence routed through the
// production system-call dispatch.
TEST_F(DumpallSysTask, DumpallAfterDumpfileAndDumpvarsSequence) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    $dumpfile(\"dump1.dump\");\n"
      "    data = 8'h11;\n"
      "    $dumpvars;\n"
      "    #10 data = 8'h22;\n"
      "    #10 $dumpall;\n"
      "  end\n"
      "endmodule\n");
  auto pos = content.find("$dumpall");
  ASSERT_NE(pos, std::string::npos);
  auto end = content.find("$end", pos);
  ASSERT_NE(end, std::string::npos);
  auto val = content.find("b100010 !", pos);
  EXPECT_LT(pos, val);
  EXPECT_LT(val, end);
}

// Input produced by §21.7.1.3's suspend/resume syntax: a value assigned while
// the dump was suspended is what the variable currently holds, so a $dumpall
// after the $dumpon window records that value as current.
TEST_F(DumpallSysTask, DumpallAfterSuspendResumeRecordsCurrentValue) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h11;\n"
      "    $dumpvars;\n"
      "    #10 $dumpoff;\n"
      "    #10 data = 8'h22;\n"
      "    #10 $dumpon;\n"
      "    #10 $dumpall;\n"
      "  end\n"
      "endmodule\n");
  auto pos = content.find("$dumpall");
  ASSERT_NE(pos, std::string::npos);
  auto end = content.find("$end", pos);
  ASSERT_NE(end, std::string::npos);
  // The suspended-window value is current at checkpoint time and is recorded
  // even though its change was never dumped as a value change of its own.
  auto val = content.find("b100010 !", pos);
  EXPECT_LT(pos, val);
  EXPECT_LT(val, end);
  // The initial value does not reappear in the checkpoint.
  EXPECT_EQ(content.find("b10001 !", pos), std::string::npos);
}

// The task is an ordinary task enable: invoked from a task body, $dumpall
// still generates the checkpoint.
TEST_F(DumpallSysTask, DumpallInvokedFromTaskBodyEmitsCheckpoint) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  task snapshot;\n"
      "    $dumpall;\n"
      "  endtask\n"
      "  initial begin\n"
      "    data = 8'h11;\n"
      "    $dumpvars;\n"
      "    #10 snapshot;\n"
      "  end\n"
      "endmodule\n");
  auto pos = content.find("$dumpall");
  ASSERT_NE(pos, std::string::npos);
  auto end = content.find("$end", pos);
  ASSERT_NE(end, std::string::npos);
  auto val = content.find("b10001 !", pos);
  EXPECT_LT(pos, val);
  EXPECT_LT(val, end);
}

// Negative: with no dump file in place, executing $dumpall is harmless -- the
// design still runs to completion without errors.
TEST_F(DumpallSysTask, WithoutDumpFileDumpallIsHarmless) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h11;\n"
      "    #10 $dumpall;\n"
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
