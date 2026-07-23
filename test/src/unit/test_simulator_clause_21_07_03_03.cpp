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

// Exercises $dumpportsall (§21.7.3.3) end to end: every test drives real
// source through parse, elaboration, lowering, and the scheduler with the
// driver's per-timestep recording loop installed, so the checkpoint rule is
// observed as the production task path applies it to a dump opened by a real
// $dumpports call (§21.7.3.1). The checkpoint itself reuses the 4-state
// machinery the extended VCD file inherits (§21.7.1.4).
class DumpportsallSysTask : public VcdTestBase {
 protected:
  // Runs the source through the full pipeline with the driver's dump loop
  // (timestamp + changed values at the end of each time unit) and returns the
  // dump file contents. The fixture is caller-owned so its diagnostics and
  // context stay inspectable after the run.
  std::string RunVcd(SimFixture& f, const std::string& src) {
    auto* design = ElaborateSrc(src, f);
    if (design == nullptr) return "<elaboration-failed>";
    Lowerer lowerer(f.ctx, f.arena, f.diag);
    lowerer.Lower(design);
    {
      VcdWriter vcd(tmp_path_);
      vcd.WriteHeader("1ns");
      vcd.BeginScope("t");
      // Register in name order so identifier codes are deterministic: the
      // alphabetically first variable gets '!', the next '"', and so on.
      std::vector<std::pair<std::string_view, Variable*>> vars(
          f.ctx.GetVariables().begin(), f.ctx.GetVariables().end());
      std::sort(vars.begin(), vars.end(),
                [](const auto& a, const auto& b) { return a.first < b.first; });
      for (const auto& [name, var] : vars) {
        vcd.RegisterSignal(name, var->value.width, var);
      }
      vcd.EndScope();
      vcd.EndDefinitions();
      // Value change dumping starts only once the source's $dumpports call
      // schedules its opening checkpoint.
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

// §21.7.3.3: $dumpportsall with the $dumpports filename writes a checkpoint
// section recording the current value of every selected port -- the scalar and
// the vector both appear inside the $dumpall ... $end section.
TEST_F(DumpportsallSysTask, WritesCheckpointOfAllSelectedPorts) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    d = 8'hA5;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsall(\"p.dump\");\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  auto pos = content.find("$dumpall");
  ASSERT_NE(pos, std::string::npos);
  auto end = content.find("$end", pos);
  ASSERT_NE(end, std::string::npos);
  auto section = content.substr(pos, end - pos);
  EXPECT_NE(section.find("1!"), std::string::npos);  // scalar current value
  EXPECT_NE(section.find("b10100101 \""), std::string::npos);  // vector value
}

// §21.7.3.3: the checkpoint records every selected port regardless of whether
// its value changed since the last time step -- a port that last changed long
// before the task executes is still re-recorded in the checkpoint section.
TEST_F(DumpportsallSysTask, CheckpointRecordsPortsUnchangedSinceLastStep) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    d = 8'hA5;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #5 a = 1'b0;\n"
                        "    #5 $dumpportsall(\"p.dump\");\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  auto pos = content.find("$dumpall");
  ASSERT_NE(pos, std::string::npos);
  auto end = content.find("$end", pos);
  ASSERT_NE(end, std::string::npos);
  auto section = content.substr(pos, end - pos);
  // The port that changed at #5 and the port untouched since time 0 are both
  // present with their current values.
  EXPECT_NE(section.find("0!"), std::string::npos);
  EXPECT_NE(section.find("b10100101 \""), std::string::npos);
}

// §21.7.3.3: the checkpoint shows the port values at the simulation time the
// task executed, so its section follows that time's #<time> marker (placement
// inherited from the 4-state rules, §21.7.2.4 via §21.7.3).
TEST_F(DumpportsallSysTask, CheckpointFollowsItsTimeMarker) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsall(\"p.dump\");\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("#10\n$dumpall"), std::string::npos);
}

// §21.7.3.3: dumping continues unchanged after the checkpoint -- a later value
// change is still recorded at its own time.
TEST_F(DumpportsallSysTask, DumpingContinuesAfterCheckpoint) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsall(\"p.dump\");\n"
                        "    #10 a = 1'b0;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("$dumpall"), std::string::npos);
  EXPECT_NE(content.find("#20"), std::string::npos);
  EXPECT_NE(content.find("0!"), std::string::npos);  // post-checkpoint change
}

// §21.7.3.3: the checkpoint shows the value of every selected port, and a port
// whose value is unknown at that time is recorded as x alongside the ports
// holding known values.
TEST_F(DumpportsallSysTask, CheckpointRecordsUnknownValuedPort) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  logic b;\n"
                        "  initial begin\n"
                        "    b = 1'b1;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsall(\"p.dump\");\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  auto pos = content.find("$dumpall");
  ASSERT_NE(pos, std::string::npos);
  auto end = content.find("$end", pos);
  ASSERT_NE(end, std::string::npos);
  auto section = content.substr(pos, end - pos);
  EXPECT_NE(section.find("x!"), std::string::npos);   // never-assigned port
  EXPECT_NE(section.find("1\""), std::string::npos);  // known-valued port
}

// §21.7.3.3: the checkpoint records the ports' values at the task's execution
// time even when the dump state was shaped by a suspend/resume cycle
// (§21.7.3.2) -- after resuming, $dumpportsall re-records the value that
// changed while dumping was stopped.
TEST_F(DumpportsallSysTask, CheckpointAfterSuspendResumeCycle) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff(\"p.dump\");\n"
                        "    #5 a = 1'b0;\n"
                        "    #5 $dumpportson(\"p.dump\");\n"
                        "    #10 $dumpportsall(\"p.dump\");\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  auto pos = content.find("#30\n$dumpall");
  ASSERT_NE(pos, std::string::npos);
  auto end = content.find("$end", pos);
  ASSERT_NE(end, std::string::npos);
  // The checkpoint section at #30 re-records the current value 0.
  EXPECT_NE(content.substr(pos, end - pos).find("0!"), std::string::npos);
}

// §21.7.3.3: with no filename, checkpointing occurs for all files opened by
// calls to $dumpports -- the bare form checkpoints the open dump.
TEST_F(DumpportsallSysTask, NoFilenameCheckpointsAllDumpportsFiles) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsall;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("#10\n$dumpall"), std::string::npos);
  EXPECT_NE(content.find("1!"), std::string::npos);
}

// §21.7.3.3: leaving the filename unspecified also admits the empty
// parenthesized call, which takes the same all-files default action.
TEST_F(DumpportsallSysTask, EmptyParenFormCheckpointsAllDumpportsFiles) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsall();\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("$dumpall"), std::string::npos);
  EXPECT_NE(content.find("1!"), std::string::npos);
}

// §21.7.3.3: the filename may be a string-typed variable -- here filled by a
// procedural assignment -- holding the name given to $dumpports; the dump it
// names is checkpointed.
TEST_F(DumpportsallSysTask, FilenameFromStringTypedVariable) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  string fn;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    fn = \"p.dump\";\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsall(fn);\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("$dumpall"), std::string::npos);
  EXPECT_NE(content.find("1!"), std::string::npos);
}

// §21.7.3.3: the filename may equally be an integral variable containing a
// character string -- here filled by a declaration initializer -- naming the
// $dumpports dump to checkpoint.
TEST_F(DumpportsallSysTask, FilenameFromIntegralVariable) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  logic [47:0] fn = \"p.dump\";\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsall(fn);\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("$dumpall"), std::string::npos);
  EXPECT_NE(content.find("1!"), std::string::npos);
}

// §21.7.3.3: the string-typed filename variable may equally be filled by its
// declaration initializer; the $dumpports dump it names is checkpointed.
TEST_F(DumpportsallSysTask, FilenameFromStringVariableDeclInitializer) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  string fn = \"p.dump\";\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsall(fn);\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("$dumpall"), std::string::npos);
  EXPECT_NE(content.find("1!"), std::string::npos);
}

// §21.7.3.3: the integral filename variable may equally be filled by a
// procedural assignment before the task executes; the character string it
// holds names the $dumpports dump to checkpoint.
TEST_F(DumpportsallSysTask, FilenameFromIntegralVariableProceduralAssignment) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  logic [47:0] fn;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    fn = \"p.dump\";\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsall(fn);\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("$dumpall"), std::string::npos);
  EXPECT_NE(content.find("1!"), std::string::npos);
}

// §21.7.3.3 negative: a filename that names no $dumpports output denotes no
// dump to checkpoint, so no checkpoint section is written and per-timestep
// recording simply continues.
TEST_F(DumpportsallSysTask, UnknownFilenameWritesNoCheckpoint) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsall(\"other.vcd\");\n"
                        "    #10 a = 1'b0;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(content.find("$dumpall"), std::string::npos);
  EXPECT_NE(content.find("0!"), std::string::npos);  // still recording
}

// §21.7.3.3 negative: the unknown-file rule sees through a variable-held name
// too -- a string variable naming no $dumpports output checkpoints nothing.
TEST_F(DumpportsallSysTask, UnknownFilenameInVariableWritesNoCheckpoint) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  string fn;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    fn = \"other.vcd\";\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsall(fn);\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(content.find("$dumpall"), std::string::npos);
}

}  // namespace
}  // namespace delta
