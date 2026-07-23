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

// Exercises $dumpportsoff/$dumpportson (§21.7.3.2) end to end: every test
// drives real source through parse, elaboration, lowering, and the scheduler
// with the driver's per-timestep recording loop installed, so the suspend and
// resume rules are observed as the production task path applies them to a dump
// opened by a real $dumpports call (§21.7.3.1). The checkpoints themselves
// reuse the 4-state suspend/resume machinery the extended VCD file inherits
// (§21.7.1.3).
class DumpportsOffOnSysTask : public VcdTestBase {
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

// §21.7.3.2: when $dumpportsoff executes with a filename naming the $dumpports
// output, a checkpoint is written in which every selected port is recorded as
// x -- the scalar as x<id> and the vector in the bx form.
TEST_F(DumpportsOffOnSysTask, DumpportsoffWritesAllXCheckpoint) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  logic [3:0] b;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    b = 4'b1010;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff(\"p.dump\");\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("$dumpoff"), std::string::npos);
  EXPECT_NE(content.find("x!"), std::string::npos);     // scalar dumped as x
  EXPECT_NE(content.find("bx \""), std::string::npos);  // vector dumped as x
}

// §21.7.3.2: after $dumpportsoff, port values are no longer dumped from that
// simulation time forward, so a later change leaves no record.
TEST_F(DumpportsOffOnSysTask, DumpportsoffStopsDumpingFromThatTimeForward) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff(\"p.dump\");\n"
                        "    #10 a = 1'b0;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("1!"), std::string::npos);  // dumped before suspend
  EXPECT_EQ(content.find("#20"), std::string::npos);
  EXPECT_EQ(content.find("0!"), std::string::npos);  // suppressed change
}

// §21.7.3.2: with no filename argument, dumping to all files opened by
// $dumpports calls is suspended.
TEST_F(DumpportsOffOnSysTask, DumpportsoffNoFilenameSuspendsAllDumpportsFiles) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff;\n"
                        "    #10 a = 1'b0;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("$dumpoff"), std::string::npos);
  EXPECT_EQ(content.find("0!"), std::string::npos);  // suppressed change
}

// §21.7.3.2: the suspend checkpoint belongs to the simulation time the task
// executed at, so its section follows that time's #<time> marker.
TEST_F(DumpportsOffOnSysTask, SuspendCheckpointFollowsItsTimeMarker) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff(\"p.dump\");\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("#10\n$dumpoff"), std::string::npos);
}

// §21.7.3.2: when $dumpportson executes with the $dumpports filename, all
// selected ports have their current values dumped -- including a value that
// changed while the dump was suspended -- and recording resumes.
TEST_F(DumpportsOffOnSysTask, DumpportsonResumesWithCurrentValues) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'hA5;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff(\"p.dump\");\n"
                        "    #5 d = 8'h3C;\n"
                        "    #5 $dumpportson(\"p.dump\");\n"
                        "    #10 d = 8'hFF;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("$dumpon"), std::string::npos);
  // §21.7.2.2: the resumed value 8'h3C prints in its shortest form.
  EXPECT_NE(content.find("b111100 !"), std::string::npos);
  // Recording is live again: the post-resume change is dumped at its time.
  EXPECT_NE(content.find("#30"), std::string::npos);
  EXPECT_NE(content.find("b11111111 !"), std::string::npos);
}

// §21.7.3.2: the resume checkpoint belongs to the simulation time the task
// executed at, so its section follows that time's #<time> marker.
TEST_F(DumpportsOffOnSysTask, ResumeCheckpointFollowsItsTimeMarker) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff(\"p.dump\");\n"
                        "    #10 $dumpportson(\"p.dump\");\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("#20\n$dumpon"), std::string::npos);
}

// §21.7.3.2: with no filename argument, dumping resumes for all files
// specified by $dumpports calls whose dumping was stopped.
TEST_F(DumpportsOffOnSysTask, DumpportsonNoFilenameResumesAllStoppedFiles) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff;\n"
                        "    #10 $dumpportson;\n"
                        "    #10 a = 1'b0;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("$dumpon"), std::string::npos);
  EXPECT_NE(content.find("#30"), std::string::npos);
  EXPECT_NE(content.find("0!"), std::string::npos);  // post-resume change
}

// §21.7.3.2: if $dumpportsoff executes while port dumping is already suspended
// for the file, the task is ignored, so no second suspend checkpoint appears.
TEST_F(DumpportsOffOnSysTask, DumpportsoffIgnoredWhenAlreadySuspended) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff(\"p.dump\");\n"
                        "    #10 $dumpportsoff(\"p.dump\");\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(CountOccurrences(content, "$dumpoff"), 1u);
}

// §21.7.3.2: if $dumpportson executes while the ports are already being dumped
// to the file, the task is ignored, so no resume checkpoint appears.
TEST_F(DumpportsOffOnSysTask, DumpportsonIgnoredWhenAlreadyDumping) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportson(\"p.dump\");\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(content.find("$dumpon"), std::string::npos);
}

// §21.7.3.2: the filename may be a string-typed variable holding the name
// given to $dumpports; the task then acts on that dump.
TEST_F(DumpportsOffOnSysTask, FilenameFromStringTypedVariable) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  string fn;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    fn = \"p.dump\";\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff(fn);\n"
                        "    #10 a = 1'b0;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("$dumpoff"), std::string::npos);
  EXPECT_EQ(content.find("0!"), std::string::npos);  // suppressed change
}

// §21.7.3.2: the filename may be an integral variable containing a character
// string -- here filled by a declaration initializer -- naming the $dumpports
// dump the task acts on.
TEST_F(DumpportsOffOnSysTask, FilenameFromIntegralVariable) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  logic [47:0] fn = \"p.dump\";\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff(fn);\n"
                        "    #10 a = 1'b0;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("$dumpoff"), std::string::npos);
  EXPECT_EQ(content.find("0!"), std::string::npos);  // suppressed change
}

// §21.7.3.2: dumping resumes without a filename only for files whose dumping
// was stopped; while the dump is live a no-argument $dumpportson has nothing
// to resume and leaves no checkpoint.
TEST_F(DumpportsOffOnSysTask, NoFilenameResumeIgnoredWhenNothingStopped) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportson;\n"
                        "    #10 a = 1'b0;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(content.find("$dumpon"), std::string::npos);
  EXPECT_NE(content.find("0!"), std::string::npos);  // dump simply continues
}

// §21.7.3.2: the resume task's filename may also be a variable holding the
// name given to $dumpports; the suspended dump it names is resumed.
TEST_F(DumpportsOffOnSysTask, ResumeFilenameFromStringTypedVariable) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  string fn;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    fn = \"p.dump\";\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff(\"p.dump\");\n"
                        "    #10 $dumpportson(fn);\n"
                        "    #10 a = 1'b0;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("$dumpon"), std::string::npos);
  EXPECT_NE(content.find("#30"), std::string::npos);
  EXPECT_NE(content.find("0!"), std::string::npos);  // post-resume change
}

// §21.7.3.2: the resume task's filename may equally be an integral variable
// containing the character string -- here filled by a procedural assignment --
// naming the $dumpports dump to resume.
TEST_F(DumpportsOffOnSysTask, ResumeFilenameFromIntegralVariable) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  logic [47:0] fn;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    fn = \"p.dump\";\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff(\"p.dump\");\n"
                        "    #10 $dumpportson(fn);\n"
                        "    #10 a = 1'b0;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("$dumpon"), std::string::npos);
  EXPECT_NE(content.find("0!"), std::string::npos);  // post-resume change
}

// §21.7.3.2: the redundant-suspend rule holds in the no-argument position too:
// once all dumping is suspended, a further bare $dumpportsoff writes no second
// checkpoint.
TEST_F(DumpportsOffOnSysTask, NoFilenameSuspendIgnoredWhenAlreadySuspended) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff;\n"
                        "    #10 $dumpportsoff;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(CountOccurrences(content, "$dumpoff"), 1u);
}

// §21.7.3.2 negative: a filename that names no $dumpports output leaves the
// dump untouched -- the task targets nothing, so dumping continues.
TEST_F(DumpportsOffOnSysTask, DumpportsoffUnknownFilenameLeavesDumpRunning) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff(\"other.vcd\");\n"
                        "    #10 a = 1'b0;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(content.find("$dumpoff"), std::string::npos);
  EXPECT_NE(content.find("#20"), std::string::npos);
  EXPECT_NE(content.find("0!"), std::string::npos);  // still recording
}

// §21.7.3.2 negative: the unknown-file rule sees through a variable-held name
// too -- a string variable naming no $dumpports output does not suspend the
// dump.
TEST_F(DumpportsOffOnSysTask, UnknownFilenameInVariableLeavesDumpRunning) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  string fn;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    fn = \"other.vcd\";\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff(fn);\n"
                        "    #10 a = 1'b0;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(content.find("$dumpoff"), std::string::npos);
  EXPECT_NE(content.find("0!"), std::string::npos);  // still recording
}

// §21.7.3.2 negative: $dumpportson naming no $dumpports output resumes
// nothing, so a dump suspended by $dumpportsoff stays suspended.
TEST_F(DumpportsOffOnSysTask, DumpportsonUnknownFilenameResumesNothing) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff(\"p.dump\");\n"
                        "    #10 $dumpportson(\"other.vcd\");\n"
                        "    #10 a = 1'b0;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(content.find("$dumpon"), std::string::npos);
  EXPECT_EQ(content.find("0!"), std::string::npos);  // still suspended
}

}  // namespace
}  // namespace delta
