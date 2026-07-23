#include <algorithm>
#include <iostream>
#include <sstream>
#include <string>
#include <utility>
#include <vector>

// Completes the CoverageDB type that sim_context.h only forward-declares;
// included ahead of the fixtures so SimContext's inline constructor (whose
// unwind path destroys the owned coverage database) is well-formed in this TU.
#include "fixture_simulator.h"
#include "fixture_vcd.h"
#include "simulator/coverage.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"
#include "simulator/vcd_writer.h"

namespace delta {
namespace {

// Exercises $dumpportsflush (§21.7.3.5) end to end: every test drives real
// source through parse, elaboration, lowering, and the scheduler with the
// driver's per-timestep recording loop installed, so the buffer-flushing rule
// is observed as the production task path applies it to a dump opened by a
// real $dumpports call (§21.7.3.1). The rule's observable is the dump file's
// on-disk contents WHILE the simulation still runs, so each flushing test
// plays the role of the reader from the $dumpflush machinery the extended VCD
// file inherits (§21.7.1.6): procedural code in the design opens the dump
// file mid-run, echoes its current bytes to stdout between marker lines, and
// closes it again. The captured echo is the mid-simulation snapshot the
// assertions inspect alongside the final file contents.
class DumpportsflushSysTask : public VcdTestBase {
 protected:
  // Runs the source through the full pipeline with the driver's dump loop
  // (timestamp + changed values at the end of each time unit), capturing
  // stdout produced during the run so mid-simulation reader snippets can be
  // inspected afterwards. The fixture is caller-owned so its diagnostics and
  // context stay inspectable after the run. Returns the final dump contents.
  std::string RunVcd(SimFixture& f, const std::string& src) {
    run_output_.clear();
    auto* design = ElaborateSrc(src, f);
    if (design == nullptr) return "<elaboration-failed>";
    Lowerer lowerer(f.ctx, f.arena, f.diag);
    lowerer.Lower(design);
    std::ostringstream captured;
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
      std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
      f.scheduler.Run();
      std::cout.rdbuf(old_buf);
    }  // writer destructor flushes the dump to tmp_path_ before ReadVcd
    run_output_ = captured.str();
    return ReadVcd();
  }

  // SV statements playing the mid-simulation reader: open the dump file, echo
  // its current contents to stdout delimited by <tag>-BEGIN/<tag>-END marker
  // lines, and close it. The enclosing module must declare the integer
  // variables rfd and rch.
  std::string ReaderSnippet(const std::string& tag) const {
    return "$display(\"" + tag + "-BEGIN\");\n" +  //
           "rfd = $fopen(\"" + tmp_path_ + "\", \"r\");\n" +
           "rch = $fgetc(rfd);\n" + "while (rch != -1) begin\n" +
           "  $write(\"%c\", rch);\n" + "  rch = $fgetc(rfd);\n" + "end\n" +
           "$fclose(rfd);\n" + "$display(\"" + tag + "-END\");\n";
  }

  // The mid-simulation dump snapshot echoed between the tag's marker lines.
  std::string MidDump(const std::string& tag) const {
    const std::string begin_marker = tag + "-BEGIN\n";
    auto b = run_output_.find(begin_marker);
    auto e = run_output_.find(tag + "-END");
    if (b == std::string::npos || e == std::string::npos) {
      return "<no-snapshot>";
    }
    b += begin_marker.size();
    return run_output_.substr(b, e - b);
  }

  std::string run_output_;
};

// §21.7.3.5: $dumpportsflush with the $dumpports filename writes all buffered
// port values out to the associated file, clearing the simulator's VCD
// buffer. A reader running during the same simulation therefore finds the
// earlier timestamp and the vector change already on disk right after the
// task executes.
TEST_F(DumpportsflushSysTask, NamedFlushStoresBufferedRecordsMidSimulation) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  logic [7:0] d;\n"
                        "  integer rfd;\n"
                        "  integer rch;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 d = 8'hA5;\n"
                        "    #10 begin\n"
                        "      $dumpportsflush(\"p.dump\");\n" +
                            ReaderSnippet("MID") +
                            "    end\n"
                            "  end\n"
                            "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  auto mid = MidDump("MID");
  EXPECT_NE(mid.find("#10"), std::string::npos);
  EXPECT_NE(mid.find("b10100101 "), std::string::npos);
  EXPECT_NE(content.find("b10100101 "), std::string::npos);
}

// §21.7.3.5 baseline: the flush rule exists because simulators buffer VCD
// output instead of writing line by line. Without a $dumpportsflush call, the
// same mid-simulation reader does NOT yet find the recorded change on disk --
// the record is still sitting in the buffer -- which is what makes the
// flushing tests' positive observations discriminating.
TEST_F(DumpportsflushSysTask, WithoutFlushBufferedRecordsNotYetOnDisk) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  logic [7:0] d;\n"
                        "  integer rfd;\n"
                        "  integer rch;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 d = 8'hA5;\n"
                        "    #10 begin\n" +
                            ReaderSnippet("MID") +
                            "    end\n"
                            "  end\n"
                            "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(MidDump("MID").find("b10100101 "), std::string::npos);
  // The record does reach the file once the writer closes at end of run.
  EXPECT_NE(content.find("b10100101 "), std::string::npos);
}

// §21.7.3.5: the flush only empties the buffer -- it inserts no command text
// into the dump, and dumping continues exactly as before, so a change after
// the flush is still recorded under its own timestamp.
TEST_F(DumpportsflushSysTask, FlushEmitsNoCommandAndDumpingContinues) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsflush(\"p.dump\");\n"
                        "    #10 d = 8'hA5;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(content.find("flush"), std::string::npos);
  auto t20 = content.find("#20");
  ASSERT_NE(t20, std::string::npos);
  EXPECT_NE(content.find("b10100101 ", t20), std::string::npos);
}

// §21.7.3.5: if the filename is not specified, the VCD buffers shall be
// flushed for all files opened by calls to $dumpports -- the bare form with
// no argument list flushes this dump's buffer to disk mid-simulation.
TEST_F(DumpportsflushSysTask, NoArgFlushCoversAllDumpportsFiles) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  logic a;\n"
         "  logic [7:0] d;\n"
         "  integer rfd;\n"
         "  integer rch;\n"
         "  initial begin\n"
         "    a = 1'b1;\n"
         "    d = 8'h00;\n"
         "    $dumpports(, \"p.dump\");\n"
         "    #10 d = 8'hA5;\n"
         "    #10 begin\n"
         "      $dumpportsflush;\n" +
             ReaderSnippet("MID") +
             "    end\n"
             "  end\n"
             "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(MidDump("MID").find("b10100101 "), std::string::npos);
}

// §21.7.3.5: the empty-parenthesis spelling of the no-filename call performs
// the same default action, flushing the buffers of every $dumpports file.
TEST_F(DumpportsflushSysTask, EmptyParenFlushSameDefaultAction) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  logic a;\n"
         "  logic [7:0] d;\n"
         "  integer rfd;\n"
         "  integer rch;\n"
         "  initial begin\n"
         "    a = 1'b1;\n"
         "    d = 8'h00;\n"
         "    $dumpports(, \"p.dump\");\n"
         "    #10 d = 8'hA5;\n"
         "    #10 begin\n"
         "      $dumpportsflush();\n" +
             ReaderSnippet("MID") +
             "    end\n"
             "  end\n"
             "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(MidDump("MID").find("b10100101 "), std::string::npos);
}

// §21.7.3.5: the filename is an expression -- a string-typed variable holding
// the character string given to $dumpports denotes the same file, here bound
// through the variable's declaration initializer.
TEST_F(DumpportsflushSysTask, StringVariableFilenameDeclInit) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  logic a;\n"
         "  logic [7:0] d;\n"
         "  string fn = \"p.dump\";\n"
         "  integer rfd;\n"
         "  integer rch;\n"
         "  initial begin\n"
         "    a = 1'b1;\n"
         "    d = 8'h00;\n"
         "    $dumpports(, \"p.dump\");\n"
         "    #10 d = 8'hA5;\n"
         "    #10 begin\n"
         "      $dumpportsflush(fn);\n" +
             ReaderSnippet("MID") +
             "    end\n"
             "  end\n"
             "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(MidDump("MID").find("b10100101 "), std::string::npos);
}

// §21.7.3.5: the same string-typed filename variable works when the name is
// stored by a procedural assignment before the flush executes.
TEST_F(DumpportsflushSysTask, StringVariableFilenameProceduralAssign) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  logic a;\n"
         "  logic [7:0] d;\n"
         "  string fn;\n"
         "  integer rfd;\n"
         "  integer rch;\n"
         "  initial begin\n"
         "    a = 1'b1;\n"
         "    d = 8'h00;\n"
         "    fn = \"p.dump\";\n"
         "    $dumpports(, \"p.dump\");\n"
         "    #10 d = 8'hA5;\n"
         "    #10 begin\n"
         "      $dumpportsflush(fn);\n" +
             ReaderSnippet("MID") +
             "    end\n"
             "  end\n"
             "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(MidDump("MID").find("b10100101 "), std::string::npos);
}

// §21.7.3.5: an integral variable containing the character string is also an
// accepted filename form, here initialized in its declaration.
TEST_F(DumpportsflushSysTask, IntegralVariableFilenameDeclInit) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  logic a;\n"
         "  logic [7:0] d;\n"
         "  reg [47:0] fn = \"p.dump\";\n"
         "  integer rfd;\n"
         "  integer rch;\n"
         "  initial begin\n"
         "    a = 1'b1;\n"
         "    d = 8'h00;\n"
         "    $dumpports(, \"p.dump\");\n"
         "    #10 d = 8'hA5;\n"
         "    #10 begin\n"
         "      $dumpportsflush(fn);\n" +
             ReaderSnippet("MID") +
             "    end\n"
             "  end\n"
             "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(MidDump("MID").find("b10100101 "), std::string::npos);
}

// §21.7.3.5: the integral filename variable equally denotes the file when the
// character string is stored procedurally before the flush.
TEST_F(DumpportsflushSysTask, IntegralVariableFilenameProceduralAssign) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  logic a;\n"
         "  logic [7:0] d;\n"
         "  reg [47:0] fn;\n"
         "  integer rfd;\n"
         "  integer rch;\n"
         "  initial begin\n"
         "    a = 1'b1;\n"
         "    d = 8'h00;\n"
         "    fn = \"p.dump\";\n"
         "    $dumpports(, \"p.dump\");\n"
         "    #10 d = 8'hA5;\n"
         "    #10 begin\n"
         "      $dumpportsflush(fn);\n" +
             ReaderSnippet("MID") +
             "    end\n"
             "  end\n"
             "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(MidDump("MID").find("b10100101 "), std::string::npos);
}

// §21.7.3.5: the filename is an expression, so a parameter constant holding
// the character string is also accepted. The name stays within four
// characters: string parameters longer than that hit an upstream §6.20 32-bit
// truncation defect outside this subclause.
TEST_F(DumpportsflushSysTask, ParameterConstantFilename) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  parameter string FN = \"p.vc\";\n"
         "  logic a;\n"
         "  logic [7:0] d;\n"
         "  integer rfd;\n"
         "  integer rch;\n"
         "  initial begin\n"
         "    a = 1'b1;\n"
         "    d = 8'h00;\n"
         "    $dumpports(, \"p.vc\");\n"
         "    #10 d = 8'hA5;\n"
         "    #10 begin\n"
         "      $dumpportsflush(FN);\n" +
             ReaderSnippet("MID") +
             "    end\n"
             "  end\n"
             "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(MidDump("MID").find("b10100101 "), std::string::npos);
}

// §21.7.3.5: a localparam constant holding the character string is likewise
// an accepted filename expression (kept within four characters for the same
// upstream §6.20 truncation limit as the parameter form).
TEST_F(DumpportsflushSysTask, LocalparamConstantFilename) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  localparam string FN = \"l.vc\";\n"
         "  logic a;\n"
         "  logic [7:0] d;\n"
         "  integer rfd;\n"
         "  integer rch;\n"
         "  initial begin\n"
         "    a = 1'b1;\n"
         "    d = 8'h00;\n"
         "    $dumpports(, \"l.vc\");\n"
         "    #10 d = 8'hA5;\n"
         "    #10 begin\n"
         "      $dumpportsflush(FN);\n" +
             ReaderSnippet("MID") +
             "    end\n"
             "  end\n"
             "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(MidDump("MID").find("b10100101 "), std::string::npos);
}

// §21.7.3.5: the buffer is cleared by each flush and refills as dumping
// continues, so a later flush shows the cumulative dump with no value change
// lost -- the first mid-simulation read finds only the first change, and a
// second read after another change and flush finds both records on disk.
TEST_F(DumpportsflushSysTask, RepeatedFlushesAccumulateRecordsWithNoneLost) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  logic a;\n"
         "  logic [7:0] d;\n"
         "  integer rfd;\n"
         "  integer rch;\n"
         "  initial begin\n"
         "    a = 1'b1;\n"
         "    d = 8'h00;\n"
         "    $dumpports(, \"p.dump\");\n"
         "    #10 d = 8'hA5;\n"
         "    #5 begin\n"
         "      $dumpportsflush(\"p.dump\");\n" +
             ReaderSnippet("MID1") +
             "    end\n"
             "    #5 d = 8'hC3;\n"
             "    #5 begin\n"
             "      $dumpportsflush(\"p.dump\");\n" +
             ReaderSnippet("MID2") +
             "    end\n"
             "  end\n"
             "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  auto mid1 = MidDump("MID1");
  EXPECT_NE(mid1.find("b10100101 "), std::string::npos);
  EXPECT_EQ(mid1.find("b11000011 "), std::string::npos);
  auto mid2 = MidDump("MID2");
  EXPECT_NE(mid2.find("b10100101 "), std::string::npos);
  EXPECT_NE(mid2.find("#20"), std::string::npos);
  EXPECT_NE(mid2.find("b11000011 "), std::string::npos);
}

// §21.7.3.5: the filename denotes the file the $dumpports call named, so the
// match is on the evaluated name regardless of the source form each side
// used -- a $dumpports whose filename arrived through a string variable
// (§21.7.3.1 syntax) is flushed by a literal spelling the same name.
TEST_F(DumpportsflushSysTask, LiteralFlushMatchesDumpportsVariableFilename) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  logic a;\n"
         "  logic [7:0] d;\n"
         "  string dn = \"v.dump\";\n"
         "  integer rfd;\n"
         "  integer rch;\n"
         "  initial begin\n"
         "    a = 1'b1;\n"
         "    d = 8'h00;\n"
         "    $dumpports(, dn);\n"
         "    #10 d = 8'hA5;\n"
         "    #10 begin\n"
         "      $dumpportsflush(\"v.dump\");\n" +
             ReaderSnippet("MID") +
             "    end\n"
             "  end\n"
             "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(MidDump("MID").find("b10100101 "), std::string::npos);
}

// §21.7.3.5 negative: the filename denotes a file named by a $dumpports call.
// A literal naming a file no $dumpports call opened matches nothing, so the
// flush is ignored -- the mid-simulation reader still finds the record
// buffered off disk -- while the dump itself is unaffected and completes.
TEST_F(DumpportsflushSysTask, UnknownFilenameLiteralFlushIgnored) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  logic [7:0] d;\n"
                        "  integer rfd;\n"
                        "  integer rch;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 d = 8'hA5;\n"
                        "    #10 begin\n"
                        "      $dumpportsflush(\"other.dump\");\n" +
                            ReaderSnippet("MID") +
                            "    end\n"
                            "  end\n"
                            "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(MidDump("MID").find("b10100101 "), std::string::npos);
  EXPECT_NE(content.find("b10100101 "), std::string::npos);
}

// §21.7.3.5 negative: the unknown filename may equally arrive through a
// string variable -- the evaluated name is what must match a $dumpports file,
// and a non-matching variable-held name leaves the flush ignored too.
TEST_F(DumpportsflushSysTask, UnknownFilenameVariableFlushIgnored) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  logic [7:0] d;\n"
                        "  string fn = \"other.dump\";\n"
                        "  integer rfd;\n"
                        "  integer rch;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 d = 8'hA5;\n"
                        "    #10 begin\n"
                        "      $dumpportsflush(fn);\n" +
                            ReaderSnippet("MID") +
                            "    end\n"
                            "  end\n"
                            "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(MidDump("MID").find("b10100101 "), std::string::npos);
  EXPECT_NE(content.find("b10100101 "), std::string::npos);
}

// §21.7.3.5: flushing right after the $dumpports opening checkpoint (which
// the dump schedules at the end of its own time unit, §21.7.3.1) pushes the
// header and that initial checkpoint to disk, so a reader early in the run
// already sees the definitions section and the scalar's opening value.
TEST_F(DumpportsflushSysTask, FlushAfterOpeningCheckpointShowsHeaderMidSim) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  logic a;\n"
         "  integer rfd;\n"
         "  integer rch;\n"
         "  initial begin\n"
         "    a = 1'b1;\n"
         "    $dumpports(, \"p.dump\");\n"
         "    #5 begin\n"
         "      $dumpportsflush(\"p.dump\");\n" +
             ReaderSnippet("MID") +
             "    end\n"
             "  end\n"
             "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  auto mid = MidDump("MID");
  EXPECT_NE(mid.find("$enddefinitions"), std::string::npos);
  EXPECT_NE(mid.find("1!"), std::string::npos);
}

// §21.7.3.5: the flush is not tied to the initial process that opened the
// dump -- reached from an always process on a clock edge, it equally pushes
// the buffered records to disk for a mid-simulation reader in that process.
TEST_F(DumpportsflushSysTask, FlushFromAlwaysProcessOnClockEdge) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  logic clk;\n"
         "  logic [7:0] d;\n"
         "  integer rfd;\n"
         "  integer rch;\n"
         "  initial begin\n"
         "    clk = 1'b0;\n"
         "    d = 8'h00;\n"
         "    $dumpports(, \"p.dump\");\n"
         "    #10 d = 8'hA5;\n"
         "    #10 clk = 1'b1;\n"
         "  end\n"
         "  always @(posedge clk) begin\n"
         "    $dumpportsflush(\"p.dump\");\n" +
             ReaderSnippet("MID") +
             "  end\n"
             "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  auto mid = MidDump("MID");
  EXPECT_NE(mid.find("#10"), std::string::npos);
  EXPECT_NE(mid.find("b10100101 "), std::string::npos);
}

// §21.7.3.5 edge: with no $dumpports call in the source there are no files
// opened for port dumping, so the no-filename default action has nothing to
// flush -- the task completes harmlessly with no diagnostic.
TEST_F(DumpportsflushSysTask, FlushWithNoDumpportsFilesIsHarmless) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  logic a;\n"
         "  initial begin\n"
         "    a = 1'b1;\n"
         "    #10 $dumpportsflush;\n"
         "  end\n"
         "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
}  // namespace delta
