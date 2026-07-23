#include <algorithm>
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

// §21.7.1: creating the 4-state VCD file. The subclause's own text (its
// descendants own the individual tasks) makes two observable claims:
// (1) the file is created by inserting the VCD system tasks in the
// SystemVerilog source -- one call defining the dump file name, one
// specifying the variables to dump -- and then running the simulation
// (the Figure 21-1 flow); (2) the resulting file is ASCII text holding, in
// order, header information, variable definitions, and the value changes of
// every variable the task calls specified. Both are runtime rules whose
// observable is the dump file a full simulation leaves on disk, so each test
// drives real source through parse, elaboration, lowering, and the scheduler
// with the driver's per-timestep recording loop installed, then inspects the
// file -- nothing is hand-driven on the writer.
class CreatingFourStateVcd : public VcdTestBase {
 protected:
  // Runs a single-module source through the full pipeline with the driver's
  // dump loop (timestamp + changed values at the end of each time unit) and
  // returns the dump file contents.
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

// The creation steps of Figure 21-1: the source inserts the VCD system tasks
// -- $dumpfile defining the dump file name, then $dumpvars specifying the
// variables -- and the simulation runs. The product is a non-empty dump file
// recording the variable's later value change, ready for post-processing.
TEST_F(CreatingFourStateVcd, InsertTasksAndRunSimulationProducesDumpFile) {
  auto content = RunVcd(
      "module t;\n"
      "  logic clk;\n"
      "  initial begin\n"
      "    $dumpfile(\"dump1.dump\");\n"
      "    $dumpvars;\n"
      "    clk = 1'b0;\n"
      "    #10 clk = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_FALSE(content.empty());
  EXPECT_NE(content.find("$enddefinitions"), std::string::npos);
  EXPECT_NE(content.find("#10"), std::string::npos);
  EXPECT_NE(content.find("1!"), std::string::npos);  // clk's recorded change
}

// A VCD file is an ASCII file: with the dump exercising the full 4-state
// alphabet (0, 1, x, and z reaching the value-change section in both vector
// and scalar encodings), every byte of the file is printable ASCII or
// ordinary whitespace -- no byte outside the 7-bit printable range appears.
TEST_F(CreatingFourStateVcd, DumpFileIsAsciiText) {
  auto content = RunVcd(
      "module t;\n"
      "  logic s;\n"
      "  logic [7:0] v;\n"
      "  initial begin\n"
      "    s = 1'b0;\n"
      "    v = 8'b00000000;\n"
      "    $dumpvars;\n"
      "    #10 v = 8'b10xz01zx;\n"
      "    #10 s = 1'bx;\n"
      "    #10 s = 1'bz;\n"
      "    #10 v = 8'hFF;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_FALSE(content.empty());
  // The 4-state values are carried as ASCII letters in the change records:
  // s -> '!' (scalar encoding), v -> '"' (vector encoding).
  EXPECT_NE(content.find("b10xz01zx \""), std::string::npos);
  EXPECT_NE(content.find("x!"), std::string::npos);
  EXPECT_NE(content.find("z!"), std::string::npos);
  for (unsigned char c : content) {
    bool ascii_text =
        (c >= 0x20 && c < 0x7F) || c == '\n' || c == '\t' || c == '\r';
    ASSERT_TRUE(ascii_text) << "non-ASCII byte 0x" << std::hex << int{c};
  }
}

// The file's three parts appear in creation order: header information first,
// then the variable definitions, then the value changes -- matching the
// header / node information / value-change layout of Figure 21-1.
TEST_F(CreatingFourStateVcd, HeaderThenDefinitionsThenValueChanges) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    $dumpvars;\n"
      "    #10 a = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  auto p_date = content.find("$date");
  auto p_timescale = content.find("$timescale");
  auto p_var = content.find("$var wire 1 ! a $end");
  auto p_defs_end = content.find("$enddefinitions");
  auto p_change = content.find("#10");
  ASSERT_NE(p_date, std::string::npos);
  ASSERT_NE(p_timescale, std::string::npos);
  ASSERT_NE(p_var, std::string::npos);
  ASSERT_NE(p_defs_end, std::string::npos);
  ASSERT_NE(p_change, std::string::npos);
  EXPECT_LT(p_date, p_timescale);   // header information...
  EXPECT_LT(p_timescale, p_var);    // ...precedes variable definitions...
  EXPECT_LT(p_var, p_defs_end);     // ...closed by $enddefinitions...
  EXPECT_LT(p_defs_end, p_change);  // ...and value changes come last
  EXPECT_NE(content.find("1!", p_change), std::string::npos);
}

// The file contains the value changes for ALL variables specified in the
// task calls: with two variables specified and each changing at a different
// time, both variables' definitions and both recorded changes are present.
TEST_F(CreatingFourStateVcd, ValueChangesForAllSpecifiedVariables) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  logic [3:0] b;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    b = 4'b0000;\n"
      "    $dumpvars;\n"
      "    #10 a = 1'b1;\n"
      "    #10 b = 4'b1010;\n"
      "  end\n"
      "endmodule\n");
  // Variable definitions cover each specified variable.
  EXPECT_NE(content.find("$var wire 1 ! a $end"), std::string::npos);
  EXPECT_NE(content.find("$var wire 4 \" b $end"), std::string::npos);
  // Value changes cover each specified variable.
  auto p_defs_end = content.find("$enddefinitions");
  ASSERT_NE(p_defs_end, std::string::npos);
  EXPECT_NE(content.find("1!", p_defs_end), std::string::npos);
  EXPECT_NE(content.find("b1010 \"", p_defs_end), std::string::npos);
}

// "All variables specified" includes one that never changes after the
// specifying call: the checkpoint the specification produces records its
// value, so the variable is represented in the file's value-change section
// even without a later edge.
TEST_F(CreatingFourStateVcd, SpecifiedButUnchangingVariableStillRepresented) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  logic [3:0] steady;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    steady = 4'b0110;\n"
      "    $dumpvars;\n"
      "    #10 a = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  auto p_defs_end = content.find("$enddefinitions");
  ASSERT_NE(p_defs_end, std::string::npos);
  // a -> '!', steady -> '"': the never-changing variable's value is recorded
  // by the $dumpvars checkpoint alongside the changing one's.
  EXPECT_NE(content.find("0!", p_defs_end), std::string::npos);
  EXPECT_NE(content.find("b110 \"", p_defs_end), std::string::npos);
  EXPECT_NE(content.find("1!", p_defs_end), std::string::npos);
}

// The creation tasks are ordinary task enables: inserted in a task body
// rather than directly in the initial block, the same run produces the same
// three-part dump file.
TEST_F(CreatingFourStateVcd, TasksInsertedInTaskBodyStillCreateFile) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  task start_dump;\n"
      "    $dumpfile(\"dump1.dump\");\n"
      "    $dumpvars;\n"
      "  endtask\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    start_dump;\n"
      "    #10 a = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("$timescale"), std::string::npos);
  EXPECT_NE(content.find("$var wire 1 ! a $end"), std::string::npos);
  EXPECT_NE(content.find("$enddefinitions"), std::string::npos);
  EXPECT_NE(content.find("1!"), std::string::npos);
}

// Negative: with no writer installed (no dump file in place), executing the
// creation tasks is harmless -- the design still runs to completion and no
// dump file content appears.
TEST_F(CreatingFourStateVcd, WithoutWriterCreationTasksAreHarmless) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    $dumpfile(\"dump1.dump\");\n"
      "    $dumpvars;\n"
      "    #10 a = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();  // no VcdWriter installed anywhere
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(ReadVcd().empty());
}

}  // namespace
}  // namespace delta
