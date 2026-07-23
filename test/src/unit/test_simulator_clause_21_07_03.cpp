#include <algorithm>
#include <iterator>
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

// §21.7.3: creating the extended VCD file. The subclause's own text (its
// descendants own the individual tasks and the extended grammar) makes two
// observable claims: (1) the file is created by inserting the extended VCD
// system tasks in the SystemVerilog source -- defining the dump file name and
// naming what to dump -- and then running the simulation (the Figure 21-2
// flow), yielding a file laid out as header information, node information,
// and value changes; (2) the 4-state file rules and syntax carry over to the
// extended file except where this subclause replaces them. Both are runtime
// rules whose observable is the dump file a full simulation leaves on disk,
// so each test drives real source through parse, elaboration, lowering, and
// the scheduler with the driver's per-timestep recording loop installed, then
// inspects the file -- nothing is hand-driven on the writer.
class CreatingExtendedVcd : public VcdTestBase {
 protected:
  // Runs a single-module source through the full pipeline with the driver's
  // dump loop (timestamp + changed values at the end of each time unit) and
  // returns the dump file contents. The module scope is opened around the
  // variable definitions the way the simulation driver does, so the node
  // information carries the inherited $scope/$var/$upscope sections.
  std::string RunVcd(const std::string& src) {
    SimFixture f;
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
      // Value change dumping starts once the source's extended dump task
      // executes and produces its opening checkpoint.
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

// The dump file split into its white-space-delimited tokens: the projection
// under which the inherited free-format rule is observable.
std::vector<std::string> Tokens(const std::string& content) {
  std::istringstream iss(content);
  return {std::istream_iterator<std::string>(iss),
          std::istream_iterator<std::string>()};
}

// True when no token fuses two commands together: a '$' introduces a keyword
// command, so after tokenizing on white space it can only appear at the start
// of a token.
bool NoFusedCommands(const std::vector<std::string>& toks) {
  for (const auto& t : toks) {
    if (t.find('$', 1) != std::string::npos) return false;
  }
  return true;
}

// Occurrences of `tok` as a complete white-space-delimited token.
size_t CountToken(const std::vector<std::string>& toks,
                  std::string_view target) {
  size_t n = 0;
  for (const auto& t : toks) {
    if (t == target) ++n;
  }
  return n;
}

// The creation steps of Figure 21-2: the source inserts the extended VCD
// system task -- $dumpports with a null scope_list and the figure's file name
// -- and the simulation runs. The product is a non-empty dump file recording
// the variable's later value change, ready for user postprocessing.
TEST_F(CreatingExtendedVcd, InsertTaskAndRunSimulationProducesDumpFile) {
  auto content = RunVcd(
      "module t;\n"
      "  logic clk;\n"
      "  initial begin\n"
      "    clk = 1'b0;\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    #10 clk = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_FALSE(content.empty());
  EXPECT_NE(content.find("$enddefinitions"), std::string::npos);
  EXPECT_NE(content.find("#10"), std::string::npos);
  EXPECT_NE(content.find("1!"), std::string::npos);  // clk's recorded change
}

// Step a) of the creation flow: the inserted task defines the dump file name.
// After the run, the name the simulation would write the extended VCD file
// under is the one the source's task call supplied.
TEST_F(CreatingExtendedVcd, InsertedTaskDefinesDumpFileName) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk;\n"
      "  initial begin\n"
      "    clk = 1'b0;\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    #10 clk = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(f.ctx.GetDumpFileName(), "dump2.dump");
}

// The file's three regions appear in creation order: header information
// first, then the node information, then the value changes -- matching the
// layout Figure 21-2 draws inside the extended VCD file box.
TEST_F(CreatingExtendedVcd, HeaderThenNodeInfoThenValueChanges) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    $dumpports(, \"dump2.dump\");\n"
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
  EXPECT_LT(p_timescale, p_var);    // ...precedes the node information...
  EXPECT_LT(p_var, p_defs_end);     // ...closed by $enddefinitions...
  EXPECT_LT(p_defs_end, p_change);  // ...and value changes come last
  EXPECT_NE(content.find("1!", p_change), std::string::npos);
}

// Step a) also has the inserted task specify what is dumped: with two
// variables in scope of the call and each changing at a different time, both
// declarations and both recorded changes reach the file.
TEST_F(CreatingExtendedVcd, ValueChangesForAllSpecifiedVariables) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  logic [3:0] b;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    b = 4'b0000;\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    #10 a = 1'b1;\n"
      "    #10 b = 4'b1010;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("$var wire 1 ! a $end"), std::string::npos);
  EXPECT_NE(content.find("$var wire 4 \" b $end"), std::string::npos);
  auto p_defs_end = content.find("$enddefinitions");
  ASSERT_NE(p_defs_end, std::string::npos);
  EXPECT_NE(content.find("1!", p_defs_end), std::string::npos);
  EXPECT_NE(content.find("b1010 \"", p_defs_end), std::string::npos);
}

// The creation task is an ordinary task enable: inserted in a task body
// rather than directly in the initial block, the same run produces the same
// three-region dump file.
TEST_F(CreatingExtendedVcd, TaskInsertedInTaskBodyStillCreatesFile) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  task start_dump;\n"
      "    $dumpports(, \"dump2.dump\");\n"
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

// The inherited rules of the 4-state file apply to the extended file: it is
// free format, each command stands apart from its neighbors bounded by white
// space, keyword sections balance with a standalone $end, and every
// simulation-time command is a '#' followed by decimal digits and nothing
// else. Nothing in the head replaces these rules for the commands this dump
// produces, so the extended file must satisfy them unchanged.
TEST_F(CreatingExtendedVcd, InheritedFreeFormatCommandSeparation) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    #10 a = 1'b1;\n"
      "    #10 a = 1'b0;\n"
      "  end\n"
      "endmodule\n");
  auto toks = Tokens(content);
  ASSERT_FALSE(toks.empty());
  EXPECT_TRUE(NoFusedCommands(toks));
  // The declaration and checkpoint keywords all stand apart as tokens.
  const char* openers[] = {"$date", "$version", "$timescale",      "$scope",
                           "$var",  "$upscope", "$enddefinitions", "$dumpvars"};
  size_t opened = 0;
  for (const char* kw : openers) {
    size_t n = CountToken(toks, kw);
    EXPECT_GE(n, 1u) << kw << " missing as a standalone token";
    opened += n;
  }
  // Every opened keyword section is closed by a matching standalone $end.
  EXPECT_EQ(CountToken(toks, "$end"), opened);
  // Simulation times keep the inherited #<decimal> form.
  for (const auto& t : toks) {
    if (t[0] != '#') continue;
    ASSERT_GT(t.size(), 1u) << "bare # token";
    for (size_t i = 1; i < t.size(); ++i) {
      ASSERT_TRUE(t[i] >= '0' && t[i] <= '9')
          << "simulation time fused with another command: " << t;
    }
  }
}

// The inherited ASCII-text rule: with the dump exercising the full 4-state
// alphabet in both scalar and vector encodings, every byte of the extended
// file is printable ASCII or ordinary white space.
TEST_F(CreatingExtendedVcd, ExtendedDumpFileIsAsciiText) {
  auto content = RunVcd(
      "module t;\n"
      "  logic s;\n"
      "  logic [7:0] v;\n"
      "  initial begin\n"
      "    s = 1'b0;\n"
      "    v = 8'b00000000;\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    #10 v = 8'b10xz01zx;\n"
      "    #10 s = 1'bx;\n"
      "    #10 s = 1'bz;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_FALSE(content.empty());
  EXPECT_NE(content.find("b10xz01zx \""), std::string::npos);
  EXPECT_NE(content.find("x!"), std::string::npos);
  EXPECT_NE(content.find("z!"), std::string::npos);
  for (unsigned char c : content) {
    bool ascii_text =
        (c >= 0x20 && c < 0x7F) || c == '\n' || c == '\t' || c == '\r';
    ASSERT_TRUE(ascii_text) << "non-ASCII byte 0x" << std::hex << int{c};
  }
}

// The creation task can also be reached from an always process: triggered
// once by an edge, the same flow starts the dump mid-simulation and the
// later value change is recorded exactly as from an initial block.
TEST_F(CreatingExtendedVcd, TaskReachedFromAlwaysProcessStillCreatesFile) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  logic go;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    go = 1'b0;\n"
      "    #5 go = 1'b1;\n"
      "    #10 a = 1'b1;\n"
      "  end\n"
      "  always @(posedge go) $dumpports(, \"dump2.dump\");\n"
      "endmodule\n");
  // a -> '!', go -> '"': the edge-triggered call opens the checkpoint and the
  // change at time 15 is recorded after the definitions close.
  auto p_defs_end = content.find("$enddefinitions");
  ASSERT_NE(p_defs_end, std::string::npos);
  EXPECT_NE(content.find("$dumpvars", p_defs_end), std::string::npos);
  EXPECT_NE(content.find("#15"), std::string::npos);
  EXPECT_NE(content.find("1!", p_defs_end), std::string::npos);
}

// The dumped variables' starting values may be produced by declaration
// initializers rather than procedural assignments: the checkpoint the
// inserted task opens records those initializer-produced values, and a later
// procedural change is recorded on top of them.
TEST_F(CreatingExtendedVcd, DeclarationInitializedVariablesDumpedThroughFlow) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a = 1'b0;\n"
      "  logic [3:0] v = 4'b0011;\n"
      "  initial begin\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    #10 v = 4'b1100;\n"
      "  end\n"
      "endmodule\n");
  auto p_defs_end = content.find("$enddefinitions");
  ASSERT_NE(p_defs_end, std::string::npos);
  // a -> '!', v -> '"': the opening checkpoint carries the initializer-given
  // values, then the change at time 10 follows.
  EXPECT_NE(content.find("0!", p_defs_end), std::string::npos);
  EXPECT_NE(content.find("b11 \"", p_defs_end), std::string::npos);
  EXPECT_NE(content.find("#10"), std::string::npos);
  EXPECT_NE(content.find("b1100 \"", p_defs_end), std::string::npos);
}

// The inherited value-command formats reach beyond the scalar and vector
// encodings: a real variable dumped through the extended flow keeps the
// 4-state real-number command form in both the opening checkpoint and a
// later recorded change, since nothing in the head replaces it.
TEST_F(CreatingExtendedVcd, InheritedRealValueFormatInExtendedFile) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  real r;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    r = 3.5;\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    #10 r = 1.25;\n"
      "  end\n"
      "endmodule\n");
  // a -> '!', r -> '"': the checkpoint records the initial real value and the
  // later change is recorded in the same inherited real-number command form.
  EXPECT_NE(content.find("r3.5 \""), std::string::npos);
  EXPECT_NE(content.find("r1.25 \""), std::string::npos);
  EXPECT_TRUE(NoFusedCommands(Tokens(content)));
}

// Negative for step a): with a dump file in place but no extended VCD task
// inserted in the source, running the simulation yields no value changes --
// the flow's first step is what starts the dump, so the file holds only the
// driver-written header and node information.
TEST_F(CreatingExtendedVcd, WithoutInsertedTaskNoValueChangesRecorded) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    #10 a = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_FALSE(content.empty());
  EXPECT_NE(content.find("$enddefinitions"), std::string::npos);
  // No task ran, so no checkpoint section, no simulation times, and no
  // recorded change follow the definitions.
  EXPECT_EQ(content.find("$dumpvars"), std::string::npos);
  EXPECT_EQ(content.find('#'), std::string::npos);
  EXPECT_EQ(content.find("1!"), std::string::npos);
}

// Negative: with no writer installed (no dump file in place), the inserted
// task is harmless -- the design still runs to completion and no dump file
// content appears for either flow step to have produced.
TEST_F(CreatingExtendedVcd, WithoutWriterInsertedTaskIsHarmless) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic a;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    $dumpports(, \"dump2.dump\");\n"
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
