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

// Exercises the general rules that apply to every extended VCD system task
// (§21.7.3.7) end to end: a control task naming a file that no $dumpports
// call specified is ignored, and for the tasks whose arguments are all
// optional the bare name and the empty-parenthesis spelling both run the
// default actions. Every test drives real source through parse, elaboration,
// lowering, and the scheduler with the driver's per-timestep recording loop
// installed, so both rules are observed as the production control-task
// dispatch applies them to a dump opened by a real $dumpports call
// (§21.7.3.1). The flush-observing test additionally plays the reader role:
// procedural code opens the dump file mid-run and echoes its bytes to stdout
// between marker lines, giving a mid-simulation snapshot to inspect.
class ExtendedVcdGeneralRules : public VcdTestBase {
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

// ---------------------------------------------------------------------------
// Rule 1: a control task whose filename does not match a filename specified
// in a $dumpports call shall be ignored -- for each task of the family.
// ---------------------------------------------------------------------------

// §21.7.3.7: $dumpportsoff naming a file no $dumpports call specified is
// ignored -- no suspend checkpoint is written and a later port change is
// still recorded.
TEST_F(ExtendedVcdGeneralRules, OffNamingUnspecifiedFileIsIgnored) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff(\"nomatch.dump\");\n"
                        "    #10 d = 8'hA5;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(content.find("$dumpoff"), std::string::npos);  // task ignored
  auto t20 = content.find("#20");
  ASSERT_NE(t20, std::string::npos);
  EXPECT_NE(content.find("b10100101 ", t20), std::string::npos);
}

// §21.7.3.7 accepting counterpart: when the filename matches the name a
// $dumpports call specified, the task is not ignored -- the suspend
// checkpoint appears and the later change is not recorded.
TEST_F(ExtendedVcdGeneralRules, OffNamingSpecifiedFileIsApplied) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff(\"p.dump\");\n"
                        "    #10 d = 8'hA5;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("$dumpoff"), std::string::npos);    // suspend applied
  EXPECT_EQ(content.find("b10100101 "), std::string::npos);  // change dropped
}

// §21.7.3.7: $dumpportson naming an unspecified file is ignored too -- the
// dump suspended by a matching $dumpportsoff stays suspended, so no resume
// checkpoint appears and the later change stays unrecorded.
TEST_F(ExtendedVcdGeneralRules, OnNamingUnspecifiedFileIsIgnored) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff(\"p.dump\");\n"
                        "    #10 $dumpportson(\"nomatch.dump\");\n"
                        "    #10 d = 8'hA5;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("$dumpoff"), std::string::npos);
  EXPECT_EQ(content.find("$dumpon"), std::string::npos);     // resume ignored
  EXPECT_EQ(content.find("b10100101 "), std::string::npos);  // still stopped
}

// §21.7.3.7 accepting counterpart: $dumpportson naming the specified file is
// not ignored -- the resume checkpoint appears and a change after it is
// recorded again.
TEST_F(ExtendedVcdGeneralRules, OnNamingSpecifiedFileIsApplied) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff(\"p.dump\");\n"
                        "    #10 $dumpportson(\"p.dump\");\n"
                        "    #10 d = 8'hA5;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  auto on = content.find("$dumpon");
  ASSERT_NE(on, std::string::npos);  // matched name: resume applied
  EXPECT_NE(content.find("b10100101 ", on), std::string::npos);
}

// §21.7.3.7: $dumpportsall naming an unspecified file is ignored -- no
// checkpoint section is written for it.
TEST_F(ExtendedVcdGeneralRules, AllNamingUnspecifiedFileIsIgnored) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'hA5;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsall(\"nomatch.dump\");\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(content.find("$dumpall"), std::string::npos);  // no checkpoint
}

// §21.7.3.7: $dumpportsflush naming an unspecified file is ignored -- the
// buffered record is NOT pushed to disk, so a reader running right after the
// call still finds nothing (the flushing counterpart puts it on disk, and the
// record does arrive once the writer closes at end of run).
TEST_F(ExtendedVcdGeneralRules, FlushNamingUnspecifiedFileIsIgnored) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  integer rfd;\n"
                        "  integer rch;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 d = 8'hA5;\n"
                        "    #10 begin\n"
                        "      $dumpportsflush(\"nomatch.dump\");\n" +
                            ReaderSnippet("MID") +
                            "    end\n"
                            "  end\n"
                            "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(MidDump("MID").find("b10100101 "), std::string::npos);
  EXPECT_NE(content.find("b10100101 "), std::string::npos);
}

// §21.7.3.7 accepting counterpart: $dumpportsflush naming the specified file
// is not ignored -- the reader running right after the call finds the
// buffered record already on disk, the within-suite discriminator for the
// ignored-flush test above.
TEST_F(ExtendedVcdGeneralRules, FlushNamingSpecifiedFileIsApplied) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  logic [7:0] d;\n"
         "  integer rfd;\n"
         "  integer rch;\n"
         "  initial begin\n"
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
  EXPECT_NE(MidDump("MID").find("b10100101 "), std::string::npos);
}

// §21.7.3.7: the ignore rule reaches $dumpportslimit through its trailing
// filename argument -- naming an unspecified file there leaves the byte
// budget unset, so no limit comment appears and the late changes of a
// workload that would otherwise trip the budget are retained.
TEST_F(ExtendedVcdGeneralRules, LimitNamingUnspecifiedFileIsIgnored) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    $dumpportslimit(300, \"nomatch.dump\");\n"
                        "    repeat (40) #10 d = d + 1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(content.find("$comment"), std::string::npos);  // limit never set
  EXPECT_NE(content.find("#400\n"), std::string::npos);  // late dumps retained
}

// §21.7.3.7 accepting counterpart for $dumpportslimit: with the trailing
// filename matching the specified $dumpports name the budget applies, the
// limit comment appears, and the late changes are dropped.
TEST_F(ExtendedVcdGeneralRules, LimitNamingSpecifiedFileIsApplied) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    $dumpportslimit(300, \"p.dump\");\n"
                        "    repeat (40) #10 d = d + 1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("$comment"), std::string::npos);  // budget enforced
  EXPECT_EQ(content.find("#400\n"), std::string::npos);    // late dumps stopped
}

// §21.7.3.7: the ignore rule applies wherever the control task executes --
// a $dumpportsoff naming an unspecified file is ignored even when the call
// sits in a task body, so the dump keeps recording.
TEST_F(ExtendedVcdGeneralRules, UnmatchedFilenameIgnoredFromTaskBody) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  task try_off;\n"
                        "    $dumpportsoff(\"nomatch.dump\");\n"
                        "  endtask\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 try_off;\n"
                        "    #10 d = 8'hA5;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(content.find("$dumpoff"), std::string::npos);  // still ignored
  auto t20 = content.find("#20");
  ASSERT_NE(t20, std::string::npos);
  EXPECT_NE(content.find("b10100101 ", t20), std::string::npos);
}

// §21.7.3.7: the same holds for a control task fired from an always process
// -- a $dumpportsall naming an unspecified file on the clock edge writes no
// checkpoint.
TEST_F(ExtendedVcdGeneralRules, UnmatchedFilenameIgnoredFromAlwaysProcess) {
  SimFixture f;
  auto content =
      RunVcd(f,
             "module t;\n"
             "  logic clk;\n"
             "  logic [7:0] d;\n"
             "  always @(posedge clk) $dumpportsall(\"nomatch.dump\");\n"
             "  initial begin\n"
             "    clk = 1'b0;\n"
             "    d = 8'hA5;\n"
             "    $dumpports(, \"p.dump\");\n"
             "    #10 clk = 1'b1;\n"
             "  end\n"
             "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(content.find("$dumpall"), std::string::npos);  // no checkpoint
}

// ---------------------------------------------------------------------------
// Rule 1, filename input forms: the (mis)matching name may reach the control
// task as any filename expression, not just a string literal.
// ---------------------------------------------------------------------------

// §21.7.3.7: a string-typed variable initialized at its declaration with a
// name no $dumpports call specified makes the control task naming it ignored.
TEST_F(ExtendedVcdGeneralRules, StringVariableDeclInitUnspecifiedIgnored) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  string fn = \"nomatch.dump\";\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff(fn);\n"
                        "    #10 d = 8'hA5;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(content.find("$dumpoff"), std::string::npos);
  EXPECT_NE(content.find("b10100101 "), std::string::npos);
}

// §21.7.3.7: a string variable procedurally assigned the specified name makes
// the control task act on that dump -- the evaluated value, not the variable
// itself, is what is matched.
TEST_F(ExtendedVcdGeneralRules, StringVariableProceduralSpecifiedApplied) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  string fn;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    fn = \"p.dump\";\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff(fn);\n"
                        "    #10 d = 8'hA5;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("$dumpoff"), std::string::npos);
  EXPECT_EQ(content.find("b10100101 "), std::string::npos);
}

// §21.7.3.7: an integral variable holding an unspecified name (declaration
// initializer form) is evaluated the same way, so the task is ignored.
TEST_F(ExtendedVcdGeneralRules, IntegralVariableDeclInitUnspecifiedIgnored) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  logic [95:0] fn = \"nomatch.dump\";\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff(fn);\n"
                        "    #10 d = 8'hA5;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(content.find("$dumpoff"), std::string::npos);
  EXPECT_NE(content.find("b10100101 "), std::string::npos);
}

// §21.7.3.7: an integral variable procedurally assigned the specified name
// lets the control task through -- here $dumpportsall, whose checkpoint then
// appears.
TEST_F(ExtendedVcdGeneralRules, IntegralVariableProceduralSpecifiedApplied) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  logic [47:0] fn;\n"
                        "  initial begin\n"
                        "    d = 8'hA5;\n"
                        "    fn = \"p.dump\";\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsall(fn);\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("$dumpall"), std::string::npos);  // checkpoint made
}

// §21.7.3.7: a parameter holding the specified name (a constant of §11.2.1)
// matches, so the control task applies. The name stays within four characters
// so an untyped parameter carries it without truncation (§6.20).
TEST_F(ExtendedVcdGeneralRules, ParameterFilenameSpecifiedApplied) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  parameter P = \"p.d\";\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.d\");\n"
                        "    #10 $dumpportsoff(P);\n"
                        "    #10 d = 8'hA5;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("$dumpoff"), std::string::npos);
  EXPECT_EQ(content.find("b10100101 "), std::string::npos);
}

// §21.7.3.7: a localparam holding a name no $dumpports call specified leaves
// the control task ignored, the constant counterpart of the unmatched
// variable forms.
TEST_F(ExtendedVcdGeneralRules, LocalparamFilenameUnspecifiedIgnored) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  localparam L = \"no.d\";\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.d\");\n"
                        "    #10 $dumpportsoff(L);\n"
                        "    #10 d = 8'hA5;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(content.find("$dumpoff"), std::string::npos);
  EXPECT_NE(content.find("b10100101 "), std::string::npos);
}

// §21.7.3.7: the match compares evaluated names -- a $dumpports call whose
// filename argument is a string variable specifies the name the variable
// holds, so a control task spelling that same name as a literal matches it.
TEST_F(ExtendedVcdGeneralRules, LiteralMatchesVariableSpecifiedName) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  string fn = \"p.dump\";\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, fn);\n"
                        "    #10 $dumpportsoff(\"p.dump\");\n"
                        "    #10 d = 8'hA5;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("$dumpoff"), std::string::npos);
  EXPECT_EQ(content.find("b10100101 "), std::string::npos);
}

// §21.7.3.7 edge: the ignore rule keys off filenames specified in $dumpports
// calls. A bare $dumpports call specifies no filename (the default name is
// not "specified"), so a control task naming a file has nothing to mismatch
// and acts on the dump.
TEST_F(ExtendedVcdGeneralRules, NamedTaskAppliesWhenNoFilenameSpecified) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports;\n"
                        "    #10 $dumpportsoff(\"any.dump\");\n"
                        "    #10 d = 8'hA5;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("$dumpoff"), std::string::npos);
  EXPECT_EQ(content.find("b10100101 "), std::string::npos);
}

// ---------------------------------------------------------------------------
// Rule 2: for the tasks that have only optional arguments, the bare name and
// the name followed by () both execute the default actions.
// ---------------------------------------------------------------------------

// §21.7.3.7: the bare no-argument spelling and the empty-parenthesis
// spelling both execute the default action -- the bare run suspends every
// $dumpports file, and the two runs' dumped records (from $enddefinitions
// on) are identical.
TEST_F(ExtendedVcdGeneralRules, EmptyParenSameDefaultActionAsBare) {
  auto tail = [](const std::string& s) {
    auto p = s.find("$enddefinitions");
    return p == std::string::npos ? s : s.substr(p);
  };
  const std::string common_head =
      "module t;\n"
      "  logic [7:0] d;\n"
      "  initial begin\n"
      "    d = 8'h00;\n"
      "    $dumpports(, \"p.dump\");\n";
  const std::string common_tail =
      "    #10 d = 8'hA5;\n"
      "  end\n"
      "endmodule\n";
  SimFixture f_bare;
  auto bare =
      RunVcd(f_bare, common_head + "    #10 $dumpportsoff;\n" + common_tail);
  SimFixture f_paren;
  auto paren =
      RunVcd(f_paren, common_head + "    #10 $dumpportsoff();\n" + common_tail);
  EXPECT_FALSE(f_bare.diag.HasErrors());
  EXPECT_FALSE(f_paren.diag.HasErrors());
  EXPECT_NE(bare.find("$dumpoff"), std::string::npos);   // bare default ran
  EXPECT_NE(paren.find("$dumpoff"), std::string::npos);  // () default ran
  EXPECT_EQ(tail(bare), tail(paren));  // both defaults acted identically
}

// §21.7.3.7: the bare spelling of $dumpportson runs its default action --
// resuming every $dumpports file -- so the dump suspended for the named file
// resumes and a later change is recorded again.
TEST_F(ExtendedVcdGeneralRules, BareOnRunsDefaultResume) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff(\"p.dump\");\n"
                        "    #10 $dumpportson;\n"
                        "    #10 d = 8'hA5;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  auto on = content.find("$dumpon");
  ASSERT_NE(on, std::string::npos);  // bare default resumed the dump
  EXPECT_NE(content.find("b10100101 ", on), std::string::npos);
}

// §21.7.3.7: the empty-parenthesis spelling of $dumpportsall runs its default
// action -- checkpointing every $dumpports file -- so the all-ports section
// appears with the port's current value.
TEST_F(ExtendedVcdGeneralRules, EmptyParenAllRunsDefaultCheckpoint) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'hA5;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsall();\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  auto pos = content.find("$dumpall");
  ASSERT_NE(pos, std::string::npos);
  auto end = content.find("$end", pos);
  ASSERT_NE(end, std::string::npos);
  EXPECT_NE(content.substr(pos, end - pos).find("b10100101 "),
            std::string::npos);
}

// §21.7.3.7: the clause's own example pair is $dumpportsflush -- the bare
// spelling executes the default action, flushing every $dumpports file's
// buffer, so the reader finds the record on disk right after the call.
TEST_F(ExtendedVcdGeneralRules, BareFlushRunsDefaultAction) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  logic [7:0] d;\n"
         "  integer rfd;\n"
         "  integer rch;\n"
         "  initial begin\n"
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

// §21.7.3.7: the other half of the clause's example pair -- the
// empty-parenthesis flush spelling -- executes the same default action, so
// the reader again finds the record on disk right after the call.
TEST_F(ExtendedVcdGeneralRules, EmptyParenFlushRunsDefaultAction) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  logic [7:0] d;\n"
         "  integer rfd;\n"
         "  integer rch;\n"
         "  initial begin\n"
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

// §21.7.3.7: the default-action spellings work from any calling position --
// a bare $dumpportsall inside a task body still writes the all-ports
// checkpoint covering every $dumpports file.
TEST_F(ExtendedVcdGeneralRules, BareDefaultActionFromTaskBody) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  task do_ckpt;\n"
                        "    $dumpportsall;\n"
                        "  endtask\n"
                        "  initial begin\n"
                        "    d = 8'hA5;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 do_ckpt;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  auto pos = content.find("$dumpall");
  ASSERT_NE(pos, std::string::npos);
  auto end = content.find("$end", pos);
  ASSERT_NE(end, std::string::npos);
  // The checkpoint records the port's current value.
  EXPECT_NE(content.substr(pos, end - pos).find("b10100101 "),
            std::string::npos);
}

// §21.7.3.7: the empty-parenthesis spelling from an always process resumes
// every $dumpports file on the clock edge -- the resume checkpoint appears
// and a change after it is recorded again.
TEST_F(ExtendedVcdGeneralRules, EmptyParenDefaultActionFromAlwaysProcess) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic clk;\n"
                        "  logic [7:0] d;\n"
                        "  always @(posedge clk) $dumpportson();\n"
                        "  initial begin\n"
                        "    clk = 1'b0;\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff(\"p.dump\");\n"
                        "    #10 clk = 1'b1;\n"
                        "    #10 d = 8'hA5;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  auto on = content.find("$dumpon");
  ASSERT_NE(on, std::string::npos);  // default resume ran on the edge
  EXPECT_NE(content.find("b10100101 ", on), std::string::npos);
}

// §21.7.3.7 boundary: the default-action rule covers only the tasks whose
// arguments are all optional. $dumpportslimit requires its filesize, so its
// bare spelling gets no default byte budget -- the workload dumps unbounded
// with no limit comment, and the missing argument is reported (§21.7.3.4
// owns the diagnostic's wording).
TEST_F(ExtendedVcdGeneralRules, BareLimitGetsNoDefaultAction) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    $dumpportslimit;\n"
                        "    repeat (40) #10 d = d + 1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_TRUE(f.diag.HasErrors());  // required argument missing, not defaulted
  EXPECT_EQ(content.find("$comment"), std::string::npos);  // no default limit
  EXPECT_NE(content.find("#400\n"), std::string::npos);    // dump unbounded
}

// §21.7.3.7 boundary, empty-parenthesis spelling: $dumpportslimit() likewise
// gets no default byte budget -- the excluded task is excluded under either
// no-argument spelling.
TEST_F(ExtendedVcdGeneralRules, EmptyParenLimitGetsNoDefaultAction) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    $dumpportslimit();\n"
                        "    repeat (40) #10 d = d + 1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_TRUE(f.diag.HasErrors());  // required argument missing, not defaulted
  EXPECT_EQ(content.find("$comment"), std::string::npos);  // no default limit
  EXPECT_NE(content.find("#400\n"), std::string::npos);    // dump unbounded
}

}  // namespace
}  // namespace delta
