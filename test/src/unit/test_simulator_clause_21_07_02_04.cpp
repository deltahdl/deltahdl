#include <cstring>
#include <string>
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

// §21.7.2.4: the worked example of the complete 4-state VCD file. The
// subclause's own contribution is the integrated shape of the file -- how the
// pieces its ancestors define compose: header sections in order, a scope tree
// of definitions ending at $enddefinitions, then simulation commands where
// each checkpoint section ($dumpvars, $dumpall, $dumpoff, $dumpon) sits after
// the simulation_time command of the time unit its task executed in, and each
// later time unit lists only the variables that changed. Rules whose behavior
// depends on how the dumped objects and the producing tasks are written are
// driven through the full pipeline (parse, elaborate, lower, run) using the
// §21.7.1.1-§21.7.1.4 tasks in real source; only the scope-tree composition
// and the comment placement, which are confined to the writer (hierarchy
// traversal is owned by the driver), use the writer directly.
class FourStateVcdExampleE2E : public VcdTestBase {
 protected:
  // Runs a single-module source through the full pipeline with the driver's
  // dump loop (timestamp + changed values at the end of each time unit) and
  // returns the dump file contents, mirroring the driver's registration
  // sequence. Identifier codes ascend from '!' in name order.
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
      f.ctx.RegisterVcdSignals(vcd);
      vcd.EndScope();
      vcd.EndDefinitions();
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

// The body of the section opened by `keyword`, up to (not including) the next
// $end. Empty when the keyword is absent.
std::string Section(const std::string& content, std::string_view keyword) {
  auto start = content.find(keyword);
  if (start == std::string::npos) return {};
  auto end = content.find("$end", start);
  if (end == std::string::npos) return content.substr(start);
  return content.substr(start, end - start);
}

// The text strictly between the first occurrence of `a` (after its end) and
// the following occurrence of `b`. Empty-string result means the two are
// adjacent; a missing bound yields the sentinel "<bound-missing>".
std::string Between(const std::string& content, std::string_view a,
                    std::string_view b) {
  auto pa = content.find(a);
  if (pa == std::string::npos) return "<bound-missing>";
  auto from = pa + a.size();
  auto pb = content.find(b, from);
  if (pb == std::string::npos) return "<bound-missing>";
  return content.substr(from, pb - from);
}

size_t CountOccurrences(const std::string& content, std::string_view needle) {
  size_t n = 0;
  for (auto pos = content.find(needle); pos != std::string::npos;
       pos = content.find(needle, pos + needle.size())) {
    ++n;
  }
  return n;
}

// E1+E2+E5: the illustrated file reads in one fixed progression -- $date,
// $version, $timescale, the scope/variable definitions, $enddefinitions, then
// the first simulation time and the $dumpvars section. Driven by real source
// whose $dumpvars executes at a late time so the ordering of the header
// against the simulation region is observable.
TEST_F(FourStateVcdExampleE2E, FileSectionsFollowExampleProgression) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  logic [31:0] acc;\n"
      "  initial begin\n"
      "    #500 $dumpvars;\n"
      "    #5 begin a = 1'b0; acc = 32'h1e; end\n"
      "  end\n"
      "endmodule\n");
  size_t last = 0;
  for (const char* mark :
       {"$date", "$version", "$timescale", "$scope", "$var", "$upscope",
        "$enddefinitions", "#500", "$dumpvars"}) {
    auto pos = content.find(mark, last);
    ASSERT_NE(pos, std::string::npos) << mark << " out of order\n" << content;
    last = pos + std::strlen(mark);
  }
  // Negative form: the first simulation_time command in the file is the
  // $dumpvars time -- no earlier time marker exists anywhere.
  EXPECT_EQ(content.find('#'), content.find("#500")) << content;
}

// E5: the $dumpvars section sits directly after the simulation_time command
// of the time unit in which the task executed (#500 then $dumpvars in the
// example), and it lists the initial value of every dumped variable --
// variables no assignment has touched are listed as x (scalar) and bx
// (vector). Codes in name order: a -> !, acc -> ".
TEST_F(FourStateVcdExampleE2E, DumpvarsSectionFollowsItsTimeMarker) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  logic [31:0] acc;\n"
      "  initial begin\n"
      "    #500 $dumpvars;\n"
      "    #5 begin a = 1'b0; acc = 32'h1e; end\n"
      "  end\n"
      "endmodule\n");
  // The definitions boundary, the time marker, and the section are contiguous.
  EXPECT_EQ(Between(content, "$enddefinitions $end\n", "#500"), "") << content;
  EXPECT_NE(content.find("#500\n$dumpvars\n"), std::string::npos) << content;
  auto dumpvars = Section(content, "$dumpvars");
  ASSERT_FALSE(dumpvars.empty()) << content;
  EXPECT_NE(dumpvars.find("x!"), std::string::npos) << dumpvars;
  EXPECT_NE(dumpvars.find("bx \""), std::string::npos) << dumpvars;
  // Each variable is listed exactly once in the initial-value checkpoint.
  EXPECT_EQ(CountOccurrences(dumpvars, "!"), 1u) << dumpvars;
  // The later same-run assignments land under their own time.
  EXPECT_NE(content.find("#505"), std::string::npos) << content;
}

// E3 (pipeline side) + E5 accepting counterpart: the example's 32-bit forms
// -- a [31:0] vector and an integer -- declared in real source carry size 32
// in their $var declarations, and values assigned before the delayed
// $dumpvars surface in the #500 checkpoint as those actual values (the
// example's all-x listing is the nothing-assigned case), while the
// pre-checkpoint assignments still leave no recorded time of their own.
// Codes in name order: acc -> !, idx -> ".
TEST_F(FourStateVcdExampleE2E, ThirtyTwoBitFormsAndPreDumpValuesFromSource) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [31:0] acc;\n"
      "  integer idx;\n"
      "  initial begin\n"
      "    acc = 32'h1e;\n"
      "    idx = 5;\n"
      "    #500 $dumpvars;\n"
      "    #5 idx = 6;\n"
      "  end\n"
      "endmodule\n");
  // The declared 32-bit widths drive the $var size fields (the var_type
  // keyword mapping belongs to Table 21-11's owner, so only the size and
  // reference are pinned here).
  EXPECT_NE(content.find("32 ! acc $end"), std::string::npos) << content;
  EXPECT_NE(content.find("32 \" idx $end"), std::string::npos) << content;
  // The delayed checkpoint lists the values the time-0 assignments left, in
  // the shortened vector form -- not x.
  auto dumpvars = Section(content, "$dumpvars");
  ASSERT_FALSE(dumpvars.empty()) << content;
  EXPECT_NE(dumpvars.find("b11110 !"), std::string::npos) << dumpvars;
  EXPECT_NE(dumpvars.find("b101 \""), std::string::npos) << dumpvars;
  EXPECT_EQ(dumpvars.find("bx"), std::string::npos) << dumpvars;
  // Negative form: the pre-checkpoint assignments were still not recorded at
  // their own time -- the file's first time marker remains the $dumpvars one.
  EXPECT_EQ(content.find('#'), content.find("#500")) << content;
  // The post-checkpoint change lands under its own time as usual.
  EXPECT_NE(content.find("#505\nb110 \""), std::string::npos) << content;
}

// E5 with the variable's value produced by a declaration initializer: the
// delayed checkpoint lists the initializer's value, not x -- the all-x
// listing of the example is specific to variables nothing has set. Codes in
// name order: s -> !, v -> ".
TEST_F(FourStateVcdExampleE2E, InitializerValueListsInDelayedCheckpoint) {
  auto content = RunVcd(
      "module t;\n"
      "  logic s;\n"
      "  logic [7:0] v = 8'h05;\n"
      "  initial begin\n"
      "    s = 1'b0;\n"
      "    #500 $dumpvars;\n"
      "    #5 s = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  auto dumpvars = Section(content, "$dumpvars");
  ASSERT_FALSE(dumpvars.empty()) << content;
  EXPECT_NE(dumpvars.find("0!"), std::string::npos) << dumpvars;
  EXPECT_NE(dumpvars.find("b101 \""), std::string::npos) << dumpvars;
  // Negative form: the initialized vector is not listed as unknown.
  EXPECT_EQ(dumpvars.find("bx"), std::string::npos) << dumpvars;
  EXPECT_NE(content.find("#500\n$dumpvars\n"), std::string::npos) << content;
  EXPECT_NE(content.find("#505\n1!"), std::string::npos) << content;
}

// E6 with the changing object a net: the example's 1-bit objects are nets, so
// a net declared in real source and driven through a continuous assignment
// joins the changed-only groups the same way a variable does -- each new
// value is listed once, in the group of the time unit it arrived in. The
// driving variable's own records are deliberately not asserted: an
// edge-watched driver currently loses its dump records to the assign
// machinery's prev-value resync (upstream defect noted by the §21.7.1.3
// pass), which is not this subclause's rule. Codes: d -> !, w -> ".
TEST_F(FourStateVcdExampleE2E, ContinuousAssignDrivenNetJoinsChangedGroups) {
  auto content = RunVcd(
      "module t;\n"
      "  logic d;\n"
      "  wire w;\n"
      "  assign w = d;\n"
      "  initial begin\n"
      "    d = 1'b0;\n"
      "    $dumpvars;\n"
      "    #10 d = 1'b1;\n"
      "    #10 d = 1'b0;\n"
      "  end\n"
      "endmodule\n");
  // The net's rise is listed in the #10 group and its fall after #20.
  auto at10 = Between(content, "#10\n", "#20");
  EXPECT_NE(at10.find("1\""), std::string::npos) << content;
  auto from20 = content.substr(content.find("#20"));
  EXPECT_NE(from20.find("0\""), std::string::npos) << from20;
  // Changed-only: each net value is recorded exactly once, in its own unit.
  EXPECT_EQ(CountOccurrences(content, "1\""), 1u) << content;
}

// E7 from a different syntactic position: the checkpoint task written inside
// a task body and reached through a task enable stamps its own time marker
// exactly as a directly placed call does -- the file shape does not depend on
// where the producing call sits in the source.
TEST_F(FourStateVcdExampleE2E, TaskBodyInvokedDumpallFollowsItsMarker) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  task checkpoint_now;\n"
      "    $dumpall;\n"
      "  endtask\n"
      "  initial begin\n"
      "    data = 8'h11;\n"
      "    $dumpvars;\n"
      "    #10 data = 8'h22;\n"
      "    #10 checkpoint_now;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("#20\n$dumpall\n"), std::string::npos) << content;
  EXPECT_EQ(CountOccurrences(content, "#20\n"), 1u) << content;
  auto dumpall = Section(content, "$dumpall");
  EXPECT_NE(dumpall.find("b100010 !"), std::string::npos) << dumpall;
}

// E6 with the change produced by a nonblocking assignment: the NBA commit
// delivers the value into the same changed-only group as a blocking
// assignment would -- the group of its own time unit, and no other.
// Codes: s -> !, v -> ".
TEST_F(FourStateVcdExampleE2E, NbaProducedChangesListInTheirOwnGroupOnly) {
  auto content = RunVcd(
      "module t;\n"
      "  logic s;\n"
      "  logic [7:0] v;\n"
      "  initial begin\n"
      "    s = 1'b0; v = 8'h11;\n"
      "    $dumpvars;\n"
      "    #10 s <= 1'b1;\n"
      "    #10 v <= 8'h22;\n"
      "  end\n"
      "endmodule\n");
  // Each NBA-committed value lists exactly in its own time unit's group.
  EXPECT_EQ(Between(content, "#10\n", "#20"), "1!\n") << content;
  auto from20 = content.find("#20");
  ASSERT_NE(from20, std::string::npos) << content;
  auto after20 = content.substr(from20);
  EXPECT_NE(after20.find("b100010 \""), std::string::npos) << after20;
  // Negative form: the unchanged scalar is not re-listed in the later group.
  EXPECT_EQ(after20.find("1!"), std::string::npos) << after20;
}

// E6: after the initial checkpoint, each time unit lists only the variables
// whose values changed during it -- the example's #510/#520/#530 groups carry
// a single record each. Codes in name order: acc -> !, n1 -> ", n2 -> #,
// n3 -> $.
TEST_F(FourStateVcdExampleE2E, LaterTimeUnitsListOnlyChangedVariables) {
  auto content = RunVcd(
      "module t;\n"
      "  logic n1, n2, n3;\n"
      "  logic [31:0] acc;\n"
      "  initial begin\n"
      "    #500 $dumpvars;\n"
      "    #5 begin n1 = 0; n2 = 1; n3 = 1; acc = 32'h1e; end\n"
      "    #5 n3 = 0;\n"
      "    #10 n3 = 1;\n"
      "    #10 n3 = 0;\n"
      "  end\n"
      "endmodule\n");
  // #505 records all four assignments...
  auto at505 = Between(content, "#505\n", "#510");
  EXPECT_NE(at505.find("0\""), std::string::npos) << at505;
  EXPECT_NE(at505.find("1#"), std::string::npos) << at505;
  EXPECT_NE(at505.find("1$"), std::string::npos) << at505;
  EXPECT_NE(at505.find("b11110 !"), std::string::npos) << at505;
  // ...and each following unit carries exactly the one change made in it.
  EXPECT_EQ(Between(content, "#510\n", "#520"), "0$\n") << content;
  EXPECT_EQ(Between(content, "#520\n", "#530"), "1$\n") << content;
}

// E7: the $dumpall checkpoint sits after its own simulation_time command
// (#535 then $dumpall in the example) -- not under the previous time unit's
// marker -- and it lists the current value of every variable, including one
// no incremental group has re-dumped. Codes: moving -> !, steady -> ".
TEST_F(FourStateVcdExampleE2E, DumpallCheckpointFollowsItsOwnTimeMarker) {
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
  // The marker precedes the section, adjacently.
  EXPECT_NE(content.find("#20\n$dumpall\n"), std::string::npos) << content;
  // Negative form: the checkpoint does not land in the previous time unit --
  // nothing but the #10 change sits between the two markers.
  EXPECT_EQ(Between(content, "#10\n", "#20"), "b100010 !\n") << content;
  // One marker introduces the time unit; the checkpoint adds no duplicate.
  EXPECT_EQ(CountOccurrences(content, "#20\n"), 1u) << content;
  auto dumpall = Section(content, "$dumpall");
  EXPECT_NE(dumpall.find("b100010 !"), std::string::npos) << dumpall;
  EXPECT_NE(dumpall.find("b10100101 \""), std::string::npos) << dumpall;
}

// E7 boundary: when a value change and a $dumpall land in the same time unit,
// the single #T marker introduces both -- the change surfaces inside the
// checkpoint and the marker is not repeated for the per-timestep recording.
TEST_F(FourStateVcdExampleE2E, SameTimeChangeAndDumpallShareOneMarker) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h11;\n"
      "    $dumpvars;\n"
      "    #20 begin data = 8'h22; $dumpall; end\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("#20\n$dumpall\n"), std::string::npos) << content;
  EXPECT_EQ(CountOccurrences(content, "#20\n"), 1u) << content;
  // The same-unit value appears once, inside the checkpoint.
  EXPECT_EQ(CountOccurrences(content, "b100010 !"), 1u) << content;
  auto dumpall = Section(content, "$dumpall");
  EXPECT_NE(dumpall.find("b100010 !"), std::string::npos) << dumpall;
}

// E8: the $dumpoff section sits after its own time marker (#1000 then
// $dumpoff in the example), records every variable as x, and opens a silent
// window -- a change made while suspended appears at no time of its own and
// nothing at all is written until the resume. Codes: s -> !, v -> ".
TEST_F(FourStateVcdExampleE2E, DumpoffFollowsItsMarkerAndSilencesTheWindow) {
  auto content = RunVcd(
      "module t;\n"
      "  logic s;\n"
      "  logic [7:0] v;\n"
      "  initial begin\n"
      "    s = 1'b0; v = 8'h11;\n"
      "    $dumpvars;\n"
      "    #10 v = 8'h22;\n"
      "    #10 $dumpoff;\n"
      "    #10 v = 8'h33;\n"
      "    #10 $dumpon;\n"
      "    #10 v = 8'h44;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("#20\n$dumpoff\n"), std::string::npos) << content;
  auto dumpoff = Section(content, "$dumpoff");
  EXPECT_NE(dumpoff.find("x!"), std::string::npos) << dumpoff;
  EXPECT_NE(dumpoff.find("bx \""), std::string::npos) << dumpoff;
  // Negative form: the suspended time unit leaves no trace -- the window
  // between the suspend section's close and the resume marker is empty.
  EXPECT_EQ(content.find("#30"), std::string::npos) << content;
  EXPECT_EQ(Between(content, "$dumpoff\nx!\nbx \"\n$end\n", "#40"), "")
      << content;
}

// E9: the $dumpon section sits after its own time marker (#2000 then $dumpon
// in the example), lists each variable's value at the resume time -- the
// window change surfaces here for the first time -- and recording then
// resumes, so a later change lands under its own marker.
TEST_F(FourStateVcdExampleE2E, DumponFollowsItsMarkerAndResumesRecording) {
  auto content = RunVcd(
      "module t;\n"
      "  logic s;\n"
      "  logic [7:0] v;\n"
      "  initial begin\n"
      "    s = 1'b0; v = 8'h11;\n"
      "    $dumpvars;\n"
      "    #10 v = 8'h22;\n"
      "    #10 $dumpoff;\n"
      "    #10 v = 8'h33;\n"
      "    #10 $dumpon;\n"
      "    #10 v = 8'h44;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("#40\n$dumpon\n"), std::string::npos) << content;
  EXPECT_EQ(CountOccurrences(content, "#40\n"), 1u) << content;
  auto dumpon = Section(content, "$dumpon");
  EXPECT_NE(dumpon.find("0!"), std::string::npos) << dumpon;
  EXPECT_NE(dumpon.find("b110011 \""), std::string::npos) << dumpon;
  // The window value appears only in the resume checkpoint, never at its own
  // time.
  EXPECT_EQ(CountOccurrences(content, "b110011 \""), 1u) << content;
  // Recording is live again: the post-resume change gets its own time unit.
  EXPECT_NE(content.find("#50\nb1000100 \""), std::string::npos) << content;
}

// E7 negative: a checkpoint that emits nothing stamps no time marker. While
// the dump is suspended, $dumpall is silent, so neither a $dumpall section
// nor an orphan #T for its execution time may appear.
TEST_F(FourStateVcdExampleE2E, SuppressedDumpallLeavesNoOrphanTimeMarker) {
  auto content = RunVcd(
      "module t;\n"
      "  logic s;\n"
      "  initial begin\n"
      "    s = 1'b0;\n"
      "    $dumpvars;\n"
      "    #10 $dumpoff;\n"
      "    #10 $dumpall;\n"
      "    #10 $dumpon;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(content.find("$dumpall"), std::string::npos) << content;
  EXPECT_EQ(content.find("#20"), std::string::npos) << content;
  EXPECT_NE(content.find("#30\n$dumpon\n"), std::string::npos) << content;
}

// The whole example, replayed: header, definitions, delayed $dumpvars with
// all-x initial values, incremental changes, a $dumpall checkpoint, a
// suspend/resume pair with a silent window, and a post-resume change -- all
// in the example's order at the example's times. Codes in name order:
// acc -> !, n1 -> ", n2 -> #, n3 -> $.
TEST_F(FourStateVcdExampleE2E, IntegratedExampleReplaysInOrder) {
  auto content = RunVcd(
      "module t;\n"
      "  logic n1, n2, n3;\n"
      "  logic [31:0] acc;\n"
      "  initial begin\n"
      "    #500 $dumpvars;\n"
      "    #5 begin n1 = 0; n2 = 1; n3 = 1; acc = 32'h1e; end\n"
      "    #5 n3 = 0;\n"
      "    #10 n3 = 1;\n"
      "    #10 n3 = 0;\n"
      "    #5 $dumpall;\n"
      "    #5 n3 = 1;\n"
      "    #460 $dumpoff;\n"
      "    #500 n2 = 0;\n"
      "    #500 $dumpon;\n"
      "    #10 n3 = 0;\n"
      "  end\n"
      "endmodule\n");
  size_t last = 0;
  for (const char* mark : {"$enddefinitions", "#500", "$dumpvars", "#505",
                           "#510", "#520", "#530", "#535", "$dumpall", "#540",
                           "#1000", "$dumpoff", "#2000", "$dumpon", "#2010"}) {
    auto pos = content.find(mark, last);
    ASSERT_NE(pos, std::string::npos) << mark << " missing/misordered\n"
                                      << content;
    last = pos + std::strlen(mark);
  }
  // Every checkpoint follows its own marker adjacently.
  EXPECT_NE(content.find("#500\n$dumpvars\n"), std::string::npos);
  EXPECT_NE(content.find("#535\n$dumpall\n"), std::string::npos);
  EXPECT_NE(content.find("#1000\n$dumpoff\n"), std::string::npos);
  EXPECT_NE(content.find("#2000\n$dumpon\n"), std::string::npos);
  // The suspended-window change leaves no time of its own; its value first
  // surfaces in the $dumpon checkpoint.
  EXPECT_EQ(content.find("#1500"), std::string::npos) << content;
  auto dumpon = Section(content, "$dumpon");
  EXPECT_NE(dumpon.find("0#"), std::string::npos) << dumpon;
  // Recording resumes: the final change lands under #2010.
  EXPECT_NE(content.find("#2010\n0$"), std::string::npos) << content;
}

// E2+E3: the example's definitions compose a scope tree -- a module holding a
// nested module (whose three 1-bit variables are declared inside it) and a
// sibling task scope holding a 32-bit reg and a 32-bit integer -- with one
// $upscope closing each $scope before $enddefinitions. Scope-tree traversal
// belongs to the driver, so the composition is observed writer-side; the
// declarations land inside their holding scope's section.
TEST_F(FourStateVcdExampleE2E, NestedAndSiblingScopesComposeDefinitions) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    vcd.BeginScope("top");
    vcd.BeginScope("m1");
    vcd.RegisterSignal("net1", 1, nullptr);
    vcd.RegisterSignal("net2", 1, nullptr);
    vcd.RegisterSignal("net3", 1, nullptr);
    vcd.EndScope();
    vcd.BeginScope("t1", VcdScopeKind::kTask);
    VcdSignalSpec acc;
    acc.name = "accumulator";
    acc.width = 32;
    acc.data_type = VcdDataType::kLogic;
    vcd.RegisterSignal(acc);
    VcdSignalSpec idx;
    idx.name = "index";
    idx.width = 32;
    idx.data_type = VcdDataType::kInt;
    vcd.RegisterSignal(idx);
    vcd.EndScope();
    vcd.EndScope();
    vcd.EndDefinitions();
  }
  auto content = ReadVcd();
  size_t last = 0;
  for (const char* mark :
       {"$scope module top $end", "$scope module m1 $end", "net1", "net2",
        "net3", "$upscope $end", "$scope task t1 $end",
        "$var reg 32 $ accumulator $end", "$var integer 32 % index $end",
        "$upscope $end", "$upscope $end", "$enddefinitions $end"}) {
    auto pos = content.find(mark, last);
    ASSERT_NE(pos, std::string::npos) << mark << " missing/misordered\n"
                                      << content;
    last = pos + std::strlen(mark);
  }
  // Three scopes opened, three closed.
  EXPECT_EQ(CountOccurrences(content, "$scope "), 3u);
  EXPECT_EQ(CountOccurrences(content, "$upscope $end"), 3u);
  // Negative form: the nested module's variables stay inside its section --
  // none is declared before the m1 scope opens.
  EXPECT_EQ(Between(content, "$scope module top $end\n", "$scope module m1"),
            "")
      << content;
}

// E4: a comment section may sit between $enddefinitions and the first
// simulation_time command, as the example's dumper-inserted note does; the
// following timed $dumpvars checkpoint still opens with its time marker.
// Comment insertion and placement are writer-confined, so the writer is
// driven directly with a model-backed variable.
TEST_F(FourStateVcdExampleE2E, CommentMaySitBetweenDefinitionsAndFirstTime) {
  SimFixture f;
  auto* a = MakeVar(f, "a", 1, 0);
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    vcd.BeginScope("top");
    vcd.RegisterSignal("a", 1, a);
    vcd.EndScope();
    vcd.EndDefinitions();
    vcd.WriteComment("values dumped from time 500 onward");
    vcd.ArmDumpvarsStart();
    vcd.DumpAllValues(500);
  }
  auto content = ReadVcd();
  size_t last = 0;
  for (const char* mark : {"$enddefinitions $end", "$comment",
                           "values dumped from time 500 onward", "$end", "#500",
                           "$dumpvars", "0!", "$end"}) {
    auto pos = content.find(mark, last);
    ASSERT_NE(pos, std::string::npos) << mark << " missing/misordered\n"
                                      << content;
    last = pos + std::strlen(mark);
  }
  EXPECT_NE(content.find("#500\n$dumpvars\n"), std::string::npos) << content;
}

}  // namespace
}  // namespace delta
