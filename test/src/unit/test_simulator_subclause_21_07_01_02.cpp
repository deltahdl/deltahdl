#include <string>

#include "fixture_simulator.h"
#include "fixture_vcd.h"
#include "fixture_vcd_dump_from_source.h"
#include "fixture_vcd_dump_run.h"
#include "simulator/variable.h"
#include "simulator/vcd_writer.h"

namespace delta {
namespace {

class VcdValueChangeSim : public VcdTestBase {};

TEST_F(VcdValueChangeSim, ScalarValueChange) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    auto* var = arena_.Create<Variable>();
    var->value = MakeLogic4VecVal(arena_, 1, 1);
    vcd.RegisterSignal("clk", 1, var);
    vcd.EndDefinitions();
    vcd.WriteTimestamp(0);
    vcd.DumpAllValues();
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("$dumpvars"), std::string::npos);
  EXPECT_NE(content.find("1!"), std::string::npos);
}

TEST_F(VcdValueChangeSim, VectorValueChange) {
  {
    VcdWriter vcd(tmp_path_);
    vcd.WriteHeader("1ns");
    auto* var = arena_.Create<Variable>();
    var->value = MakeLogic4VecVal(arena_, 8, 0xA5);
    vcd.RegisterSignal("data", 8, var);
    vcd.EndDefinitions();
    vcd.WriteTimestamp(0);
    vcd.DumpAllValues();
  }
  auto content = ReadVcd();
  EXPECT_NE(content.find("b10100101 !"), std::string::npos);
}

// Exercises the $dumpvars system task itself (not just the writer) so the
// argument handling defined by §21.7.1.2 is observed end to end. Each test
// drives real source through parse, elaboration, and lowering, registers the
// design's own variables with a real writer the way the simulation driver does
// (§21.7), then runs the design so its $dumpvars call selects among those
// variables. This is what lets each scope argument be observed as the parser
// actually produces it -- a bare identifier or a hierarchical member-access
// path -- rather than a hand-built call operating on hand-registered signals.
class DumpvarsSysTask : public VcdTestBase {
 protected:
  std::string RunDumpvars(const std::string& src) {
    SimFixture f;
    auto* design = ElaborateSrc(src, f);
    if (design == nullptr) return "<elaboration-failed>";
    Lowerer lowerer(f.ctx, f.arena, f.diag);
    lowerer.Lower(design);
    {
      VcdWriter vcd(tmp_path_);
      vcd.WriteHeader("1ns");
      for (const auto& [name, var] : f.ctx.GetVariables()) {
        vcd.RegisterSignal(name, var->value.width, var);
      }
      vcd.EndDefinitions();
      vcd.WriteTimestamp(0);
      f.ctx.SetVcdWriter(&vcd);
      f.scheduler.Run();
    }  // writer destructor flushes the dump to tmp_path_ before ReadVcd
    return ReadVcd();
  }
};

// With no arguments, $dumpvars dumps every variable in the model. Two distinct
// vector values let the dump be checked to carry both.
TEST_F(DumpvarsSysTask, NoArgumentsDumpsEveryVariable) {
  auto content = RunDumpvars(
      "module t;\n"
      "  logic [7:0] alpha;\n"
      "  logic [7:0] beta;\n"
      "  initial begin\n"
      "    alpha = 8'hA5;\n"
      "    beta = 8'h3C;\n"
      "    $dumpvars;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("$dumpvars"), std::string::npos);
  EXPECT_NE(content.find("b10100101"), std::string::npos);  // alpha = 8'hA5
  EXPECT_NE(content.find("b111100"), std::string::npos);    // beta = 8'h3C
}

// The leading argument is consumed as the level count, so supplying only a
// level (no scope list) still dumps every variable rather than selecting none.
TEST_F(DumpvarsSysTask, LevelCountAloneDumpsEveryVariable) {
  auto content = RunDumpvars(
      "module t;\n"
      "  logic [7:0] alpha;\n"
      "  logic [7:0] beta;\n"
      "  initial begin\n"
      "    alpha = 8'hA5;\n"
      "    beta = 8'h3C;\n"
      "    $dumpvars(0);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("b10100101"), std::string::npos);  // alpha
  EXPECT_NE(content.find("b111100"), std::string::npos);    // beta
}

// A scope argument names an individual variable; the leading argument is the
// level count and is not treated as a variable to dump. The unnamed variable is
// left out, exercising the selection's negative path.
TEST_F(DumpvarsSysTask, NamedVariableSelectsOnlyThatVariable) {
  auto content = RunDumpvars(
      "module t;\n"
      "  logic [7:0] alpha;\n"
      "  logic [7:0] beta;\n"
      "  initial begin\n"
      "    alpha = 8'hA5;\n"
      "    beta = 8'h3C;\n"
      "    $dumpvars(0, alpha);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("b10100101"), std::string::npos);  // alpha dumped
  EXPECT_EQ(content.find("b111100"), std::string::npos);    // beta omitted
}

// A scope list may name several individual variables at once; exactly the named
// ones are dumped and the rest are left out.
TEST_F(DumpvarsSysTask, MultipleNamedVariablesSelected) {
  auto content = RunDumpvars(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] b;\n"
      "  logic [7:0] c;\n"
      "  initial begin\n"
      "    a = 8'hA5;\n"
      "    b = 8'h3C;\n"
      "    c = 8'h5A;\n"
      "    $dumpvars(0, a, b);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("b10100101"), std::string::npos);  // a dumped
  EXPECT_NE(content.find("b111100"), std::string::npos);    // b dumped
  EXPECT_EQ(content.find("b1011010"), std::string::npos);   // c = 8'h5A omitted
}

// A hierarchical scope argument (parsed as a member-access chain) selects the
// instance variable it names. The dotted path top-level.instance.leaf is
// rebuilt into the key the child variable is registered under (c1.val), so the
// sibling top-level variable is left out.
TEST_F(DumpvarsSysTask, HierarchicalNameSelectsChildVariable) {
  auto content = RunDumpvars(
      "module child;\n"
      "  logic [7:0] val;\n"
      "endmodule\n"
      "module t;\n"
      "  child c1();\n"
      "  logic [7:0] keep;\n"
      "  initial begin\n"
      "    c1.val = 8'hA5;\n"
      "    keep = 8'h3C;\n"
      "    $dumpvars(0, c1.val);\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("$dumpvars"), std::string::npos);
  EXPECT_NE(content.find("b10100101"), std::string::npos);  // c1.val dumped
  EXPECT_EQ(content.find("b111100"), std::string::npos);    // keep omitted
}

// A scope argument may name a whole module instance rather than one variable.
// With level 0, the dump covers the named module's variables and every module
// instance below it, so both the module's own variable and a grandchild
// instance's variable appear. Each variable is set in its own module's initial
// block and the dump is taken after a delay so the values are settled.
TEST_F(DumpvarsSysTask, ModuleScopeWithLevelZeroDumpsEntireSubtree) {
  auto content = RunDumpvars(
      "module leaf;\n"
      "  logic [7:0] deep;\n"
      "  initial deep = 8'h3C;\n"
      "endmodule\n"
      "module mid;\n"
      "  logic [7:0] own;\n"
      "  leaf g1();\n"
      "  initial own = 8'hA5;\n"
      "endmodule\n"
      "module t;\n"
      "  mid c1();\n"
      "  initial #1 $dumpvars(0, c1);\n"
      "endmodule\n");
  EXPECT_NE(content.find("b10100101"), std::string::npos);  // c1.own (depth 1)
  EXPECT_NE(content.find("b111100"),
            std::string::npos);  // c1.g1.deep (depth 2)
}

// The level count bounds the descent. With level 1, only the named module's own
// variables are dumped; variables in module instances below it are left out.
TEST_F(DumpvarsSysTask, LevelOneDumpsOnlyNamedModuleOwnVariables) {
  auto content = RunDumpvars(
      "module leaf;\n"
      "  logic [7:0] deep;\n"
      "  initial deep = 8'h3C;\n"
      "endmodule\n"
      "module mid;\n"
      "  logic [7:0] own;\n"
      "  leaf g1();\n"
      "  initial own = 8'hA5;\n"
      "endmodule\n"
      "module t;\n"
      "  mid c1();\n"
      "  initial #1 $dumpvars(1, c1);\n"
      "endmodule\n");
  EXPECT_NE(content.find("b10100101"), std::string::npos);  // c1.own (depth 1)
  EXPECT_EQ(content.find("b111100"), std::string::npos);  // c1.g1.deep excluded
}

// $dumpvars may be invoked as often as desired; each call emits its own dump,
// so two calls each selecting a different variable both leave their mark.
TEST_F(DumpvarsSysTask, MayBeInvokedRepeatedly) {
  auto content = RunDumpvars(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [7:0] b;\n"
      "  initial begin\n"
      "    a = 8'hA5;\n"
      "    b = 8'h3C;\n"
      "    $dumpvars(0, a);\n"
      "    $dumpvars(0, b);\n"
      "  end\n"
      "endmodule\n");
  // Two invocations emit two separate dump blocks.
  ASSERT_NE(content.find("$dumpvars"), std::string::npos);
  EXPECT_NE(content.rfind("$dumpvars"), content.find("$dumpvars"));
  EXPECT_NE(content.find("b10100101"), std::string::npos);  // a from first call
  EXPECT_NE(content.find("b111100"), std::string::npos);  // b from second call
}

// §21.7.1.2's scope arguments as a source writes them, which are written from
// the top module down: Example 1 and Example 2 pass "top" itself, and Example
// 3 passes "top.mod1" and "top.mod2.net1". Reaching that form needs the run to
// have a top module -- the one whose $scope the declarations are written under
// and whose name the registration measures every signal from -- so these cases
// let the source open its own dump rather than registering signals against a
// writer the test built, which is what DumpvarsSysTask above does and why the
// scope arguments there are all written relative to the top module instead.
class DumpvarsTopModuleScope : public VcdDumpFromSourceTestBase {
 protected:
  // §21.7.2.3: "the general information in the VCD file is presented as a
  // series of sections surrounded by keywords", so what a $dumpvars call
  // selected is what stands between its keyword and the $end closing it.
  // Reading the section rather than the file is what makes an omission
  // observable: DumpChangedValues records a variable the checkpoint left out
  // when it next changes, so the value of an unselected variable is in the
  // file either way.
  std::string CheckpointSection(const std::string& content) const {
    auto begin = content.find("$dumpvars\n");
    if (begin == std::string::npos) return "<no-checkpoint>";
    begin += std::string("$dumpvars\n").size();
    auto end = content.find("$end", begin);
    if (end == std::string::npos) return "<unterminated-checkpoint>";
    return content.substr(begin, end - begin);
  }

  // The design both cases below dump: a top module with a variable of its own
  // and a child instance with another, each set before the dump is specified
  // so the checkpoint records a value that says which of the two it is.
  static std::string Design(const std::string& dumpvars_args) {
    return "module child;\n"
           "  logic [7:0] val;\n"
           "endmodule\n"
           "module t;\n"
           "  child c1();\n"
           "  logic [7:0] own;\n"
           "  initial begin\n"
           "    own = 8'hA5;\n"
           "    c1.val = 8'h3C;\n"
           "    $dumpfile(\"dump.vcd\");\n"
           "    $dumpvars(" +
           dumpvars_args +
           ");\n"
           "  end\n"
           "endmodule\n";
  }
};

// Example 2: "$dumpvars (0, top);" -- "the $dumpvars task shall dump all
// variables in the module top and in all module instances below module top in
// the hierarchy". The top module's own variables are registered under their
// bare names and a child instance's under a path that does not carry the top
// module either, so a scope naming the top module matched no signal at all and
// the checkpoint came out empty.
TEST_F(DumpvarsTopModuleScope, TopModuleAtLevelZeroDumpsItsOwnAndThoseBelow) {
  RunSource(Design("0, t"));
  auto section = CheckpointSection(DumpFile("dump.vcd"));
  EXPECT_NE(section.find("b10100101"), std::string::npos) << section;  // own
  EXPECT_NE(section.find("b111100"), std::string::npos) << section;    // c1.val
}

// Example 1: "$dumpvars (1, top);" -- "this invocation dumps all variables
// within the module top; it does not dump variables in any of the modules
// instantiated by module top". The level counts hierarchy below the named
// scope, so the top module's own variables are the one level it admits.
TEST_F(DumpvarsTopModuleScope, TopModuleAtLevelOneStopsAtItsOwnVariables) {
  RunSource(Design("1, t"));
  auto section = CheckpointSection(DumpFile("dump.vcd"));
  EXPECT_NE(section.find("b10100101"), std::string::npos) << section;  // own
  EXPECT_EQ(section.find("b111100"), std::string::npos) << section;    // c1.val
}

// Example 3's "top.mod1": a scope argument naming an instance beneath the top
// module carries the top module's name in front of it, while the instance is
// registered without it. So the name comes off the argument rather than the
// argument being matched whole, and what is left selects the instance.
TEST_F(DumpvarsTopModuleScope, AChildNamedThroughTheTopModuleSelectsThatChild) {
  RunSource(Design("0, t.c1"));
  auto section = CheckpointSection(DumpFile("dump.vcd"));
  EXPECT_NE(section.find("b111100"), std::string::npos) << section;    // c1.val
  EXPECT_EQ(section.find("b10100101"), std::string::npos) << section;  // own
}

// §21.7.1.2: "The $dumpvars task shall be used to list which variables to dump
// into the file specified by $dumpfile." What a call listed therefore governs
// the whole recording rather than the one checkpoint the call writes, so these
// cases run the driver's per-timestep change pass -- which DumpvarsSysTask
// above installs no callback for -- and read what reaches the file after the
// checkpoint has been written. Registration is by name order, so the
// alphabetically first variable carries the identifier code '!'.
class DumpvarsSelectsWhatIsRecorded : public VcdDumpRunTestBase {
 protected:
  std::string RunVcd(const std::string& src) { return RunVcdDump(src); }

  // A design whose two variables take distinct values one time unit after the
  // dump is specified, so a value in the file names which variable produced it
  // and the change pass rather than the checkpoint is what put it there.
  static std::string Design(const std::string& dumpvars_calls) {
    return "module t;\n"
           "  logic [7:0] alpha;\n"
           "  logic [7:0] beta;\n"
           "  initial begin\n" +
           dumpvars_calls +
           "    #1 alpha = 8'hA5;\n"
           "    beta = 8'h3C;\n"
           "  end\n"
           "endmodule\n";
  }
};

// A variable outside the scope list is outside the dump: its value change is
// not recorded when it arrives, any more than its value was recorded in the
// checkpoint. The listed variable's change is recorded in the same run, so the
// claim is about which variable rather than about whether anything was dumped.
TEST_F(DumpvarsSelectsWhatIsRecorded, AnUnlistedVariablesChangeIsNotRecorded) {
  auto content = RunVcd(Design("    $dumpvars(0, alpha);\n"));
  EXPECT_NE(content.find("b10100101"), std::string::npos) << content;  // alpha
  EXPECT_EQ(content.find("b111100"), std::string::npos) << content;    // beta
}

// §21.7.1.2: "When invoked with no arguments, $dumpvars dumps all the
// variables in the model to the VCD file", so both changes are recorded.
TEST_F(DumpvarsSelectsWhatIsRecorded, NoArgumentsRecordsEveryVariablesChange) {
  auto content = RunVcd(Design("    $dumpvars;\n"));
  EXPECT_NE(content.find("b10100101"), std::string::npos) << content;  // alpha
  EXPECT_NE(content.find("b111100"), std::string::npos) << content;    // beta
}

// §21.7.1.2: the task "can be invoked as often as desired throughout the
// model", and each invocation lists variables to dump rather than replacing
// what an earlier one listed, so two calls naming one variable each leave both
// in the dump.
TEST_F(DumpvarsSelectsWhatIsRecorded, ASecondCallAddsToWhatIsRecorded) {
  auto content =
      RunVcd(Design("    $dumpvars(0, alpha);\n"
                    "    $dumpvars(0, beta);\n"));
  EXPECT_NE(content.find("b10100101"), std::string::npos) << content;  // alpha
  EXPECT_NE(content.find("b111100"), std::string::npos) << content;    // beta
}

// The same rule read the other way round: a no-argument call has already
// listed every variable in the model, so a later scope list adds nothing and
// takes nothing back. Without this the two calls would be read in order and
// the second would narrow the dump to what it names.
TEST_F(DumpvarsSelectsWhatIsRecorded,
       AScopeListAfterNoArgumentsNarrowsNothing) {
  auto content =
      RunVcd(Design("    $dumpvars;\n"
                    "    $dumpvars(0, alpha);\n"));
  EXPECT_NE(content.find("b10100101"), std::string::npos) << content;  // alpha
  EXPECT_NE(content.find("b111100"), std::string::npos) << content;    // beta
}

}  // namespace
}  // namespace delta
