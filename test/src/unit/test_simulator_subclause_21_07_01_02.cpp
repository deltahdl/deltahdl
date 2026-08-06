#include "fixture_simulator.h"
#include "fixture_vcd.h"
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

}  // namespace
}  // namespace delta
