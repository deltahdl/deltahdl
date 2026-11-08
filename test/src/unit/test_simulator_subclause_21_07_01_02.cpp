#include <gtest/gtest.h>

#include <initializer_list>
#include <string>

#include "common/types.h"
#include "fixture_simulator.h"
#include "fixture_vcd.h"
#include "fixture_vcd_dump_from_source.h"
#include "fixture_vcd_dump_run.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"
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
      f.ctx.Vcd().SetVcdWriter(&vcd);
      f.scheduler.Run();
    }
    return ReadVcd();
  }
};

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
  EXPECT_NE(content.find("b10100101"), std::string::npos);
  EXPECT_NE(content.find("b111100"), std::string::npos);
}

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
  EXPECT_NE(content.find("b10100101"), std::string::npos);
  EXPECT_NE(content.find("b111100"), std::string::npos);
}

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
  EXPECT_NE(content.find("b10100101"), std::string::npos);
  EXPECT_EQ(content.find("b111100"), std::string::npos);
}

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
  EXPECT_NE(content.find("b10100101"), std::string::npos);
  EXPECT_NE(content.find("b111100"), std::string::npos);
  EXPECT_EQ(content.find("b1011010"), std::string::npos);
}

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
  EXPECT_NE(content.find("b10100101"), std::string::npos);
  EXPECT_EQ(content.find("b111100"), std::string::npos);
}

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
  EXPECT_NE(content.find("b10100101"), std::string::npos);
  EXPECT_NE(content.find("b111100"), std::string::npos);
}

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
  EXPECT_NE(content.find("b10100101"), std::string::npos);
  EXPECT_EQ(content.find("b111100"), std::string::npos);
}

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
  ASSERT_NE(content.find("$dumpvars"), std::string::npos);
  EXPECT_NE(content.rfind("$dumpvars"), content.find("$dumpvars"));
  EXPECT_NE(content.find("b10100101"), std::string::npos);
  EXPECT_NE(content.find("b111100"), std::string::npos);
}

class DumpvarsTopModuleScope : public VcdDumpFromSourceTestBase {
 protected:
  std::string CheckpointSection(const std::string& content) const {
    auto begin = content.find("$dumpvars\n");
    if (begin == std::string::npos) return "<no-checkpoint>";
    begin += std::string("$dumpvars\n").size();
    auto end = content.find("$end", begin);
    if (end == std::string::npos) return "<unterminated-checkpoint>";
    return content.substr(begin, end - begin);
  }

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

TEST_F(DumpvarsTopModuleScope, TopModuleAtLevelZeroDumpsItsOwnAndThoseBelow) {
  RunSource(Design("0, t"));
  auto section = CheckpointSection(DumpFile("dump.vcd"));
  EXPECT_NE(section.find("b10100101"), std::string::npos) << section;
  EXPECT_NE(section.find("b111100"), std::string::npos) << section;
}

TEST_F(DumpvarsTopModuleScope, TopModuleAtLevelOneStopsAtItsOwnVariables) {
  RunSource(Design("1, t"));
  auto section = CheckpointSection(DumpFile("dump.vcd"));
  EXPECT_NE(section.find("b10100101"), std::string::npos) << section;
  EXPECT_EQ(section.find("b111100"), std::string::npos) << section;
}

TEST_F(DumpvarsTopModuleScope, AChildNamedThroughTheTopModuleSelectsThatChild) {
  RunSource(Design("0, t.c1"));
  auto section = CheckpointSection(DumpFile("dump.vcd"));
  EXPECT_NE(section.find("b111100"), std::string::npos) << section;
  EXPECT_EQ(section.find("b10100101"), std::string::npos) << section;
}

TEST_F(DumpvarsTopModuleScope, TopModuleAtLevelOneDeclaresOnlyItsOwnVariables) {
  RunSource(Design("1, t"));
  auto content = DumpFile("dump.vcd");
  EXPECT_NE(content.find(" own $end"), std::string::npos) << content;
  EXPECT_EQ(content.find(" val $end"), std::string::npos) << content;
  EXPECT_EQ(content.find("$scope module c1 $end"), std::string::npos)
      << content;
}

TEST_F(DumpvarsTopModuleScope, ANamedChildVariableIsTheOneDeclared) {
  RunSource(Design("0, t.c1.val"));
  auto content = DumpFile("dump.vcd");
  EXPECT_EQ(content.find(" own $end"), std::string::npos) << content;
  auto t_scope = content.find("$scope module t $end");
  auto c1_scope = content.find("$scope module c1 $end");
  auto val = content.find(" val $end");
  ASSERT_NE(val, std::string::npos) << content;
  EXPECT_LT(t_scope, c1_scope) << content;
  EXPECT_LT(c1_scope, val) << content;
}

TEST_F(DumpvarsTopModuleScope, TwoCallsInOneTimeUnitDeclareBothSelections) {
  RunSource(Design("0, t.own);\n    $dumpvars(0, t.c1.val"));
  auto content = DumpFile("dump.vcd");
  auto end_defs = content.find("$enddefinitions");
  ASSERT_NE(end_defs, std::string::npos) << content;
  EXPECT_LT(content.find(" own $end"), end_defs) << content;
  EXPECT_LT(content.find(" val $end"), end_defs) << content;
  auto first = content.find("$dumpvars\n");
  EXPECT_LT(end_defs, first) << content;
  EXPECT_NE(content.find("$dumpvars\n", first + 1), std::string::npos)
      << content;
}

class DumpvarsSelectsWhatIsRecorded : public VcdDumpRunTestBase {
 protected:
  std::string RunVcd(const std::string& src) { return RunVcdDump(src); }

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

TEST_F(DumpvarsSelectsWhatIsRecorded, AnUnlistedVariablesChangeIsNotRecorded) {
  auto content = RunVcd(Design("    $dumpvars(0, alpha);\n"));
  EXPECT_NE(content.find("b10100101"), std::string::npos) << content;
  EXPECT_EQ(content.find("b111100"), std::string::npos) << content;
}

TEST_F(DumpvarsSelectsWhatIsRecorded, NoArgumentsRecordsEveryVariablesChange) {
  auto content = RunVcd(Design("    $dumpvars;\n"));
  EXPECT_NE(content.find("b10100101"), std::string::npos) << content;
  EXPECT_NE(content.find("b111100"), std::string::npos) << content;
}

TEST_F(DumpvarsSelectsWhatIsRecorded, ASecondCallAddsToWhatIsRecorded) {
  auto content =
      RunVcd(Design("    $dumpvars(0, alpha);\n"
                    "    $dumpvars(0, beta);\n"));
  EXPECT_NE(content.find("b10100101"), std::string::npos) << content;
  EXPECT_NE(content.find("b111100"), std::string::npos) << content;
}

TEST_F(DumpvarsSelectsWhatIsRecorded,
       AScopeListAfterNoArgumentsNarrowsNothing) {
  auto content =
      RunVcd(Design("    $dumpvars;\n"
                    "    $dumpvars(0, alpha);\n"));
  EXPECT_NE(content.find("b10100101"), std::string::npos) << content;
  EXPECT_NE(content.find("b111100"), std::string::npos) << content;
}

class DumpvarsCallTimes : public VcdDumpRunTestBase {
 protected:
  std::string RunVcd(SimFixture& f, const std::string& src) {
    return RunVcdDump(f, src);
  }
};

TEST_F(DumpvarsCallTimes, ACallInAnotherTimeUnitIsReported) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  logic [7:0] a;\n"
         "  logic [7:0] b;\n"
         "  initial begin\n"
         "    a = 8'hA5;\n"
         "    $dumpvars(0, a);\n"
         "    #1 b = 8'h3C;\n"
         "    $dumpvars(0, b);\n"
         "  end\n"
         "endmodule\n");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "all $dumpvars tasks must execute at the same simulation time", 8,
      "21.7.1.2"));
}

TEST_F(DumpvarsCallTimes, TwoCallsInOneTimeUnitFromTwoBlocksAreAccepted) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  logic [7:0] a;\n"
         "  logic [7:0] b;\n"
         "  initial begin\n"
         "    a = 8'hA5;\n"
         "    $dumpvars(0, a);\n"
         "  end\n"
         "  initial begin\n"
         "    b = 8'h3C;\n"
         "    $dumpvars(0, b);\n"
         "  end\n"
         "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST_F(DumpvarsCallTimes, AloneCallAfterADelayIsAccepted) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  logic [7:0] a;\n"
         "  initial begin\n"
         "    a = 8'hA5;\n"
         "    #5 $dumpvars(0, a);\n"
         "  end\n"
         "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

class VcdEnumConstantSim : public VcdDumpFromSourceTestBase {};

TEST_F(VcdEnumConstantSim, EnumConstantsAreNoVariablesOfTheDump) {
  RunSource(
      "typedef enum {E, F} cu_t;\n"
      "package p;\n"
      "  enum {C, D} pe;\n"
      "endpackage\n"
      "module m;\n"
      "  enum {A, B} e;\n"
      "  cu_t u;\n"
      "  initial begin\n"
      "    $dumpfile(\"enum.vcd\");\n"
      "    $dumpvars;\n"
      "    e = B;\n"
      "    #1 e = A;\n"
      "  end\n"
      "endmodule\n");
  const std::string kDump = DumpFile("enum.vcd");
  EXPECT_NE(kDump.find("$var integer 32 "), std::string::npos) << kDump;
  EXPECT_NE(kDump.find(" e $end"), std::string::npos) << kDump;
  for (const char* constant :
       {" A $end", " B $end", " C $end", " D $end", " E $end", " F $end"}) {
    EXPECT_EQ(kDump.find(constant), std::string::npos) << constant << kDump;
  }
}

}  // namespace
}  // namespace delta
