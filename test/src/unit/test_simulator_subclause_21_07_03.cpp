#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "fixture_vcd_dump_run.h"
#include "helpers_text_lines.h"
#include "helpers_vcd_file_form.h"
#include "simulator/lowerer.h"

namespace delta {
namespace {

class CreatingExtendedVcd : public VcdDumpRunTestBase {
 protected:
  std::string RunVcd(const std::string& src) {
    return RunVcdDump(src, {.scope = "t"});
  }
};

bool NoFusedCommands(const std::vector<std::string>& toks) {
  for (const auto& t : toks) {
    if (t.find('$', 1) != std::string::npos) return false;
  }
  return true;
}

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
  EXPECT_NE(content.find("1!"), std::string::npos);
}

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
  EXPECT_EQ(f.ctx.Vcd().GetDumpportsFileName(), "dump2.dump");
}

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
  ExpectHeaderThenDefinitionsThenValueChanges(content, "$var reg 1 ! a $end",
                                              "#10");
  auto p_change = content.find("#10");
  EXPECT_NE(content.find("1!", p_change), std::string::npos);
}

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
  EXPECT_NE(content.find("$var reg 1 ! a $end"), std::string::npos);
  EXPECT_NE(content.find("$var reg 4 \" b $end"), std::string::npos);
  auto p_defs_end = content.find("$enddefinitions");
  ASSERT_NE(p_defs_end, std::string::npos);
  EXPECT_NE(content.find("1!", p_defs_end), std::string::npos);
  EXPECT_NE(content.find("b1010 \"", p_defs_end), std::string::npos);
}

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
  EXPECT_NE(content.find("$var reg 1 ! a $end"), std::string::npos);
  EXPECT_NE(content.find("$enddefinitions"), std::string::npos);
  EXPECT_NE(content.find("1!"), std::string::npos);
}

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
  const char* openers[] = {"$date", "$version", "$timescale",      "$scope",
                           "$var",  "$upscope", "$enddefinitions", "$dumpvars"};
  size_t opened = 0;
  for (const char* kw : openers) {
    size_t n = CountToken(toks, kw);
    EXPECT_GE(n, 1u) << kw << " missing as a standalone token";
    opened += n;
  }
  EXPECT_EQ(CountToken(toks, "$end"), opened);
  for (const auto& t : toks) {
    if (t[0] != '#') continue;
    ASSERT_GT(t.size(), 1u) << "bare # token";
    for (size_t i = 1; i < t.size(); ++i) {
      ASSERT_TRUE(t[i] >= '0' && t[i] <= '9')
          << "simulation time fused with another command: " << t;
    }
  }
}

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
  ExpectFileIsAsciiText(content);
}

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
  auto p_defs_end = content.find("$enddefinitions");
  ASSERT_NE(p_defs_end, std::string::npos);
  EXPECT_NE(content.find("$dumpvars", p_defs_end), std::string::npos);
  EXPECT_NE(content.find("#15"), std::string::npos);
  EXPECT_NE(content.find("1!", p_defs_end), std::string::npos);
}

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
  EXPECT_NE(content.find("0!", p_defs_end), std::string::npos);
  EXPECT_NE(content.find("b11 \"", p_defs_end), std::string::npos);
  EXPECT_NE(content.find("#10"), std::string::npos);
  EXPECT_NE(content.find("b1100 \"", p_defs_end), std::string::npos);
}

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
  EXPECT_NE(content.find("r3.5 \""), std::string::npos);
  EXPECT_NE(content.find("r1.25 \""), std::string::npos);
  EXPECT_TRUE(NoFusedCommands(Tokens(content)));
}

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
  EXPECT_EQ(content.find("$dumpvars"), std::string::npos);
  EXPECT_EQ(content.find('#'), std::string::npos);
  EXPECT_EQ(content.find("1!"), std::string::npos);
}

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
  f.scheduler.Run();
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(ReadVcd().empty());
}

}  // namespace
}  // namespace delta
