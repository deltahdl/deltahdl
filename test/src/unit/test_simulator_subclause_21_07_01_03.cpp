#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <vector>

#include "fixture_simulator.h"
#include "fixture_vcd_dump_run.h"
#include "helpers_text_lines.h"
#include "helpers_vcd_dump.h"
#include "simulator/lowerer.h"

namespace delta {
namespace {

class DumpOffOnSysTask : public VcdDumpRunTestBase {
 protected:
  std::string RunVcd(const std::string& src) { return RunVcdDump(src); }
};

std::string VarIdentCode(const std::string& content, std::string_view name) {
  for (const auto& line : AllLines(content)) {
    auto toks = Tokens(line);
    if (toks.size() == 6 && toks[0] == "$var" && toks[4] == name) {
      return toks[3];
    }
  }
  return {};
}

TEST_F(DumpOffOnSysTask, DumpingStartsAtEndOfCurrentTimeUnit) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h11;\n"
      "    #10 data = 8'h22;\n"
      "    $dumpvars;\n"
      "    data = 8'h33;\n"
      "    #10 data = 8'h44;\n"
      "  end\n"
      "endmodule\n");
  auto cp = content.find("$dumpvars");
  ASSERT_NE(cp, std::string::npos);
  EXPECT_NE(content.find("b100010 !", cp), std::string::npos);
  EXPECT_NE(content.find("#10"), std::string::npos);
  EXPECT_NE(content.find("b110011 !"), std::string::npos);
}

TEST_F(DumpOffOnSysTask, NoChangesRecordedBeforeDumpvarsExecutes) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h11;\n"
      "    #5 data = 8'h45;\n"
      "    #5 data = 8'h22;\n"
      "    $dumpvars;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(content.find("#5"), std::string::npos);
  EXPECT_EQ(content.find("b1000101"), std::string::npos);
  EXPECT_NE(content.find("b100010 !"), std::string::npos);
}

TEST_F(DumpOffOnSysTask, ScopedDumpvarsAlsoStartsTheDump) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h11;\n"
      "    #5 data = 8'h45;\n"
      "    #5 data = 8'h22;\n"
      "    $dumpvars(0, data);\n"
      "    data = 8'h33;\n"
      "    #10 data = 8'h44;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(content.find("#5"), std::string::npos);
  EXPECT_EQ(content.find("b1000101"), std::string::npos);
  auto cp = content.find("$dumpvars");
  ASSERT_NE(cp, std::string::npos);
  EXPECT_NE(content.find("b100010 !", cp), std::string::npos);
  EXPECT_NE(content.find("#10"), std::string::npos);
  EXPECT_NE(content.find("b110011 !"), std::string::npos);
}

TEST_F(DumpOffOnSysTask, DumpoffCheckpointRecordsEveryVariableAsX) {
  auto content = RunVcd(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    clk = 1; data = 8'hA5;\n"
      "    $dumpvars;\n"
      "    #10 $dumpoff;\n"
      "  end\n"
      "endmodule\n");
  auto off = content.find("$dumpoff");
  ASSERT_NE(off, std::string::npos);
  auto end = content.find("$end", off);
  ASSERT_NE(end, std::string::npos);
  auto xs = content.find("x!", off);
  auto xv = content.find("bx \"", off);
  EXPECT_LT(off, xs);
  EXPECT_LT(xs, end);
  EXPECT_LT(off, xv);
  EXPECT_LT(xv, end);
}

TEST_F(DumpOffOnSysTask, EventRecordsNothingInSuspendCheckpoint) {
  auto content = RunVcdDump(
      "module t;\n"
      "  event ev;\n"
      "  logic clk;\n"
      "  initial begin\n"
      "    clk = 1'b1;\n"
      "    $dumpvars;\n"
      "    #10 $dumpoff;\n"
      "  end\n"
      "endmodule\n",
      {.registration = VcdSignalRegistration::kContextFiltered});
  auto clk_code = VarIdentCode(content, "clk");
  auto ev_code = VarIdentCode(content, "ev");
  ASSERT_FALSE(clk_code.empty()) << content;
  ASSERT_FALSE(ev_code.empty()) << content;
  auto off = content.find("$dumpoff");
  ASSERT_NE(off, std::string::npos) << content;
  auto end = content.find("$end", off);
  ASSERT_NE(end, std::string::npos) << content;
  auto section = content.substr(off, end - off);
  EXPECT_NE(section.find("x" + clk_code), std::string::npos) << section;
  EXPECT_EQ(section.find(ev_code), std::string::npos) << section;
}

TEST_F(DumpOffOnSysTask, DumpoffRecordsZValuedVariableAsX) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'bz;\n"
      "    $dumpvars;\n"
      "    #10 $dumpoff;\n"
      "  end\n"
      "endmodule\n");
  auto cp = content.find("$dumpvars");
  ASSERT_NE(cp, std::string::npos);
  EXPECT_NE(content.find("bz !", cp), std::string::npos);
  auto off = content.find("$dumpoff");
  ASSERT_NE(off, std::string::npos);
  auto end = content.find("$end", off);
  auto xv = content.find("bx !", off);
  EXPECT_LT(off, xv);
  EXPECT_LT(xv, end);
  EXPECT_EQ(content.find("bz", off), std::string::npos);
}

TEST_F(DumpOffOnSysTask, DumpoffRecordsRealVariableAsRealZero) {
  auto content = RunVcd(
      "module t;\n"
      "  real r;\n"
      "  initial begin\n"
      "    r = 1.5;\n"
      "    $dumpvars;\n"
      "    #10 $dumpoff;\n"
      "  end\n"
      "endmodule\n");
  auto off = content.find("$dumpoff");
  ASSERT_NE(off, std::string::npos);
  EXPECT_NE(content.find("r0 !", off), std::string::npos);
  EXPECT_EQ(content.find("bx", off), std::string::npos);
}

TEST_F(DumpOffOnSysTask, NoValueChangesDumpedWhileSuspended) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h11;\n"
      "    $dumpvars;\n"
      "    #10 data = 8'h22;\n"
      "    #10 $dumpoff;\n"
      "    #10 data = 8'h33;\n"
      "    #10 $dumpon;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(content.find("#30"), std::string::npos);
  auto on = content.find("$dumpon");
  ASSERT_NE(on, std::string::npos);
  EXPECT_GT(content.find("b110011"), on);
}

TEST_F(DumpOffOnSysTask, SameChangesAreDumpedWhenNotSuspended) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h11;\n"
      "    $dumpvars;\n"
      "    #10 data = 8'h22;\n"
      "    #20 data = 8'h33;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("#30"), std::string::npos);
  EXPECT_NE(content.find("b110011 !"), std::string::npos);
}

TEST_F(DumpOffOnSysTask, DumponResumesWithValueAtThatTime) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h11;\n"
      "    $dumpvars;\n"
      "    #10 $dumpoff;\n"
      "    #10 data = 8'h33;\n"
      "    #20 $dumpon;\n"
      "    #10 data = 8'h44;\n"
      "  end\n"
      "endmodule\n");
  auto on = content.find("$dumpon");
  ASSERT_NE(on, std::string::npos);
  auto end = content.find("$end", on);
  ASSERT_NE(end, std::string::npos);
  auto val = content.find("b110011 !", on);
  EXPECT_LT(on, val);
  EXPECT_LT(val, end);
  EXPECT_NE(content.find("#50"), std::string::npos);
  EXPECT_NE(content.find("b1000100 !"), std::string::npos);
}

TEST_F(DumpOffOnSysTask, DumponRecordsRealValueAtResumeTime) {
  auto content = RunVcd(
      "module t;\n"
      "  real r;\n"
      "  initial begin\n"
      "    r = 1.5;\n"
      "    $dumpvars;\n"
      "    #10 $dumpoff;\n"
      "    #10 r = 2.25;\n"
      "    #10 $dumpon;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(content.find("#20"), std::string::npos);
  auto on = content.find("$dumpon");
  ASSERT_NE(on, std::string::npos);
  auto end = content.find("$end", on);
  ASSERT_NE(end, std::string::npos);
  auto val = content.find("r2.25 !", on);
  EXPECT_LT(on, val);
  EXPECT_LT(val, end);
}

TEST_F(DumpOffOnSysTask, DumponCheckpointIncludesUnchangedVariables) {
  auto content = RunVcd(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    clk = 1; data = 8'h11;\n"
      "    $dumpvars;\n"
      "    #10 $dumpoff;\n"
      "    #10 data = 8'h33;\n"
      "    #10 $dumpon;\n"
      "  end\n"
      "endmodule\n");
  auto on = content.find("$dumpon");
  ASSERT_NE(on, std::string::npos);
  auto end = content.find("$end", on);
  ASSERT_NE(end, std::string::npos);
  auto steady = content.find("1!", on);
  auto moved = content.find("b110011 \"", on);
  EXPECT_LT(on, steady);
  EXPECT_LT(steady, end);
  EXPECT_LT(on, moved);
  EXPECT_LT(moved, end);
}

TEST_F(DumpOffOnSysTask, ExampleWindowsBoundTheDumpPeriod) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h01;\n"
      "    #10   $dumpvars;\n"
      "    #200  $dumpoff;\n"
      "    #800  $dumpon;\n"
      "    #900  $dumpoff;\n"
      "  end\n"
      "  initial begin\n"
      "    #100 data = 8'h0A;\n"
      "    #400 data = 8'h0B;\n"
      "    #600 data = 8'h0C;\n"
      "    #900 data = 8'h0D;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(CountOccurrences(content, "$dumpoff"), 2u);
  EXPECT_EQ(CountOccurrences(content, "$dumpon"), 1u);
  EXPECT_NE(content.find("#100"), std::string::npos);
  EXPECT_NE(content.find("b1010 !"), std::string::npos);
  EXPECT_EQ(content.find("#500"), std::string::npos);
  EXPECT_GT(content.find("b1011"), content.find("$dumpon"));
  EXPECT_NE(content.find("#1100"), std::string::npos);
  EXPECT_NE(content.find("b1100 !"), std::string::npos);
  EXPECT_EQ(content.find("#2000"), std::string::npos);
  EXPECT_EQ(content.find("b1101"), std::string::npos);
}

TEST_F(DumpOffOnSysTask, DumpoffInvokedFromTaskBodySuspends) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  task stopdump;\n"
      "    $dumpoff;\n"
      "  endtask\n"
      "  initial begin\n"
      "    data = 8'h11;\n"
      "    $dumpvars;\n"
      "    #10 stopdump;\n"
      "    #10 data = 8'h22;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("$dumpoff"), std::string::npos);
  EXPECT_EQ(content.find("#20"), std::string::npos);
  EXPECT_EQ(content.find("b100010"), std::string::npos);
}

TEST_F(DumpOffOnSysTask, RepeatedSuspendResumeCycles) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h11;\n"
      "    $dumpvars;\n"
      "    #10 $dumpoff;\n"
      "    #10 $dumpon;\n"
      "    #10 $dumpoff;\n"
      "    #10 $dumpon;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(CountOccurrences(content, "$dumpoff"), 2u);
  EXPECT_EQ(CountOccurrences(content, "$dumpon"), 2u);
}

TEST_F(DumpOffOnSysTask, WithoutDumpFileTasksAreHarmless) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h11;\n"
      "    #10 $dumpoff;\n"
      "    #10 $dumpon;\n"
      "    #10 data = 8'h22;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.Vcd().GetVcdWriter(), nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST_F(DumpOffOnSysTask, DumpoffRecordsOnlyTheVariablesDumpvarsListed) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] alpha;\n"
      "  logic [7:0] beta;\n"
      "  initial begin\n"
      "    alpha = 8'hA5;\n"
      "    beta = 8'h3C;\n"
      "    $dumpvars(0, alpha);\n"
      "    #5 $dumpoff;\n"
      "  end\n"
      "endmodule\n");
  auto off = content.find("$dumpoff");
  ASSERT_NE(off, std::string::npos) << content;
  auto end = content.find("$end", off);
  ASSERT_NE(end, std::string::npos) << content;
  auto section = content.substr(off, end - off);
  EXPECT_NE(section.find(VarIdentCode(content, "alpha")), std::string::npos)
      << section;
  EXPECT_EQ(section.find(VarIdentCode(content, "beta")), std::string::npos)
      << section;
}

}  // namespace
}  // namespace delta
