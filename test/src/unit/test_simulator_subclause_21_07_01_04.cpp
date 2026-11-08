#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "fixture_vcd_dump_run.h"
#include "helpers_vcd_dump.h"
#include "simulator/lowerer.h"

namespace delta {
namespace {

class DumpallSysTask : public VcdDumpRunTestBase {
 protected:
  std::string RunVcd(const std::string& src) { return RunVcdDump(src); }
};

TEST_F(DumpallSysTask, DumpallEmitsDelimitedCheckpointOfCurrentValues) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h11;\n"
      "    $dumpvars;\n"
      "    #10 data = 8'h22;\n"
      "    #10 $dumpall;\n"
      "  end\n"
      "endmodule\n");
  auto pos = content.find("$dumpall");
  ASSERT_NE(pos, std::string::npos);
  auto end = content.find("$end", pos);
  ASSERT_NE(end, std::string::npos);
  auto val = content.find("b100010 !", pos);
  EXPECT_LT(pos, val);
  EXPECT_LT(val, end);
  EXPECT_EQ(content.find("b10001 !", pos), std::string::npos);
}

TEST_F(DumpallSysTask, DumpallCheckpointIncludesUnchangedVariables) {
  auto content = RunVcd(
      "module t;\n"
      "  logic clk;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    clk = 1; data = 8'h11;\n"
      "    $dumpvars;\n"
      "    #10 data = 8'h22;\n"
      "    #10 $dumpall;\n"
      "  end\n"
      "endmodule\n");
  auto pos = content.find("$dumpall");
  ASSERT_NE(pos, std::string::npos);
  auto end = content.find("$end", pos);
  ASSERT_NE(end, std::string::npos);
  auto steady = content.find("1!", pos);
  auto moved = content.find("b100010 \"", pos);
  EXPECT_LT(pos, steady);
  EXPECT_LT(steady, end);
  EXPECT_LT(pos, moved);
  EXPECT_LT(moved, end);
}

TEST_F(DumpallSysTask, DumpallRecordsValueAssignedInSameTimeUnit) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h11;\n"
      "    $dumpvars;\n"
      "    #10 data = 8'h55;\n"
      "    $dumpall;\n"
      "  end\n"
      "endmodule\n");
  auto pos = content.find("$dumpall");
  ASSERT_NE(pos, std::string::npos);
  auto end = content.find("$end", pos);
  ASSERT_NE(end, std::string::npos);
  auto val = content.find("b1010101 !", pos);
  EXPECT_LT(pos, val);
  EXPECT_LT(val, end);
}

TEST_F(DumpallSysTask, DumpallPreservesUnknownAndHighImpedanceStates) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  logic [7:0] hiz;\n"
      "  initial begin\n"
      "    data = 8'b1010zzzz;\n"
      "    hiz = 8'bz;\n"
      "    $dumpvars;\n"
      "    #10 $dumpall;\n"
      "  end\n"
      "endmodule\n");
  auto pos = content.find("$dumpall");
  ASSERT_NE(pos, std::string::npos);
  auto end = content.find("$end", pos);
  ASSERT_NE(end, std::string::npos);
  auto mixed = content.find("b1010zzzz !", pos);
  auto allz = content.find("bz \"", pos);
  EXPECT_LT(pos, mixed);
  EXPECT_LT(mixed, end);
  EXPECT_LT(pos, allz);
  EXPECT_LT(allz, end);
}

TEST_F(DumpallSysTask, DumpallRecordsRealCurrentValue) {
  auto content = RunVcd(
      "module t;\n"
      "  real r;\n"
      "  initial begin\n"
      "    r = 3.5;\n"
      "    $dumpvars;\n"
      "    #10 r = 4.25;\n"
      "    #10 $dumpall;\n"
      "  end\n"
      "endmodule\n");
  auto pos = content.find("$dumpall");
  ASSERT_NE(pos, std::string::npos);
  auto end = content.find("$end", pos);
  ASSERT_NE(end, std::string::npos);
  auto val = content.find("r4.25 !", pos);
  EXPECT_LT(pos, val);
  EXPECT_LT(val, end);
}

TEST_F(DumpallSysTask, EnabledDumpRecordsOnlyChangedVariablesPerIncrement) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] moving;\n"
      "  logic [7:0] steady;\n"
      "  initial begin\n"
      "    moving = 8'h11; steady = 8'hA5;\n"
      "    $dumpvars;\n"
      "    #10 moving = 8'h22;\n"
      "    #10 moving = 8'h33;\n"
      "  end\n"
      "endmodule\n");
  auto pos10 = content.find("#10");
  ASSERT_NE(pos10, std::string::npos);
  EXPECT_NE(content.find("b100010 !", pos10), std::string::npos);
  EXPECT_NE(content.find("#20"), std::string::npos);
  EXPECT_NE(content.find("b110011 !", pos10), std::string::npos);
  EXPECT_EQ(content.find("b10100101 \"", pos10), std::string::npos);
}

TEST_F(DumpallSysTask, DumpallSurfacesVariableSkippedByChangeRecording) {
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
  auto pos10 = content.find("#10");
  ASSERT_NE(pos10, std::string::npos);
  auto all = content.find("$dumpall");
  ASSERT_NE(all, std::string::npos);
  auto resurfaced = content.find("b10100101 \"", pos10);
  ASSERT_NE(resurfaced, std::string::npos);
  EXPECT_GT(resurfaced, all);
  EXPECT_LT(resurfaced, content.find("$end", all));
}

TEST_F(DumpallSysTask, RepeatedDumpallCallsEachEmitACheckpoint) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h11;\n"
      "    $dumpvars;\n"
      "    #10 $dumpall;\n"
      "    #10 data = 8'h22;\n"
      "    #10 $dumpall;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(CountOccurrences(content, "$dumpall"), 2u);
  auto first = content.find("$dumpall");
  auto second = content.find("$dumpall", first + 1);
  ASSERT_NE(second, std::string::npos);
  auto v1 = content.find("b10001 !", first);
  EXPECT_LT(first, v1);
  EXPECT_LT(v1, second);
  EXPECT_NE(content.find("b100010 !", second), std::string::npos);
}

TEST_F(DumpallSysTask, DumpallAfterDumpfileAndDumpvarsSequence) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    $dumpfile(\"dump1.dump\");\n"
      "    data = 8'h11;\n"
      "    $dumpvars;\n"
      "    #10 data = 8'h22;\n"
      "    #10 $dumpall;\n"
      "  end\n"
      "endmodule\n");
  auto pos = content.find("$dumpall");
  ASSERT_NE(pos, std::string::npos);
  auto end = content.find("$end", pos);
  ASSERT_NE(end, std::string::npos);
  auto val = content.find("b100010 !", pos);
  EXPECT_LT(pos, val);
  EXPECT_LT(val, end);
}

TEST_F(DumpallSysTask, DumpallAfterSuspendResumeRecordsCurrentValue) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h11;\n"
      "    $dumpvars;\n"
      "    #10 $dumpoff;\n"
      "    #10 data = 8'h22;\n"
      "    #10 $dumpon;\n"
      "    #10 $dumpall;\n"
      "  end\n"
      "endmodule\n");
  auto pos = content.find("$dumpall");
  ASSERT_NE(pos, std::string::npos);
  auto end = content.find("$end", pos);
  ASSERT_NE(end, std::string::npos);
  auto val = content.find("b100010 !", pos);
  EXPECT_LT(pos, val);
  EXPECT_LT(val, end);
  EXPECT_EQ(content.find("b10001 !", pos), std::string::npos);
}

TEST_F(DumpallSysTask, DumpallInvokedFromTaskBodyEmitsCheckpoint) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  task snapshot;\n"
      "    $dumpall;\n"
      "  endtask\n"
      "  initial begin\n"
      "    data = 8'h11;\n"
      "    $dumpvars;\n"
      "    #10 snapshot;\n"
      "  end\n"
      "endmodule\n");
  auto pos = content.find("$dumpall");
  ASSERT_NE(pos, std::string::npos);
  auto end = content.find("$end", pos);
  ASSERT_NE(end, std::string::npos);
  auto val = content.find("b10001 !", pos);
  EXPECT_LT(pos, val);
  EXPECT_LT(val, end);
}

TEST_F(DumpallSysTask, WithoutDumpFileDumpallIsHarmless) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  initial begin\n"
      "    data = 8'h11;\n"
      "    #10 $dumpall;\n"
      "    #10 data = 8'h22;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.Vcd().GetVcdWriter(), nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST_F(DumpallSysTask, DumpallRecordsOnlyTheVariablesDumpvarsListed) {
  auto content = RunVcd(
      "module t;\n"
      "  logic [7:0] alpha;\n"
      "  logic [7:0] beta;\n"
      "  initial begin\n"
      "    alpha = 8'hA5;\n"
      "    beta = 8'h3C;\n"
      "    $dumpvars(0, alpha);\n"
      "    #10 $dumpall;\n"
      "  end\n"
      "endmodule\n");
  auto all = content.find("$dumpall");
  ASSERT_NE(all, std::string::npos) << content;
  auto end = content.find("$end", all);
  ASSERT_NE(end, std::string::npos) << content;
  auto section = content.substr(all, end - all);
  EXPECT_NE(section.find("b10100101"), std::string::npos) << section;
  EXPECT_EQ(section.find("b111100"), std::string::npos) << section;
}

}  // namespace
}  // namespace delta
