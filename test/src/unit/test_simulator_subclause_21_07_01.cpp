#include <gtest/gtest.h>

#include <string>

#include "fixture_vcd_dump_from_source.h"
#include "fixture_vcd_dump_run.h"
#include "helpers_vcd_file_form.h"

namespace delta {
namespace {

class CreatingFourStateVcd : public VcdDumpRunTestBase {
 protected:
  std::string RunVcd(const std::string& src) { return RunVcdDump(src); }
};

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
  EXPECT_NE(content.find("1!"), std::string::npos);
}

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
  EXPECT_NE(content.find("b10xz01zx \""), std::string::npos);
  EXPECT_NE(content.find("x!"), std::string::npos);
  EXPECT_NE(content.find("z!"), std::string::npos);
  ExpectFileIsAsciiText(content);
}

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
  ExpectHeaderThenDefinitionsThenValueChanges(content, "$var reg 1 ! a $end",
                                              "#10");
  auto p_change = content.find("#10");
  EXPECT_NE(content.find("1!", p_change), std::string::npos);
}

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
  EXPECT_NE(content.find("$var reg 1 ! a $end"), std::string::npos);
  EXPECT_NE(content.find("$var reg 4 \" b $end"), std::string::npos);
  auto p_defs_end = content.find("$enddefinitions");
  ASSERT_NE(p_defs_end, std::string::npos);
  EXPECT_NE(content.find("1!", p_defs_end), std::string::npos);
  EXPECT_NE(content.find("b1010 \"", p_defs_end), std::string::npos);
}

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
  EXPECT_NE(content.find("0!", p_defs_end), std::string::npos);
  EXPECT_NE(content.find("b110 \"", p_defs_end), std::string::npos);
  EXPECT_NE(content.find("1!", p_defs_end), std::string::npos);
}

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
  EXPECT_NE(content.find("$var reg 1 ! a $end"), std::string::npos);
  EXPECT_NE(content.find("$enddefinitions"), std::string::npos);
  EXPECT_NE(content.find("1!"), std::string::npos);
}

class CreatingFourStateVcdFromSourceAlone : public VcdDumpFromSourceTestBase {
 protected:
  static std::string DesignWith(const std::string& tasks) {
    return "module t;\n"
           "  logic a;\n"
           "  initial begin\n"
           "    a = 1'b0;\n" +
           tasks +
           "    #10 a = 1'b1;\n"
           "  end\n"
           "endmodule\n";
  }
};

TEST_F(CreatingFourStateVcdFromSourceAlone, InsertedTasksAndARunCreateTheFile) {
  RunSource(
      DesignWith("    $dumpfile(\"dump1.dump\");\n"
                 "    $dumpvars;\n"));

  EXPECT_NE(DumpFile("dump1.dump").find("$enddefinitions"), std::string::npos);
}

TEST_F(CreatingFourStateVcdFromSourceAlone, ASourceWithNoVcdTaskCreatesNoFile) {
  RunSource(DesignWith(""));

  EXPECT_EQ(NamesWritten(), "");
}

}  // namespace
}  // namespace delta
