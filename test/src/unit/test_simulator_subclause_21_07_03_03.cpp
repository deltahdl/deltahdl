#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "fixture_vcd_dump_run.h"
#include "simulator/lowerer.h"

namespace delta {
namespace {

class DumpportsallSysTask : public VcdDumpRunTestBase {
 protected:
  std::string RunVcd(SimFixture& f, const std::string& src) {
    return RunVcdDump(f, src, {.scope = "t"});
  }
};

TEST_F(DumpportsallSysTask, WritesCheckpointOfAllSelectedPorts) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    d = 8'hA5;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsall(\"p.dump\");\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  auto pos = content.find("$dumpall");
  ASSERT_NE(pos, std::string::npos);
  auto end = content.find("$end", pos);
  ASSERT_NE(end, std::string::npos);
  auto section = content.substr(pos, end - pos);
  EXPECT_NE(section.find("1!"), std::string::npos);
  EXPECT_NE(section.find("b10100101 \""), std::string::npos);
}

TEST_F(DumpportsallSysTask, CheckpointRecordsPortsUnchangedSinceLastStep) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    d = 8'hA5;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #5 a = 1'b0;\n"
                        "    #5 $dumpportsall(\"p.dump\");\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  auto pos = content.find("$dumpall");
  ASSERT_NE(pos, std::string::npos);
  auto end = content.find("$end", pos);
  ASSERT_NE(end, std::string::npos);
  auto section = content.substr(pos, end - pos);
  EXPECT_NE(section.find("0!"), std::string::npos);
  EXPECT_NE(section.find("b10100101 \""), std::string::npos);
}

TEST_F(DumpportsallSysTask, CheckpointFollowsItsTimeMarker) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsall(\"p.dump\");\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("#10\n$dumpall"), std::string::npos);
}

TEST_F(DumpportsallSysTask, DumpingContinuesAfterCheckpoint) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsall(\"p.dump\");\n"
                        "    #10 a = 1'b0;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("$dumpall"), std::string::npos);
  EXPECT_NE(content.find("#20"), std::string::npos);
  EXPECT_NE(content.find("0!"), std::string::npos);
}

TEST_F(DumpportsallSysTask, CheckpointRecordsUnknownValuedPort) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  logic b;\n"
                        "  initial begin\n"
                        "    b = 1'b1;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsall(\"p.dump\");\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  auto pos = content.find("$dumpall");
  ASSERT_NE(pos, std::string::npos);
  auto end = content.find("$end", pos);
  ASSERT_NE(end, std::string::npos);
  auto section = content.substr(pos, end - pos);
  EXPECT_NE(section.find("x!"), std::string::npos);
  EXPECT_NE(section.find("1\""), std::string::npos);
}

TEST_F(DumpportsallSysTask, CheckpointAfterSuspendResumeCycle) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff(\"p.dump\");\n"
                        "    #5 a = 1'b0;\n"
                        "    #5 $dumpportson(\"p.dump\");\n"
                        "    #10 $dumpportsall(\"p.dump\");\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  auto pos = content.find("#30\n$dumpall");
  ASSERT_NE(pos, std::string::npos);
  auto end = content.find("$end", pos);
  ASSERT_NE(end, std::string::npos);
  EXPECT_NE(content.substr(pos, end - pos).find("0!"), std::string::npos);
}

TEST_F(DumpportsallSysTask, NoFilenameCheckpointsAllDumpportsFiles) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsall;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("#10\n$dumpall"), std::string::npos);
  EXPECT_NE(content.find("1!"), std::string::npos);
}

TEST_F(DumpportsallSysTask, EmptyParenFormCheckpointsAllDumpportsFiles) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsall();\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("$dumpall"), std::string::npos);
  EXPECT_NE(content.find("1!"), std::string::npos);
}

TEST_F(DumpportsallSysTask, FilenameFromStringTypedVariable) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  string fn;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    fn = \"p.dump\";\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsall(fn);\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("$dumpall"), std::string::npos);
  EXPECT_NE(content.find("1!"), std::string::npos);
}

TEST_F(DumpportsallSysTask, FilenameFromIntegralVariable) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  logic [47:0] fn = \"p.dump\";\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsall(fn);\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("$dumpall"), std::string::npos);
  EXPECT_NE(content.find("1!"), std::string::npos);
}

TEST_F(DumpportsallSysTask, FilenameFromStringVariableDeclInitializer) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  string fn = \"p.dump\";\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsall(fn);\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("$dumpall"), std::string::npos);
  EXPECT_NE(content.find("1!"), std::string::npos);
}

TEST_F(DumpportsallSysTask, FilenameFromIntegralVariableProceduralAssignment) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  logic [47:0] fn;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    fn = \"p.dump\";\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsall(fn);\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("$dumpall"), std::string::npos);
  EXPECT_NE(content.find("1!"), std::string::npos);
}

TEST_F(DumpportsallSysTask, UnknownFilenameWritesNoCheckpoint) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsall(\"other.vcd\");\n"
                        "    #10 a = 1'b0;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(content.find("$dumpall"), std::string::npos);
  EXPECT_NE(content.find("0!"), std::string::npos);
}

TEST_F(DumpportsallSysTask, UnknownFilenameInVariableWritesNoCheckpoint) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  string fn;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    fn = \"other.vcd\";\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsall(fn);\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(content.find("$dumpall"), std::string::npos);
}

}  // namespace
}  // namespace delta
