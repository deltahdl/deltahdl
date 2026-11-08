#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "fixture_vcd_dump_run.h"
#include "simulator/lowerer.h"

namespace delta {
namespace {

class DumpportsflushSysTask : public VcdMidRunReaderTestBase {
 protected:
  std::string RunVcd(SimFixture& f, const std::string& src) {
    return RunVcdDump(f, src, {.scope = "t", .captured_stdout = &run_output_});
  }
};

TEST_F(DumpportsflushSysTask, NamedFlushStoresBufferedRecordsMidSimulation) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  logic [7:0] d;\n"
                        "  integer rfd;\n"
                        "  integer rch;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
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
  auto mid = MidDump("MID");
  EXPECT_NE(mid.find("#10"), std::string::npos);
  EXPECT_NE(mid.find("b10100101 "), std::string::npos);
  EXPECT_NE(content.find("b10100101 "), std::string::npos);
}

TEST_F(DumpportsflushSysTask, WithoutFlushBufferedRecordsNotYetOnDisk) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  logic [7:0] d;\n"
                        "  integer rfd;\n"
                        "  integer rch;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 d = 8'hA5;\n"
                        "    #10 begin\n" +
                            ReaderSnippet("MID") +
                            "    end\n"
                            "  end\n"
                            "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(MidDump("MID").find("b10100101 "), std::string::npos);
  EXPECT_NE(content.find("b10100101 "), std::string::npos);
}

TEST_F(DumpportsflushSysTask, FlushEmitsNoCommandAndDumpingContinues) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsflush(\"p.dump\");\n"
                        "    #10 d = 8'hA5;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(content.find("flush"), std::string::npos);
  auto t20 = content.find("#20");
  ASSERT_NE(t20, std::string::npos);
  EXPECT_NE(content.find("b10100101 ", t20), std::string::npos);
}

TEST_F(DumpportsflushSysTask, NoArgFlushCoversAllDumpportsFiles) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  logic a;\n"
         "  logic [7:0] d;\n"
         "  integer rfd;\n"
         "  integer rch;\n"
         "  initial begin\n"
         "    a = 1'b1;\n"
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

TEST_F(DumpportsflushSysTask, EmptyParenFlushSameDefaultAction) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  logic a;\n"
         "  logic [7:0] d;\n"
         "  integer rfd;\n"
         "  integer rch;\n"
         "  initial begin\n"
         "    a = 1'b1;\n"
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

TEST_F(DumpportsflushSysTask, StringVariableFilenameDeclInit) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  logic a;\n"
         "  logic [7:0] d;\n"
         "  string fn = \"p.dump\";\n"
         "  integer rfd;\n"
         "  integer rch;\n"
         "  initial begin\n"
         "    a = 1'b1;\n"
         "    d = 8'h00;\n"
         "    $dumpports(, \"p.dump\");\n"
         "    #10 d = 8'hA5;\n"
         "    #10 begin\n"
         "      $dumpportsflush(fn);\n" +
             ReaderSnippet("MID") +
             "    end\n"
             "  end\n"
             "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(MidDump("MID").find("b10100101 "), std::string::npos);
}

TEST_F(DumpportsflushSysTask, StringVariableFilenameProceduralAssign) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  logic a;\n"
         "  logic [7:0] d;\n"
         "  string fn;\n"
         "  integer rfd;\n"
         "  integer rch;\n"
         "  initial begin\n"
         "    a = 1'b1;\n"
         "    d = 8'h00;\n"
         "    fn = \"p.dump\";\n"
         "    $dumpports(, \"p.dump\");\n"
         "    #10 d = 8'hA5;\n"
         "    #10 begin\n"
         "      $dumpportsflush(fn);\n" +
             ReaderSnippet("MID") +
             "    end\n"
             "  end\n"
             "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(MidDump("MID").find("b10100101 "), std::string::npos);
}

TEST_F(DumpportsflushSysTask, IntegralVariableFilenameDeclInit) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  logic a;\n"
         "  logic [7:0] d;\n"
         "  reg [47:0] fn = \"p.dump\";\n"
         "  integer rfd;\n"
         "  integer rch;\n"
         "  initial begin\n"
         "    a = 1'b1;\n"
         "    d = 8'h00;\n"
         "    $dumpports(, \"p.dump\");\n"
         "    #10 d = 8'hA5;\n"
         "    #10 begin\n"
         "      $dumpportsflush(fn);\n" +
             ReaderSnippet("MID") +
             "    end\n"
             "  end\n"
             "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(MidDump("MID").find("b10100101 "), std::string::npos);
}

TEST_F(DumpportsflushSysTask, IntegralVariableFilenameProceduralAssign) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  logic a;\n"
         "  logic [7:0] d;\n"
         "  reg [47:0] fn;\n"
         "  integer rfd;\n"
         "  integer rch;\n"
         "  initial begin\n"
         "    a = 1'b1;\n"
         "    d = 8'h00;\n"
         "    fn = \"p.dump\";\n"
         "    $dumpports(, \"p.dump\");\n"
         "    #10 d = 8'hA5;\n"
         "    #10 begin\n"
         "      $dumpportsflush(fn);\n" +
             ReaderSnippet("MID") +
             "    end\n"
             "  end\n"
             "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(MidDump("MID").find("b10100101 "), std::string::npos);
}

TEST_F(DumpportsflushSysTask, ParameterConstantFilename) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  parameter string FN = \"p.vc\";\n"
         "  logic a;\n"
         "  logic [7:0] d;\n"
         "  integer rfd;\n"
         "  integer rch;\n"
         "  initial begin\n"
         "    a = 1'b1;\n"
         "    d = 8'h00;\n"
         "    $dumpports(, \"p.vc\");\n"
         "    #10 d = 8'hA5;\n"
         "    #10 begin\n"
         "      $dumpportsflush(FN);\n" +
             ReaderSnippet("MID") +
             "    end\n"
             "  end\n"
             "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(MidDump("MID").find("b10100101 "), std::string::npos);
}

TEST_F(DumpportsflushSysTask, LocalparamConstantFilename) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  localparam string FN = \"l.vc\";\n"
         "  logic a;\n"
         "  logic [7:0] d;\n"
         "  integer rfd;\n"
         "  integer rch;\n"
         "  initial begin\n"
         "    a = 1'b1;\n"
         "    d = 8'h00;\n"
         "    $dumpports(, \"l.vc\");\n"
         "    #10 d = 8'hA5;\n"
         "    #10 begin\n"
         "      $dumpportsflush(FN);\n" +
             ReaderSnippet("MID") +
             "    end\n"
             "  end\n"
             "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(MidDump("MID").find("b10100101 "), std::string::npos);
}

TEST_F(DumpportsflushSysTask, RepeatedFlushesAccumulateRecordsWithNoneLost) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  logic a;\n"
         "  logic [7:0] d;\n"
         "  integer rfd;\n"
         "  integer rch;\n"
         "  initial begin\n"
         "    a = 1'b1;\n"
         "    d = 8'h00;\n"
         "    $dumpports(, \"p.dump\");\n"
         "    #10 d = 8'hA5;\n"
         "    #5 begin\n"
         "      $dumpportsflush(\"p.dump\");\n" +
             ReaderSnippet("MID1") +
             "    end\n"
             "    #5 d = 8'hC3;\n"
             "    #5 begin\n"
             "      $dumpportsflush(\"p.dump\");\n" +
             ReaderSnippet("MID2") +
             "    end\n"
             "  end\n"
             "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  auto mid1 = MidDump("MID1");
  EXPECT_NE(mid1.find("b10100101 "), std::string::npos);
  EXPECT_EQ(mid1.find("b11000011 "), std::string::npos);
  auto mid2 = MidDump("MID2");
  EXPECT_NE(mid2.find("b10100101 "), std::string::npos);
  EXPECT_NE(mid2.find("#20"), std::string::npos);
  EXPECT_NE(mid2.find("b11000011 "), std::string::npos);
}

TEST_F(DumpportsflushSysTask, LiteralFlushMatchesDumpportsVariableFilename) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  logic a;\n"
         "  logic [7:0] d;\n"
         "  string dn = \"v.dump\";\n"
         "  integer rfd;\n"
         "  integer rch;\n"
         "  initial begin\n"
         "    a = 1'b1;\n"
         "    d = 8'h00;\n"
         "    $dumpports(, dn);\n"
         "    #10 d = 8'hA5;\n"
         "    #10 begin\n"
         "      $dumpportsflush(\"v.dump\");\n" +
             ReaderSnippet("MID") +
             "    end\n"
             "  end\n"
             "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(MidDump("MID").find("b10100101 "), std::string::npos);
}

TEST_F(DumpportsflushSysTask, UnknownFilenameLiteralFlushIgnored) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  logic [7:0] d;\n"
                        "  integer rfd;\n"
                        "  integer rch;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 d = 8'hA5;\n"
                        "    #10 begin\n"
                        "      $dumpportsflush(\"other.dump\");\n" +
                            ReaderSnippet("MID") +
                            "    end\n"
                            "  end\n"
                            "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(MidDump("MID").find("b10100101 "), std::string::npos);
  EXPECT_NE(content.find("b10100101 "), std::string::npos);
}

TEST_F(DumpportsflushSysTask, UnknownFilenameVariableFlushIgnored) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  logic [7:0] d;\n"
                        "  string fn = \"other.dump\";\n"
                        "  integer rfd;\n"
                        "  integer rch;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 d = 8'hA5;\n"
                        "    #10 begin\n"
                        "      $dumpportsflush(fn);\n" +
                            ReaderSnippet("MID") +
                            "    end\n"
                            "  end\n"
                            "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(MidDump("MID").find("b10100101 "), std::string::npos);
  EXPECT_NE(content.find("b10100101 "), std::string::npos);
}

TEST_F(DumpportsflushSysTask, FlushAfterOpeningCheckpointShowsHeaderMidSim) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  logic a;\n"
         "  integer rfd;\n"
         "  integer rch;\n"
         "  initial begin\n"
         "    a = 1'b1;\n"
         "    $dumpports(, \"p.dump\");\n"
         "    #5 begin\n"
         "      $dumpportsflush(\"p.dump\");\n" +
             ReaderSnippet("MID") +
             "    end\n"
             "  end\n"
             "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  auto mid = MidDump("MID");
  EXPECT_NE(mid.find("$enddefinitions"), std::string::npos);
  EXPECT_NE(mid.find("1!"), std::string::npos);
}

TEST_F(DumpportsflushSysTask, FlushFromAlwaysProcessOnClockEdge) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  logic clk;\n"
         "  logic [7:0] d;\n"
         "  integer rfd;\n"
         "  integer rch;\n"
         "  initial begin\n"
         "    clk = 1'b0;\n"
         "    d = 8'h00;\n"
         "    $dumpports(, \"p.dump\");\n"
         "    #10 d = 8'hA5;\n"
         "    #10 clk = 1'b1;\n"
         "  end\n"
         "  always @(posedge clk) begin\n"
         "    $dumpportsflush(\"p.dump\");\n" +
             ReaderSnippet("MID") +
             "  end\n"
             "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  auto mid = MidDump("MID");
  EXPECT_NE(mid.find("#10"), std::string::npos);
  EXPECT_NE(mid.find("b10100101 "), std::string::npos);
}

TEST_F(DumpportsflushSysTask, FlushWithNoDumpportsFilesIsHarmless) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  logic a;\n"
         "  initial begin\n"
         "    a = 1'b1;\n"
         "    #10 $dumpportsflush;\n"
         "  end\n"
         "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
}  // namespace delta
