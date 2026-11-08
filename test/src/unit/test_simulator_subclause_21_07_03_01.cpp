#include <gtest/gtest.h>

#include <fstream>
#include <string>

#include "fixture_simulator.h"
#include "fixture_vcd_dump_from_source.h"
#include "fixture_vcd_dump_run.h"
#include "helpers_reported_error.h"
#include "helpers_text_lines.h"
#include "simulator/lowerer.h"

namespace delta {
namespace {

class DumpportsSysTask : public VcdDumpRunTestBase {
 protected:
  std::string RunVcd(SimFixture& f, const std::string& src) {
    return RunVcdDump(f, src, {.scope = "t"});
  }
};

TEST_F(DumpportsSysTask, NoArgumentFormsUseDefaults) {
  SimFixture f1;
  RunVcd(f1,
         "module t;\n"
         "  logic a;\n"
         "  initial begin\n"
         "    a = 1'b1;\n"
         "    $dumpports;\n"
         "  end\n"
         "endmodule\n");
  EXPECT_FALSE(f1.diag.HasErrors());
  EXPECT_EQ(f1.ctx.Vcd().GetDumpportsFileName(), "dumpports.vcd");

  SimFixture f2;
  auto content = RunVcd(f2,
                        "module t;\n"
                        "  logic a;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    $dumpports();\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f2.diag.HasErrors());
  EXPECT_EQ(f2.ctx.Vcd().GetDumpportsFileName(), "dumpports.vcd");
  EXPECT_NE(content.find("1!"), std::string::npos);
}

TEST_F(DumpportsSysTask, NullScopeCommaThenStringLiteralFilename) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  logic b;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    b = 1'b0;\n"
                        "    $dumpports(, \"dump2.dump\");\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(f.ctx.Vcd().GetDumpportsFileName(), "dump2.dump");
  EXPECT_NE(content.find("1!"), std::string::npos);
  EXPECT_NE(content.find("0\""), std::string::npos);
}

TEST_F(DumpportsSysTask, FilenameFromStringTypedVariable) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  string fn;\n"
         "  initial begin\n"
         "    fn = \"sv.vcd\";\n"
         "    $dumpports(, fn);\n"
         "  end\n"
         "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(f.ctx.Vcd().GetDumpportsFileName(), "sv.vcd");
}

TEST_F(DumpportsSysTask, FilenameFromIntegralVariable) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  logic [55:0] fn;\n"
         "  initial begin\n"
         "    fn = \"int.vcd\";\n"
         "    $dumpports(, fn);\n"
         "  end\n"
         "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(f.ctx.Vcd().GetDumpportsFileName(), "int.vcd");
}

TEST_F(DumpportsSysTask, FilenameFromDeclarationInitializedVariable) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  logic [55:0] fn = \"ini.vcd\";\n"
         "  initial $dumpports(, fn);\n"
         "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(f.ctx.Vcd().GetDumpportsFileName(), "ini.vcd");
}

TEST_F(DumpportsSysTask, FilenameFromParameterConstant) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  parameter string FN = \"p.vc\";\n"
         "  initial $dumpports(, FN);\n"
         "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(f.ctx.Vcd().GetDumpportsFileName(), "p.vc");
}

TEST_F(DumpportsSysTask, FilenameFromLocalparamConstant) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  localparam string FN = \"l.vc\";\n"
         "  initial $dumpports(, FN);\n"
         "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(f.ctx.Vcd().GetDumpportsFileName(), "l.vc");
}

TEST_F(DumpportsSysTask, NamesFileIndependentlyOfDumpfileCall) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  logic a;\n"
         "  initial begin\n"
         "    a = 1'b1;\n"
         "    $dumpfile(\"dump1.dump\");\n"
         "    $dumpports(, \"dump2.dump\");\n"
         "  end\n"
         "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(f.ctx.Vcd().GetDumpportsFileName(), "dump2.dump");
}

TEST_F(DumpportsSysTask, UnwritablePathReportedAsError) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  logic a;\n"
         "  initial begin\n"
         "    a = 1'b1;\n"
         "    $dumpports(, \"no_such_dir_21731/f.vcd\");\n"
         "  end\n"
         "endmodule\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot write dump file at path", 5, "21.7.3.1"));
}

TEST_F(DumpportsSysTask, ExistingFileSilentlyOverwritten) {
  {
    std::ofstream stale(tmp_path_);
    stale << "STALE-CONTENT\n";
  }
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  initial begin\n"
                        "    a = 1'b1;\n"
                        "    $dumpports(, \"dump2.dump\");\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(content.find("STALE-CONTENT"), std::string::npos);
  EXPECT_NE(content.find("$date"), std::string::npos);
  EXPECT_NE(content.find("1!"), std::string::npos);
}

TEST_F(DumpportsSysTask, PortsBelowListedScopeNotDumped) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module leafA;\n"
                        "  logic [7:0] deep;\n"
                        "  initial begin\n"
                        "    deep = 8'h3C;\n"
                        "    #5 deep = 8'hFF;\n"
                        "  end\n"
                        "endmodule\n"
                        "module midA;\n"
                        "  logic [7:0] own;\n"
                        "  leafA g1();\n"
                        "  initial begin\n"
                        "    own = 8'hA5;\n"
                        "    #5 own = 8'h0F;\n"
                        "  end\n"
                        "endmodule\n"
                        "module t;\n"
                        "  midA c1();\n"
                        "  initial #1 $dumpports(c1, \"dump2.dump\");\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("b10100101 "), std::string::npos);
  EXPECT_NE(content.find("b1111 \""), std::string::npos);
  EXPECT_EQ(content.find("b111100 "), std::string::npos);
  EXPECT_EQ(content.find("b11111111"), std::string::npos);
}

TEST_F(DumpportsSysTask, HierarchicalPathNamesModuleScope) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module leafA;\n"
                        "  logic [7:0] deep;\n"
                        "  initial deep = 8'h3C;\n"
                        "endmodule\n"
                        "module midA;\n"
                        "  logic [7:0] own;\n"
                        "  leafA g1();\n"
                        "  initial own = 8'hA5;\n"
                        "endmodule\n"
                        "module t;\n"
                        "  midA c1();\n"
                        "  initial $dumpports(c1.g1, \"dump2.dump\");\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("b111100 "), std::string::npos);
  EXPECT_EQ(content.find("b10100101 "), std::string::npos);
}

TEST_F(DumpportsSysTask, MultipleScopeListModulesDumped) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module ma;\n"
                        "  logic [7:0] xa;\n"
                        "  initial xa = 8'h11;\n"
                        "endmodule\n"
                        "module mb;\n"
                        "  logic [7:0] xb;\n"
                        "  initial xb = 8'h22;\n"
                        "endmodule\n"
                        "module mc;\n"
                        "  logic [7:0] xc;\n"
                        "  initial xc = 8'h33;\n"
                        "endmodule\n"
                        "module t;\n"
                        "  ma c1();\n"
                        "  mb c2();\n"
                        "  mc c3();\n"
                        "  initial $dumpports(c1, c2, \"dump2.dump\");\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("b10001 "), std::string::npos);
  EXPECT_NE(content.find("b100010 "), std::string::npos);
  EXPECT_EQ(content.find("b110011"), std::string::npos);
}

TEST_F(DumpportsSysTask, ScopeWithoutFilenameKeepsDefaultName) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module midA;\n"
                        "  logic [7:0] own;\n"
                        "  initial own = 8'hA5;\n"
                        "endmodule\n"
                        "module t;\n"
                        "  midA c1();\n"
                        "  initial $dumpports(c1);\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(f.ctx.Vcd().GetDumpportsFileName(), "dumpports.vcd");
  EXPECT_NE(content.find("b10100101 "), std::string::npos);
}

TEST_F(DumpportsSysTask, StringLiteralScopeRejected) {
  SimFixture f;
  RunVcd(f,
         "module midA;\n"
         "  logic [7:0] own;\n"
         "  initial own = 8'hA5;\n"
         "endmodule\n"
         "module t;\n"
         "  midA c1();\n"
         "  initial $dumpports(\"c1\", \"dump2.dump\");\n"
         "endmodule\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "must be a module, not a string", 7, "21.7.3.1"));
}

TEST_F(DumpportsSysTask, VariableScopeRejected) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  logic [7:0] v;\n"
         "  initial begin\n"
         "    v = 8'h01;\n"
         "    $dumpports(v, \"dump2.dump\");\n"
         "  end\n"
         "endmodule\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "scope_list entry must be a module, not a variable",
                            5, "21.7.3.1"));
}

TEST_F(DumpportsSysTask, DuplicateScopeWithinCallRejected) {
  SimFixture f;
  RunVcd(f,
         "module midA;\n"
         "  logic [7:0] own;\n"
         "  initial own = 8'hA5;\n"
         "endmodule\n"
         "module t;\n"
         "  midA c1();\n"
         "  initial $dumpports(c1, c1, \"dump2.dump\");\n"
         "endmodule\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "scope_list entries must be unique", 7,
                            "21.7.3.1"));
}

TEST_F(DumpportsSysTask, DuplicateScopeAcrossCallsRejected) {
  SimFixture f;
  RunVcd(f,
         "module midA;\n"
         "  logic [7:0] own;\n"
         "  initial own = 8'hA5;\n"
         "endmodule\n"
         "module t;\n"
         "  midA c1();\n"
         "  initial begin\n"
         "    $dumpports(c1, \"f1.vcd\");\n"
         "    $dumpports(c1, \"f2.vcd\");\n"
         "  end\n"
         "endmodule\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "scope already named by an earlier call", 9,
                            "21.7.3.1"));
}

TEST_F(DumpportsSysTask, RepeatedFileNameAcrossCallsRejected) {
  SimFixture f;
  RunVcd(f,
         "module ma;\n"
         "  logic [7:0] xa;\n"
         "  initial xa = 8'h11;\n"
         "endmodule\n"
         "module mb;\n"
         "  logic [7:0] xb;\n"
         "  initial xb = 8'h22;\n"
         "endmodule\n"
         "module t;\n"
         "  ma c1();\n"
         "  mb c2();\n"
         "  initial begin\n"
         "    $dumpports(c1, \"same.vcd\");\n"
         "    $dumpports(c2, \"same.vcd\");\n"
         "  end\n"
         "endmodule\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "may not name the same output file more than once",
                            14, "21.7.3.1"));
}

TEST_F(DumpportsSysTask, MultipleCallsAtSameTimeAllowed) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module ma;\n"
                        "  logic [7:0] xa;\n"
                        "  initial xa = 8'h11;\n"
                        "endmodule\n"
                        "module mb;\n"
                        "  logic [7:0] xb;\n"
                        "  initial xb = 8'h22;\n"
                        "endmodule\n"
                        "module mc;\n"
                        "  logic [7:0] xc;\n"
                        "  initial xc = 8'h33;\n"
                        "endmodule\n"
                        "module t;\n"
                        "  ma c1();\n"
                        "  mb c2();\n"
                        "  mc c3();\n"
                        "  initial begin\n"
                        "    $dumpports(c1, \"f1.vcd\");\n"
                        "    $dumpports(c2, \"f2.vcd\");\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("b10001 "), std::string::npos);
  EXPECT_NE(content.find("b100010 "), std::string::npos);
  EXPECT_EQ(content.find("b110011"), std::string::npos);
}

TEST_F(DumpportsSysTask, CallsAtDifferentTimesRejected) {
  SimFixture f;
  RunVcd(f,
         "module ma;\n"
         "  logic [7:0] xa;\n"
         "  initial xa = 8'h11;\n"
         "endmodule\n"
         "module mb;\n"
         "  logic [7:0] xb;\n"
         "  initial xb = 8'h22;\n"
         "endmodule\n"
         "module t;\n"
         "  ma c1();\n"
         "  mb c2();\n"
         "  initial begin\n"
         "    $dumpports(c1, \"f1.vcd\");\n"
         "    #10 $dumpports(c2, \"f2.vcd\");\n"
         "  end\n"
         "endmodule\n");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "all $dumpports tasks must execute at the same simulation time", 14,
      "21.7.3.1"));
}

TEST_F(DumpportsSysTask, DumpingStartsAtEndOfCurrentTimeUnit) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  initial begin\n"
                        "    a = 1'b0;\n"
                        "    $dumpports(, \"dump2.dump\");\n"
                        "    a = 1'b1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("1!"), std::string::npos);
  EXPECT_EQ(content.find("0!"), std::string::npos);
}

TEST_F(DumpportsSysTask, EndOfUnitStartAtNonzeroExecutionTime) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  initial begin\n"
                        "    a = 1'b0;\n"
                        "    #7 $dumpports(, \"dump2.dump\");\n"
                        "    a = 1'b1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("#7"), std::string::npos);
  EXPECT_NE(content.find("1!"), std::string::npos);
  EXPECT_EQ(content.find("0!"), std::string::npos);
}

TEST_F(DumpportsSysTask, EndOfUnitCheckpointSeesNonblockingUpdate) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  initial begin\n"
                        "    a = 1'b0;\n"
                        "    $dumpports(, \"dump2.dump\");\n"
                        "    a <= 1'b1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("1!"), std::string::npos);
  EXPECT_EQ(content.find("0!"), std::string::npos);
}

TEST_F(DumpportsSysTask, CoexistsWithDumpvarsInSameSource) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic a;\n"
                        "  initial begin\n"
                        "    a = 1'b0;\n"
                        "    $dumpvars;\n"
                        "    $dumpports(, \"dump2.dump\");\n"
                        "    #10 a = 1'b1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  auto first = content.find("$dumpvars");
  ASSERT_NE(first, std::string::npos);
  EXPECT_NE(content.rfind("$dumpvars"), first);
  EXPECT_NE(content.find("#10"), std::string::npos);
  EXPECT_NE(content.find("1!"), std::string::npos);
}

TEST_F(DumpportsSysTask, UnwritablePathNames21_7_3_1) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  logic b;\n"
         "  initial begin\n"
         "    b = 1'b0;\n"
         "    $dumpports(, \"absent_dir_217310/g.vcd\");\n"
         "  end\n"
         "endmodule\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot write dump file at path", 5, "21.7.3.1"));
}

TEST_F(DumpportsSysTask, StringLiteralScopeNames21_7_3_1) {
  SimFixture f;
  RunVcd(f,
         "module subA;\n"
         "  logic [7:0] own;\n"
         "  initial own = 8'h5A;\n"
         "endmodule\n"
         "module t;\n"
         "  subA k1();\n"
         "  initial $dumpports(\"k1\", \"lit.dump\");\n"
         "endmodule\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "not a string literal", 7,
                            "21.7.3.1"));
}

TEST_F(DumpportsSysTask, VariableScopeNames21_7_3_1) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  logic [7:0] w;\n"
         "  initial begin\n"
         "    w = 8'h02;\n"
         "    $dumpports(w, \"var.dump\");\n"
         "  end\n"
         "endmodule\n");
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "not a variable", 5, "21.7.3.1"));
}

TEST_F(DumpportsSysTask, DuplicateScopeWithinCallNames21_7_3_1) {
  SimFixture f;
  RunVcd(f,
         "module subB;\n"
         "  logic [7:0] own;\n"
         "  initial own = 8'h5B;\n"
         "endmodule\n"
         "module t;\n"
         "  subB k2();\n"
         "  initial $dumpports(k2, k2, \"dup.dump\");\n"
         "endmodule\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "scope_list entries must be unique", 7,
                            "21.7.3.1"));
}

TEST_F(DumpportsSysTask, DuplicateScopeAcrossCallsNames21_7_3_1) {
  SimFixture f;
  RunVcd(f,
         "module subC;\n"
         "  logic [7:0] own;\n"
         "  initial own = 8'h5C;\n"
         "endmodule\n"
         "module t;\n"
         "  subC k3();\n"
         "  initial begin\n"
         "    $dumpports(k3, \"g1.vcd\");\n"
         "    $dumpports(k3, \"g2.vcd\");\n"
         "  end\n"
         "endmodule\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "scope already named by an earlier call", 9,
                            "21.7.3.1"));
}

TEST_F(DumpportsSysTask, RepeatedFileNameNames21_7_3_1) {
  SimFixture f;
  RunVcd(f,
         "module na;\n"
         "  logic [7:0] ya;\n"
         "  initial ya = 8'h31;\n"
         "endmodule\n"
         "module nb;\n"
         "  logic [7:0] yb;\n"
         "  initial yb = 8'h32;\n"
         "endmodule\n"
         "module t;\n"
         "  na k4();\n"
         "  nb k5();\n"
         "  initial begin\n"
         "    $dumpports(k4, \"twice.vcd\");\n"
         "    $dumpports(k5, \"twice.vcd\");\n"
         "  end\n"
         "endmodule\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "may not name the same output file", 14,
                            "21.7.3.1"));
}

TEST_F(DumpportsSysTask, CallsAtDifferentTimesName21_7_3_1) {
  SimFixture f;
  RunVcd(f,
         "module nc;\n"
         "  logic [7:0] yc;\n"
         "  initial yc = 8'h41;\n"
         "endmodule\n"
         "module nd;\n"
         "  logic [7:0] yd;\n"
         "  initial yd = 8'h42;\n"
         "endmodule\n"
         "module t;\n"
         "  nc k6();\n"
         "  nd k7();\n"
         "  initial begin\n"
         "    $dumpports(k6, \"h1.vcd\");\n"
         "    #20 $dumpports(k7, \"h2.vcd\");\n"
         "  end\n"
         "endmodule\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "at the same simulation time",
                            14, "21.7.3.1"));
}

class DumpvarsAndDumpportsFromSource : public VcdDumpFromSourceTestBase {
 protected:
  static std::string SourceCalling(const std::string& tasks) {
    return "module t;\n"
           "  logic a;\n"
           "  initial begin\n"
           "    a = 1'b0;\n" +
           tasks +
           "    #1 a = 1'b1;\n"
           "  end\n"
           "endmodule\n";
  }
};

TEST_F(DumpvarsAndDumpportsFromSource, DumpvarsThenDumpportsWritesBothFiles) {
  RunSource(
      SourceCalling("    $dumpfile(\"a.vcd\");\n"
                    "    $dumpvars;\n"
                    "    $dumpports;\n"));
  EXPECT_EQ(NamesWritten(), "a.vcd dumpports.vcd");
  auto four_state = DumpFile("a.vcd");
  EXPECT_TRUE(Holds(four_state, "$var ")) << four_state;
  EXPECT_FALSE(Holds(four_state, "$var port ")) << four_state;
  EXPECT_TRUE(Holds(DumpFile("dumpports.vcd"), "$var port "))
      << DumpFile("dumpports.vcd");
}

TEST_F(DumpvarsAndDumpportsFromSource, DumpportsThenDumpvarsWritesBothFiles) {
  RunSource(
      SourceCalling("    $dumpports;\n"
                    "    $dumpfile(\"a.vcd\");\n"
                    "    $dumpvars;\n"));
  EXPECT_EQ(NamesWritten(), "a.vcd dumpports.vcd");
  auto four_state = DumpFile("a.vcd");
  EXPECT_TRUE(Holds(four_state, "$var ")) << four_state;
  EXPECT_FALSE(Holds(four_state, "$var port ")) << four_state;
  EXPECT_TRUE(Holds(DumpFile("dumpports.vcd"), "$var port "))
      << DumpFile("dumpports.vcd");
}

TEST_F(DumpvarsAndDumpportsFromSource, DumpportsAloneWritesOnlyItsOwnDefault) {
  RunSource(SourceCalling("    $dumpports;\n"));
  EXPECT_EQ(NamesWritten(), "dumpports.vcd");
}

}  // namespace
}  // namespace delta
