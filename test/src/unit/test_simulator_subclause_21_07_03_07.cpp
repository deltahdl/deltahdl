#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "fixture_vcd_dump_run.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"

namespace delta {
namespace {

class ExtendedVcdGeneralRules : public VcdMidRunReaderTestBase {
 protected:
  std::string RunVcd(SimFixture& f, const std::string& src) {
    return RunVcdDump(f, src, {.scope = "t", .captured_stdout = &run_output_});
  }
};

TEST_F(ExtendedVcdGeneralRules, OffNamingUnspecifiedFileIsIgnored) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff(\"nomatch.dump\");\n"
                        "    #10 d = 8'hA5;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(content.find("$dumpoff"), std::string::npos);
  auto t20 = content.find("#20");
  ASSERT_NE(t20, std::string::npos);
  EXPECT_NE(content.find("b10100101 ", t20), std::string::npos);
}

TEST_F(ExtendedVcdGeneralRules, OffNamingSpecifiedFileIsApplied) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff(\"p.dump\");\n"
                        "    #10 d = 8'hA5;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("$dumpoff"), std::string::npos);
  EXPECT_EQ(content.find("b10100101 "), std::string::npos);
}

TEST_F(ExtendedVcdGeneralRules, OnNamingUnspecifiedFileIsIgnored) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff(\"p.dump\");\n"
                        "    #10 $dumpportson(\"nomatch.dump\");\n"
                        "    #10 d = 8'hA5;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("$dumpoff"), std::string::npos);
  EXPECT_EQ(content.find("$dumpon"), std::string::npos);
  EXPECT_EQ(content.find("b10100101 "), std::string::npos);
}

TEST_F(ExtendedVcdGeneralRules, OnNamingSpecifiedFileIsApplied) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff(\"p.dump\");\n"
                        "    #10 $dumpportson(\"p.dump\");\n"
                        "    #10 d = 8'hA5;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  auto on = content.find("$dumpon");
  ASSERT_NE(on, std::string::npos);
  EXPECT_NE(content.find("b10100101 ", on), std::string::npos);
}

TEST_F(ExtendedVcdGeneralRules, AllNamingUnspecifiedFileIsIgnored) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'hA5;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsall(\"nomatch.dump\");\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(content.find("$dumpall"), std::string::npos);
}

TEST_F(ExtendedVcdGeneralRules, FlushNamingUnspecifiedFileIsIgnored) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  integer rfd;\n"
                        "  integer rch;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 d = 8'hA5;\n"
                        "    #10 begin\n"
                        "      $dumpportsflush(\"nomatch.dump\");\n" +
                            ReaderSnippet("MID") +
                            "    end\n"
                            "  end\n"
                            "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(MidDump("MID").find("b10100101 "), std::string::npos);
  EXPECT_NE(content.find("b10100101 "), std::string::npos);
}

TEST_F(ExtendedVcdGeneralRules, FlushNamingSpecifiedFileIsApplied) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  logic [7:0] d;\n"
         "  integer rfd;\n"
         "  integer rch;\n"
         "  initial begin\n"
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
  EXPECT_NE(MidDump("MID").find("b10100101 "), std::string::npos);
}

TEST_F(ExtendedVcdGeneralRules, LimitNamingUnspecifiedFileIsIgnored) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    $dumpportslimit(300, \"nomatch.dump\");\n"
                        "    repeat (40) #10 d = d + 1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(content.find("$comment"), std::string::npos);
  EXPECT_NE(content.find("#400\n"), std::string::npos);
}

TEST_F(ExtendedVcdGeneralRules, LimitNamingSpecifiedFileIsApplied) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    $dumpportslimit(300, \"p.dump\");\n"
                        "    repeat (40) #10 d = d + 1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("$comment"), std::string::npos);
  EXPECT_EQ(content.find("#400\n"), std::string::npos);
}

TEST_F(ExtendedVcdGeneralRules, UnmatchedFilenameIgnoredFromTaskBody) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  task try_off;\n"
                        "    $dumpportsoff(\"nomatch.dump\");\n"
                        "  endtask\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 try_off;\n"
                        "    #10 d = 8'hA5;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(content.find("$dumpoff"), std::string::npos);
  auto t20 = content.find("#20");
  ASSERT_NE(t20, std::string::npos);
  EXPECT_NE(content.find("b10100101 ", t20), std::string::npos);
}

TEST_F(ExtendedVcdGeneralRules, UnmatchedFilenameIgnoredFromAlwaysProcess) {
  SimFixture f;
  auto content =
      RunVcd(f,
             "module t;\n"
             "  logic clk;\n"
             "  logic [7:0] d;\n"
             "  always @(posedge clk) $dumpportsall(\"nomatch.dump\");\n"
             "  initial begin\n"
             "    clk = 1'b0;\n"
             "    d = 8'hA5;\n"
             "    $dumpports(, \"p.dump\");\n"
             "    #10 clk = 1'b1;\n"
             "  end\n"
             "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(content.find("$dumpall"), std::string::npos);
}

TEST_F(ExtendedVcdGeneralRules, StringVariableDeclInitUnspecifiedIgnored) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  string fn = \"nomatch.dump\";\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff(fn);\n"
                        "    #10 d = 8'hA5;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(content.find("$dumpoff"), std::string::npos);
  EXPECT_NE(content.find("b10100101 "), std::string::npos);
}

TEST_F(ExtendedVcdGeneralRules, StringVariableProceduralSpecifiedApplied) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  string fn;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    fn = \"p.dump\";\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff(fn);\n"
                        "    #10 d = 8'hA5;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("$dumpoff"), std::string::npos);
  EXPECT_EQ(content.find("b10100101 "), std::string::npos);
}

TEST_F(ExtendedVcdGeneralRules, IntegralVariableDeclInitUnspecifiedIgnored) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  logic [95:0] fn = \"nomatch.dump\";\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff(fn);\n"
                        "    #10 d = 8'hA5;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(content.find("$dumpoff"), std::string::npos);
  EXPECT_NE(content.find("b10100101 "), std::string::npos);
}

TEST_F(ExtendedVcdGeneralRules, IntegralVariableProceduralSpecifiedApplied) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  logic [47:0] fn;\n"
                        "  initial begin\n"
                        "    d = 8'hA5;\n"
                        "    fn = \"p.dump\";\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsall(fn);\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("$dumpall"), std::string::npos);
}

TEST_F(ExtendedVcdGeneralRules, ParameterFilenameSpecifiedApplied) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  parameter P = \"p.d\";\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.d\");\n"
                        "    #10 $dumpportsoff(P);\n"
                        "    #10 d = 8'hA5;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("$dumpoff"), std::string::npos);
  EXPECT_EQ(content.find("b10100101 "), std::string::npos);
}

TEST_F(ExtendedVcdGeneralRules, LocalparamFilenameUnspecifiedIgnored) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  localparam L = \"no.d\";\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.d\");\n"
                        "    #10 $dumpportsoff(L);\n"
                        "    #10 d = 8'hA5;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(content.find("$dumpoff"), std::string::npos);
  EXPECT_NE(content.find("b10100101 "), std::string::npos);
}

TEST_F(ExtendedVcdGeneralRules, LiteralMatchesVariableSpecifiedName) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  string fn = \"p.dump\";\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, fn);\n"
                        "    #10 $dumpportsoff(\"p.dump\");\n"
                        "    #10 d = 8'hA5;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("$dumpoff"), std::string::npos);
  EXPECT_EQ(content.find("b10100101 "), std::string::npos);
}

TEST_F(ExtendedVcdGeneralRules, NamedTaskAppliesWhenNoFilenameSpecified) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports;\n"
                        "    #10 $dumpportsoff(\"any.dump\");\n"
                        "    #10 d = 8'hA5;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(content.find("$dumpoff"), std::string::npos);
  EXPECT_EQ(content.find("b10100101 "), std::string::npos);
}

TEST_F(ExtendedVcdGeneralRules, EmptyParenSameDefaultActionAsBare) {
  auto tail = [](const std::string& s) {
    auto p = s.find("$enddefinitions");
    return p == std::string::npos ? s : s.substr(p);
  };
  const std::string kCommonHead =
      "module t;\n"
      "  logic [7:0] d;\n"
      "  initial begin\n"
      "    d = 8'h00;\n"
      "    $dumpports(, \"p.dump\");\n";
  const std::string kCommonTail =
      "    #10 d = 8'hA5;\n"
      "  end\n"
      "endmodule\n";
  SimFixture f_bare;
  auto bare =
      RunVcd(f_bare, kCommonHead + "    #10 $dumpportsoff;\n" + kCommonTail);
  SimFixture f_paren;
  auto paren =
      RunVcd(f_paren, kCommonHead + "    #10 $dumpportsoff();\n" + kCommonTail);
  EXPECT_FALSE(f_bare.diag.HasErrors());
  EXPECT_FALSE(f_paren.diag.HasErrors());
  EXPECT_NE(bare.find("$dumpoff"), std::string::npos);
  EXPECT_NE(paren.find("$dumpoff"), std::string::npos);
  EXPECT_EQ(tail(bare), tail(paren));
}

TEST_F(ExtendedVcdGeneralRules, BareOnRunsDefaultResume) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff(\"p.dump\");\n"
                        "    #10 $dumpportson;\n"
                        "    #10 d = 8'hA5;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  auto on = content.find("$dumpon");
  ASSERT_NE(on, std::string::npos);
  EXPECT_NE(content.find("b10100101 ", on), std::string::npos);
}

TEST_F(ExtendedVcdGeneralRules, EmptyParenAllRunsDefaultCheckpoint) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'hA5;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsall();\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  auto pos = content.find("$dumpall");
  ASSERT_NE(pos, std::string::npos);
  auto end = content.find("$end", pos);
  ASSERT_NE(end, std::string::npos);
  EXPECT_NE(content.substr(pos, end - pos).find("b10100101 "),
            std::string::npos);
}

TEST_F(ExtendedVcdGeneralRules, BareFlushRunsDefaultAction) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  logic [7:0] d;\n"
         "  integer rfd;\n"
         "  integer rch;\n"
         "  initial begin\n"
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

TEST_F(ExtendedVcdGeneralRules, EmptyParenFlushRunsDefaultAction) {
  SimFixture f;
  RunVcd(f,
         "module t;\n"
         "  logic [7:0] d;\n"
         "  integer rfd;\n"
         "  integer rch;\n"
         "  initial begin\n"
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

TEST_F(ExtendedVcdGeneralRules, BareDefaultActionFromTaskBody) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  task do_ckpt;\n"
                        "    $dumpportsall;\n"
                        "  endtask\n"
                        "  initial begin\n"
                        "    d = 8'hA5;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 do_ckpt;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  auto pos = content.find("$dumpall");
  ASSERT_NE(pos, std::string::npos);
  auto end = content.find("$end", pos);
  ASSERT_NE(end, std::string::npos);
  EXPECT_NE(content.substr(pos, end - pos).find("b10100101 "),
            std::string::npos);
}

TEST_F(ExtendedVcdGeneralRules, EmptyParenDefaultActionFromAlwaysProcess) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic clk;\n"
                        "  logic [7:0] d;\n"
                        "  always @(posedge clk) $dumpportson();\n"
                        "  initial begin\n"
                        "    clk = 1'b0;\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    #10 $dumpportsoff(\"p.dump\");\n"
                        "    #10 clk = 1'b1;\n"
                        "    #10 d = 8'hA5;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_FALSE(f.diag.HasErrors());
  auto on = content.find("$dumpon");
  ASSERT_NE(on, std::string::npos);
  EXPECT_NE(content.find("b10100101 ", on), std::string::npos);
}

TEST_F(ExtendedVcdGeneralRules, BareLimitGetsNoDefaultAction) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    $dumpportslimit;\n"
                        "    repeat (40) #10 d = d + 1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$dumpportslimit requires a filesize argument", 6,
                            "21.7.3.4"));
  EXPECT_EQ(content.find("$comment"), std::string::npos);
  EXPECT_NE(content.find("#400\n"), std::string::npos);
}

TEST_F(ExtendedVcdGeneralRules, EmptyParenLimitGetsNoDefaultAction) {
  SimFixture f;
  auto content = RunVcd(f,
                        "module t;\n"
                        "  logic [7:0] d;\n"
                        "  initial begin\n"
                        "    d = 8'h00;\n"
                        "    $dumpports(, \"p.dump\");\n"
                        "    $dumpportslimit();\n"
                        "    repeat (40) #10 d = d + 1;\n"
                        "  end\n"
                        "endmodule\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "$dumpportslimit requires a filesize argument", 6,
                            "21.7.3.4"));
  EXPECT_EQ(content.find("$comment"), std::string::npos);
  EXPECT_NE(content.find("#400\n"), std::string::npos);
}

}  // namespace
}  // namespace delta
