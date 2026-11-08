#include <gtest/gtest.h>

#include <cctype>
#include <cstddef>
#include <string>
#include <vector>

#include "fixture_vcd_dump_from_source.h"
#include "fixture_vcd_dump_run.h"
#include "helpers_text_lines.h"
#include "helpers_vcd_var_decl.h"
#include "simulator/vcd_writer.h"

namespace delta {
namespace {

class VcdcloseKeyword : public VcdDumpRunTestBase {
 protected:
  std::string RunVcd(const std::string& src, bool close_file = true) {
    return RunVcdDump(src, {.scope = "t", .close_file = close_file});
  }
};
TEST_F(VcdcloseKeyword, ClosedFileEndsWithKeywordTimeEnd) {
  auto toks =
      Tokens(RunVcd("module t;\n"
                    "  logic a;\n"
                    "  initial begin\n"
                    "    a = 1'b0;\n"
                    "    $dumpports(, \"dump2.dump\");\n"
                    "    #10 a = 1'b1;\n"
                    "  end\n"
                    "endmodule\n"));
  ASSERT_GE(toks.size(), 3u);
  EXPECT_EQ(toks[toks.size() - 3], "$vcdclose");
  EXPECT_EQ(toks[toks.size() - 1], "$end");
  const std::string& time_tok = toks[toks.size() - 2];
  ASSERT_GE(time_tok.size(), 2u);
  EXPECT_EQ(time_tok[0], '#');
  for (size_t i = 1; i < time_tok.size(); ++i) {
    EXPECT_TRUE(std::isdigit(static_cast<unsigned char>(time_tok[i])))
        << "non-decimal digit in final_simulation_time: " << time_tok;
  }
  EXPECT_EQ(time_tok, "#10");
  EXPECT_EQ(CountToken(toks, "$vcdclose"), 1u);
}

TEST_F(VcdcloseKeyword, RecordsEndTimeBeyondLastValueChange) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    #10 a = 1'b1;\n"
      "    #5 a = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("$vcdclose #15 $end"), std::string::npos);
  EXPECT_EQ(content.find("$vcdclose #10"), std::string::npos);
}

TEST_F(VcdcloseKeyword, ZeroTimeRunClosesWithZero) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("$vcdclose #0 $end"), std::string::npos);
}

TEST_F(VcdcloseKeyword, DefaultNamedDumpAlsoCloses) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    $dumpports;\n"
      "    #10 a = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("$vcdclose #10 $end"), std::string::npos);
}

TEST_F(VcdcloseKeyword, StringVariableFilenameFormAlsoCloses) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  string fn = \"dump2.dump\";\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    $dumpports(, fn);\n"
      "    #10 a = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("$vcdclose #10 $end"), std::string::npos);
}

TEST_F(VcdcloseKeyword, IntegralVariableFilenameFormAlsoCloses) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  int fn;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    fn = \"du2\";\n"
      "    $dumpports(, fn);\n"
      "    #10 a = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("$vcdclose #10 $end"), std::string::npos);
}

TEST_F(VcdcloseKeyword, ProceduralStringFilenameFormAlsoCloses) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  string fn;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    fn = \"dump2.dump\";\n"
      "    $dumpports(, fn);\n"
      "    #10 a = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("$vcdclose #10 $end"), std::string::npos);
}

TEST_F(VcdcloseKeyword, DeclInitIntegralFilenameFormAlsoCloses) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  int fn = \"du2\";\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    $dumpports(, fn);\n"
      "    #10 a = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("$vcdclose #10 $end"), std::string::npos);
}

TEST_F(VcdcloseKeyword, ParameterFilenameFormAlsoCloses) {
  auto content = RunVcd(
      "module t;\n"
      "  parameter FN = \"du2\";\n"
      "  logic a;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    $dumpports(, FN);\n"
      "    #10 a = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("$vcdclose #10 $end"), std::string::npos);
}

TEST_F(VcdcloseKeyword, DumpportsFromAlwaysStillCloses) {
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
  EXPECT_NE(content.find("$vcdclose #15 $end"), std::string::npos);
}

TEST_F(VcdcloseKeyword, TaskBodyDumpportsStillCloses) {
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
  EXPECT_NE(content.find("$vcdclose #10 $end"), std::string::npos);
}

TEST_F(VcdcloseKeyword, ExampleScaleEndTimeRendersDecimal) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    #13000 a = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_NE(content.find("$vcdclose #13000 $end"), std::string::npos);
}

TEST_F(VcdcloseKeyword, MultipleDumpportsCallsStillCloseOnce) {
  auto toks =
      Tokens(RunVcd("module t;\n"
                    "  logic a;\n"
                    "  localparam FN = \"dux\";\n"
                    "  initial begin\n"
                    "    a = 1'b0;\n"
                    "    $dumpports(, \"dump2.dump\");\n"
                    "    $dumpports(, FN);\n"
                    "    #10 a = 1'b1;\n"
                    "  end\n"
                    "endmodule\n"));
  EXPECT_EQ(CountToken(toks, "$vcdclose"), 1u);
  ASSERT_GE(toks.size(), 3u);
  EXPECT_EQ(toks[toks.size() - 3], "$vcdclose");
  EXPECT_EQ(toks[toks.size() - 2], "#10");
  EXPECT_EQ(toks[toks.size() - 1], "$end");
}

TEST_F(VcdcloseKeyword, FourStateDumpNeverGainsVcdclose) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    $dumpfile(\"dump1.dump\");\n"
      "    $dumpvars;\n"
      "    #10 a = 1'b1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(content.find("#10"), std::string::npos);
  EXPECT_EQ(content.find("$vcdclose"), std::string::npos);
}

TEST_F(VcdcloseKeyword, NoKeywordWithoutCloseStep) {
  auto content = RunVcd(
      "module t;\n"
      "  logic a;\n"
      "  initial begin\n"
      "    a = 1'b0;\n"
      "    $dumpports(, \"dump2.dump\");\n"
      "    #10 a = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      false);
  ASSERT_NE(content.find("#10"), std::string::npos);
  EXPECT_EQ(content.find("$vcdclose"), std::string::npos);
}

TEST_F(VcdcloseKeyword, WithoutOpenFileIsHarmless) {
  VcdWriter vcd(tmp_path_ + "/cannot_open.vcd");
  ASSERT_FALSE(vcd.IsOpen());
  vcd.SetExtended();
  vcd.WriteVcdClose(13000);
  EXPECT_FALSE(vcd.IsOpen());
}

class VcdcloseFromSource : public VcdDumpFromSourceTestBase {
 protected:
  static std::string DesignCalling(const std::string& open_task,
                                   const std::string& close_task) {
    return "module t;\n"
           "  logic a;\n"
           "  initial begin\n"
           "    a = 1'b0;\n" +
           open_task + "    #10 a = 1'b1;\n" + close_task +
           "    #5 a = 1'b0;\n"
           "  end\n"
           "endmodule\n";
  }
};

TEST_F(VcdcloseFromSource, SourceCallTerminatesTheExtendedFileAtItsOwnTime) {
  RunSource(DesignCalling("    $dumpports(, \"portdump.vcd\");\n",
                          "    $vcdclose;\n"),
            false);

  auto content = DumpFile("portdump.vcd");
  EXPECT_TRUE(HasLine(Lines(content), "$dumpports"));
  auto toks = Tokens(content);
  ASSERT_GE(toks.size(), 3u);
  EXPECT_EQ(toks[toks.size() - 3], "$vcdclose");
  EXPECT_EQ(toks[toks.size() - 2], "#10");
  EXPECT_EQ(toks[toks.size() - 1], "$end");
  EXPECT_EQ(CountToken(toks, "$vcdclose"), 1u);
}

TEST_F(VcdcloseFromSource, ExtendedDumpWithoutTheCallIsNotTerminated) {
  RunSource(DesignCalling("    $dumpports(, \"portdump.vcd\");\n", ""), false);

  auto content = DumpFile("portdump.vcd");
  ASSERT_NE(content.find("$var port"), std::string::npos);
  ASSERT_TRUE(HasLine(Lines(content), "#15"));
  EXPECT_EQ(content.find("$vcdclose"), std::string::npos);
}

TEST_F(VcdcloseFromSource, FourStateDumpIgnoresTheSourceCall) {
  RunSource(DesignCalling("    $dumpfile(\"vardump.vcd\");\n    $dumpvars;\n",
                          "    $vcdclose;\n"),
            false);

  auto content = DumpFile("vardump.vcd");
  ASSERT_NE(content.find("$var reg"), std::string::npos);
  EXPECT_EQ(content.find("$vcdclose"), std::string::npos);
  EXPECT_TRUE(HasLine(Lines(content), "#15"));
}

class VcdcloseClosingUnit : public VcdcloseFromSource {
 protected:
  std::string UnitBeforeClose(const std::string& close_task,
                              const std::string& time_line) {
    RunSource(
        DesignCalling("    $dumpports(, \"portdump.vcd\");\n", close_task),
        false);
    std::string content = DumpFile("portdump.vcd");
    whole_ = content;
    code_ = "";
    found_ = false;
    auto decl = VarDecl(content, "a");
    if (decl.size() != 6) return "";
    code_ = decl[3];
    size_t close_at = content.find("$vcdclose");
    if (close_at == std::string::npos) return "";
    size_t unit_at = content.rfind(time_line, close_at);
    if (unit_at == std::string::npos) return "";
    found_ = true;
    return content.substr(unit_at, close_at - unit_at);
  }

  bool found_ = false;
  std::string code_;
  std::string whole_;
};

TEST_F(VcdcloseClosingUnit,
       ChangeInTheClosingTimeUnitIsRecordedBeforeTheClose) {
  std::string unit = UnitBeforeClose("    $vcdclose;\n", "\n#10\n");
  ASSERT_TRUE(found_) << whole_;
  EXPECT_NE(unit.find(code_), std::string::npos) << whole_;
}

TEST_F(VcdcloseClosingUnit, ChangeBeforeTheClosingTimeUnitIsStillRecorded) {
  std::string unit = UnitBeforeClose("    #1 $vcdclose;\n", "\n#10\n");
  ASSERT_TRUE(found_) << whole_;
  EXPECT_NE(unit.find(code_), std::string::npos) << whole_;
}

TEST_F(VcdcloseClosingUnit, ClosingUnitWithNoChangeListsNoValueChange) {
  std::string unit = UnitBeforeClose("    #1 $vcdclose;\n", "\n#11\n");
  ASSERT_TRUE(found_) << whole_;
  EXPECT_EQ(unit.find(code_), std::string::npos) << whole_;
}

}  // namespace
}  // namespace delta
