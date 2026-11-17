#include <gtest/gtest.h>

#include <cstdio>
#include <iostream>
#include <sstream>
#include <string>

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_simulator.h"
#include "helpers_preprocess_and_get.h"
#include "helpers_reported_error.h"
#include "helpers_temp_file.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

namespace {

RtlirDesign* PreprocElaborate(const std::string& src, SimFixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Preprocessor preproc(f.mgr, f.diag, {});
  auto pp = preproc.Preprocess(fid);
  auto pp_fid = f.mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(f.mgr.FileContent(pp_fid), pp_fid, f.diag,
              TextOrigin::kPreprocessorOutput);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  cu->has_preproc_global_precision = preproc.HasGlobalPrecision();
  cu->preproc_global_precision = preproc.GlobalPrecision();
  Elaborator elab(f.arena, f.diag, cu);
  auto* design = elab.Elaborate(cu->modules.back()->name);
  f.has_errors = f.diag.HasErrors();
  return design;
}

TEST(TimeformatSysTask, InstalledFormatAppliesToPercentT) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial begin\n"
      "    $timeformat(-9, 2, \" ns\", 10);\n"
      "    $display(\"%t\", 5);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "   5.00 ns\n");
}

TEST(TimeformatSysTask, DefaultFormatPadsToTwentyColumns) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $display(\"[%t]\", 3);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[" + std::string(19, ' ') + "3]\n");
}

TEST(TimeformatSysTask, FormatPersistsAcrossDisplays) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial begin\n"
      "    $timeformat(-9, 1, \"ns\", 0);\n"
      "    $display(\"%t\", 4);\n"
      "    $display(\"%t\", 6);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4.0ns\n6.0ns\n");
}

TEST(TimeformatSysTask, ReinvocationReplacesFormat) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial begin\n"
      "    $timeformat(-9, 1, \"ns\", 0);\n"
      "    $display(\"%t\", 4);\n"
      "    $timeformat(-12, 2, \"ps\", 0);\n"
      "    $display(\"%t\", 8);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "4.0ns\n8000.00ps\n");
}

TEST(TimeformatSysTask, DefaultUnitsFollowSmallestTimescalePrecision) {
  SimFixture f;
  auto* design = PreprocElaborate(
      "`timescale 10ns / 1ps\n"
      "module t;\n"
      "  wire w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.GetTimeFormat().units_number, -12);
}

TEST(TimeformatSysTask, UnitsAboveRangeRejected) {
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  initial $timeformat(3, 0, \"\", 20);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "units_number out of range",
                            2, "20.4.3"));
}

TEST(TimeformatSysTask, UnitsBelowRangeRejected) {
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  initial $timeformat(-16, 0, \"\", 20);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "units_number out of range",
                            2, "20.4.3"));
}

TEST(TimeformatSysTask, PrecisionBelowRangeRejected) {
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  initial $timeformat(-9, -16, \"\", 20);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "precision_number out of range", 2, "20.4.3"));
}

TEST(TimeformatSysTask, PrecisionAboveRangeRejected) {
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  initial $timeformat(-9, 3, \"\", 20);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "precision_number out of range", 2, "20.4.3"));
}

TEST(TimeformatSysTask, RangeEndpointsAccepted) {
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  initial $timeformat(2, -15, \"\", 0);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(TimeformatSysTask, OutOfRangeLeavesPriorFormatIntact) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial begin\n"
      "    $timeformat(-9, 2, \"ns\", 0);\n"
      "    $timeformat(5, 0, \"XX\", 0);\n"
      "    $display(\"%t\", 7);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "units_number out of range",
                            4, "20.4.3"));
  EXPECT_NE(out.find("7.00ns"), std::string::npos);
  EXPECT_EQ(out.find("XX"), std::string::npos);
}

TEST(TimeformatSysTask, DISABLED_ABareCallRestoresTheDefaults) {
  SimFixture f;
  EXPECT_EQ(PreprocessAndCapture("`timescale 1ns / 1ps\n"
                                 "module t;\n"
                                 "  initial begin\n"
                                 "    $timeformat(-9, 2, \"ns\", 0);\n"
                                 "    $display(\"[%t]\", 3ns);\n"
                                 "    $timeformat;\n"
                                 "    $display(\"[%t]\", 3ns);\n"
                                 "  end\n"
                                 "endmodule\n",
                                 f),
            "[3.00ns]\n[" + std::string(16, ' ') + "3000]\n");
}

TEST(TimeformatSysTask, FileOutputTaskAppliesFormat) {
  SimFixture f;
  const std::string kPath = "/tmp/deltahdl_tf_20_04_03_file.txt";
  std::remove(kPath.c_str());
  RunCapture(
      "module t;\n"
      "  integer fd;\n"
      "  initial begin\n"
      "    $timeformat(-9, 2, \" ns\", 0);\n"
      "    fd = $fopen(\"" +
          kPath +
          "\", \"w\");\n"
          "    $fdisplay(fd, \"%t\", 5);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(SlurpFile(kPath), "5.00 ns\n");
  std::remove(kPath.c_str());
}

TEST(TimeformatSysTask, FormattedStringFunctionAppliesFormat) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial begin\n"
      "    $timeformat(-9, 2, \"ns\", 0);\n"
      "    $display(\"%s\", $sformatf(\"%t\", 6));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("6.00ns"), std::string::npos);
}

TEST(TimeformatSysTask, OutOfRangeArgumentNames20_4_3) {
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  initial $timeformat(4, 0, \"\", 20);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "out of range [2 .. -15]", 2,
                            "20.4.3"));
}

std::string PreprocRunCapture(const std::string& src, SimFixture& f) {
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  auto* design = PreprocElaborate(src, f);
  if (design != nullptr) LowerAndRun(design, f);
  std::cout.rdbuf(old_buf);
  return captured.str();
}

TEST(TimeformatSysTask, PercentTConvertsToTheUnitsNumber) {
  SimFixture f;
  EXPECT_EQ(PreprocRunCapture("`timescale 1ns/1ps\n"
                              "module t;\n"
                              "  initial begin\n"
                              "    $timeformat(-6, 1, \"us\", 0);\n"
                              "    #7000 $display(\"[%t]\", $time);\n"
                              "  end\n"
                              "endmodule\n",
                              f),
            "[7.0us]\n");
}

TEST(TimeformatSysTask, PercentTDefaultsToTheGlobalPrecision) {
  SimFixture f;
  EXPECT_EQ(PreprocRunCapture("`timescale 1ns/1ps\n"
                              "module t;\n"
                              "  initial #5 $display(\"[%t]\", $time);\n"
                              "endmodule\n",
                              f),
            "[" + std::string(16, ' ') + "5000]\n");
}

TEST(TimeformatSysTask, PercentTFormatsARealTimeByItsValue) {
  SimFixture f;
  EXPECT_EQ(PreprocRunCapture("`timescale 1ns/1ps\n"
                              "module t;\n"
                              "  real r = 2.5;\n"
                              "  initial begin\n"
                              "    $timeformat(-9, 2, \" ns\", 10);\n"
                              "    #5 $display(\"[%t]\", $realtime);\n"
                              "    $timeformat(-12, 1, \" ps\", 0);\n"
                              "    $display(\"[%t]\", r);\n"
                              "  end\n"
                              "endmodule\n",
                              f),
            "[   5.00 ns]\n[2500.0 ps]\n");
}

TEST(TimeformatSysTask, DISABLED_TheFinestDirectivePrecisionIsTheDefaultUnits) {
  SimFixture f;
  EXPECT_EQ(PreprocessAndCapture("`timescale 1ns / 1ps\n"
                                 "module a;\n"
                                 "endmodule\n"
                                 "`timescale 1ns / 10fs\n"
                                 "module t;\n"
                                 "  a u();\n"
                                 "  initial $display(\"[%t]\", 1ns);\n"
                                 "endmodule\n",
                                 f),
            "[" + std::string(14, ' ') + "100000]\n");
}

TEST(TimeformatSysTask,
     DISABLED_ATimeprecisionDeclarationLeavesTheDefaultUnits) {
  SimFixture f;
  EXPECT_EQ(PreprocessAndCapture("`timescale 1ns / 1ps\n"
                                 "module t;\n"
                                 "  timeprecision 1fs;\n"
                                 "  initial $display(\"[%t]\", 1ns);\n"
                                 "endmodule\n",
                                 f),
            "[" + std::string(16, ' ') + "1000]\n");
}

TEST(TimeformatSysTask, TheFinestUnitsNumberIsAccepted) {
  SimFixture f;
  EXPECT_EQ(PreprocessAndCapture("`timescale 1ns / 1fs\n"
                                 "module t;\n"
                                 "  initial begin\n"
                                 "    $timeformat(-15, 2, \"\", 0);\n"
                                 "    $display(\"[%t]\", 1ns);\n"
                                 "  end\n"
                                 "endmodule\n",
                                 f),
            "[1000000.00]\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(TimeformatSysTask, DISABLED_ANonIntegerUnitsOrPrecisionNumberIsRejected) {
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  initial begin\n"
      "    $timeformat(-9.5, 2, \"ns\", 5);\n"
      "    $timeformat(-9, 1.5, \"ns\", 5);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "units_number is not an integer", 3, "20.4.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "precision_number is not an integer", 4, "20.4.3"));
}

TEST(TimeformatSysTask, AValueWiderThanTheFieldIsPrintedWhole) {
  SimFixture f;
  EXPECT_EQ(PreprocessAndCapture("`timescale 1ns / 1ps\n"
                                 "module t;\n"
                                 "  initial begin\n"
                                 "    $timeformat(-9, 2, \" ns\", 10);\n"
                                 "    $display(\"[%t]\", 123456789ns);\n"
                                 "  end\n"
                                 "endmodule\n",
                                 f),
            "[123456789.00 ns]\n");
}

TEST(TimeformatSysTask, ExtraFractionalDigitsAreRounded) {
  SimFixture f;
  EXPECT_EQ(
      PreprocessAndCapture("`timescale 1ns / 1ps\n"
                           "module t;\n"
                           "  initial begin\n"
                           "    $timeformat(-6, 1, \"\", 0);\n"
                           "    $display(\"[%t] [%t]\", 1260ns, 1240ns);\n"
                           "  end\n"
                           "endmodule\n",
                           f),
      "[1.3] [1.2]\n");
}

TEST(TimeformatSysTask, ACallInOneModuleGovernsModulesOfOtherUnits) {
  SimFixture f;
  EXPECT_EQ(PreprocessAndCaptureAllTops(
                "`timescale 1ms / 1ns\n"
                "module cntrl;\n"
                "  initial $timeformat(-9, 2, \" ns\", 10);\n"
                "endmodule\n"
                "`timescale 1fs / 1fs\n"
                "module a1_dat;\n"
                "  initial #10000000 $display(\"%m: %t\", $realtime);\n"
                "endmodule\n"
                "`timescale 1ps / 1ps\n"
                "module a2_dat;\n"
                "  initial #20000 $display(\"%m: %t\", $realtime);\n"
                "endmodule\n",
                f),
            "a1_dat:   10.00 ns\na2_dat:   20.00 ns\n");
}

TEST(TimeformatSysTask, ACallFromAStaticClassMethodGovernsPercentT) {
  SimFixture f;
  EXPECT_EQ(PreprocessAndCapture("`timescale 1ns / 1ps\n"
                                 "class C;\n"
                                 "  static function void f();\n"
                                 "    $timeformat(-9, 2, \"ns\", 8);\n"
                                 "  endfunction\n"
                                 "endclass\n"
                                 "module t;\n"
                                 "  initial begin\n"
                                 "    C::f();\n"
                                 "    $display(\"[%t]\", 2ns);\n"
                                 "  end\n"
                                 "endmodule\n",
                                 f),
            "[  2.00ns]\n");
}

TEST(TimeformatSysTask, WriteStrobeMonitorAndStringTasksApplyTheFormat) {
  SimFixture f;
  EXPECT_EQ(PreprocessAndCapture("`timescale 1ns / 1ps\n"
                                 "module t;\n"
                                 "  string s;\n"
                                 "  initial begin\n"
                                 "    $timeformat(-9, 1, \"n\", 6);\n"
                                 "    $write(\"w[%t]\\n\", 2ns);\n"
                                 "    $strobe(\"s[%t]\", 3ns);\n"
                                 "    $sformat(s, \"f[%t]\", 4ns);\n"
                                 "    $display(s);\n"
                                 "    $swrite(s, \"r[%t]\", 5ns);\n"
                                 "    $display(s);\n"
                                 "    #1 $monitor(\"m[%t]\", $realtime);\n"
                                 "  end\n"
                                 "endmodule\n",
                                 f),
            "w[  2.0n]\nf[  4.0n]\nr[  5.0n]\ns[  3.0n]\nm[  1.0n]\n");
}

TEST(TimeformatSysTask, FileWriteStrobeAndMonitorApplyTheFormat) {
  SimFixture f;
  const std::string kPath = "/tmp/deltahdl_tf_20_04_03_tasks.txt";
  std::remove(kPath.c_str());
  PreprocessAndCapture(
      "`timescale 1ns / 1ps\n"
      "module t;\n"
      "  integer fd;\n"
      "  initial begin\n"
      "    $timeformat(-9, 1, \"n\", 6);\n"
      "    fd = $fopen(\"" +
          kPath +
          "\", \"w\");\n"
          "    $fwrite(fd, \"w[%t]\\n\", 6ns);\n"
          "    $fstrobe(fd, \"s[%t]\", 7ns);\n"
          "    #1 $fmonitor(fd, \"m[%t]\", $realtime);\n"
          "    #1 $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(SlurpFile(kPath), "w[  6.0n]\ns[  7.0n]\nm[  1.0n]\n");
  std::remove(kPath.c_str());
}

}  // namespace
