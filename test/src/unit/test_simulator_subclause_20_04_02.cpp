#include <gtest/gtest.h>

#include <cstddef>
#include <string>

#include "fixture_simulator.h"
#include "helpers_preprocess_and_get.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(PrinttimescaleSysTask, NoArgumentDescribesCurrentScope) {
  SimFixture f;
  std::string out = RunCapture(
      "module a_dat;\n"
      "  timeunit 1ms / 1us;\n"
      "  initial $printtimescale;\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "Time scale of (a_dat) is 1ms / 1us\n");
}

TEST(PrinttimescaleSysTask, NamedElementArgumentDescribesThatElement) {
  SimFixture f;
  std::string out = RunCapture(
      "module child;\n"
      "  timeunit 100ps / 10fs;\n"
      "endmodule\n"
      "module top;\n"
      "  timeunit 1ns / 1ns;\n"
      "  child c1();\n"
      "  initial $printtimescale(c1);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "Time scale of (c1) is 100ps / 10fs\n");
}

TEST(PrinttimescaleSysTask, UnitArgumentDescribesCompilationUnit) {
  SimFixture f;
  std::string out = RunCapture(
      "timeunit 1s / 1ms;\n"
      "module top;\n"
      "  timeunit 1ns / 1ns;\n"
      "  initial $printtimescale($unit);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "Time scale of ($unit) is 1s / 1ms\n");
}

TEST(PrinttimescaleSysTask, RootArgumentDescribesSimulationTimeUnit) {
  SimFixture f;
  std::string out = RunCapture(
      "module top;\n"
      "  timeunit 1ns / 1fs;\n"
      "  initial $printtimescale($root);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "Time scale of ($root) is 1fs / 1fs\n");
}

TEST(PrinttimescaleSysTask, ReportFollowsRequiredFormat) {
  SimFixture f;
  std::string out = RunCapture(
      "module dut;\n"
      "  timeunit 100us / 10ns;\n"
      "  initial $printtimescale;\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "Time scale of (dut) is 100us / 10ns\n");
}

TEST(PrinttimescaleSysTask, RendersWholeSecondUnits) {
  SimFixture f;
  std::string out = RunCapture(
      "module slow;\n"
      "  timeunit 100s / 10s;\n"
      "  initial $printtimescale;\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "Time scale of (slow) is 100s / 10s\n");
}

TEST(PrinttimescaleSysTask, DefaultCurrentScopeIsNanosecond) {
  SimFixture f;
  std::string out = RunCapture(
      "module top;\n"
      "  initial $printtimescale;\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "Time scale of (top) is 1ns / 1ns\n");
}

std::string RunSource(const std::string& src) {
  SimFixture f;
  return RunCapture(src, f);
}

TEST(PrinttimescaleSysTask, TheStandardsExampleDescribesEveryScale) {
  SimFixture f;
  EXPECT_EQ(PreprocessAndCaptureAllTops("timeunit 100ps / 10fs;\n"
                                        "module a_dat;\n"
                                        "  timeunit 1ms / 1us;\n"
                                        "  initial begin\n"
                                        "    $printtimescale($root);\n"
                                        "    $printtimescale($unit);\n"
                                        "    $printtimescale;\n"
                                        "    $printtimescale(b_dat.c1);\n"
                                        "  end\n"
                                        "endmodule\n"
                                        "`timescale 10 fs / 1 fs\n"
                                        "module b_dat;\n"
                                        "  c_dat c1 ();\n"
                                        "endmodule\n"
                                        "`timescale 1 ns / 1 ns\n"
                                        "module c_dat;\n"
                                        "endmodule\n",
                                        f),
            "Time scale of ($root) is 1fs / 1fs\n"
            "Time scale of ($unit) is 100ps / 10fs\n"
            "Time scale of (a_dat) is 1ms / 1us\n"
            "Time scale of (b_dat.c1) is 1ns / 1ns\n");
}

TEST(PrinttimescaleSysTask, TheTopModulesOwnNameDescribesTheTop) {
  EXPECT_EQ(RunSource("timeunit 1s / 1ms;\n"
                      "module child;\n"
                      "  timeunit 100ps / 10fs;\n"
                      "endmodule\n"
                      "module top;\n"
                      "  timeunit 10ns / 1ns;\n"
                      "  child c1();\n"
                      "  initial $printtimescale(top);\n"
                      "endmodule\n"),
            "Time scale of (top) is 10ns / 1ns\n");
}

constexpr const char* kInterfaceAndProgram =
    "interface i;\n"
    "  timeunit 10us;\n"
    "  timeprecision 1ns;\n"
    "  initial #1 $printtimescale;\n"
    "endinterface\n"
    "program p;\n"
    "  timeunit 100ms;\n"
    "  timeprecision 10us;\n"
    "  initial #2 $printtimescale;\n"
    "endprogram\n"
    "module top;\n"
    "  timeunit 1ns / 1ps;\n"
    "  i ui();\n"
    "  p up();\n"
    "  initial begin\n"
    "    $printtimescale(ui);\n"
    "    $printtimescale(up);\n"
    "  end\n"
    "endmodule\n";

std::size_t Occurrences(const std::string& text, const std::string& part) {
  std::size_t count = 0;
  for (auto at = text.find(part); at != std::string::npos;
       at = text.find(part, at + part.size())) {
    ++count;
  }
  return count;
}

TEST(PrinttimescaleSysTask, AnInterfaceOrProgramIsDescribedByItsOwnScale) {
  std::string out = RunSource(kInterfaceAndProgram);
  EXPECT_NE(out.find("Time scale of (ui) is 10us / 1ns\n"), std::string::npos)
      << out;
  EXPECT_NE(out.find("Time scale of (up) is 100ms / 10us\n"), std::string::npos)
      << out;
  EXPECT_EQ(Occurrences(out, ") is 10us / 1ns\n"), 2u) << out;
  EXPECT_EQ(Occurrences(out, ") is 100ms / 10us\n"), 2u) << out;
  EXPECT_EQ(Occurrences(out, "Time scale of ("), 4u) << out;
}

TEST(PrinttimescaleSysTask, DISABLED_APackageSubroutineDescribesThePackage) {
  EXPECT_EQ(RunSource("package pk;\n"
                      "  timeunit 10ms;\n"
                      "  timeprecision 100fs;\n"
                      "  task show();\n"
                      "    $printtimescale;\n"
                      "  endtask\n"
                      "  function void tell();\n"
                      "    $printtimescale;\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  timeunit 1ns / 1ps;\n"
                      "  initial begin\n"
                      "    pk::show();\n"
                      "    pk::tell();\n"
                      "  end\n"
                      "endmodule\n"),
            "Time scale of (pk) is 10ms / 100fs\n"
            "Time scale of (pk) is 10ms / 100fs\n");
}

TEST(PrinttimescaleSysTask, DISABLED_ANameResolvingToNothingIsReported) {
  SimFixture f;
  std::string out = RunCapture(
      "module c;\n"
      "  timeunit 1us / 1ns;\n"
      "endmodule\n"
      "module top;\n"
      "  timeunit 1ns / 1ns;\n"
      "  c c1();\n"
      "  initial begin\n"
      "    $printtimescale(nosuch);\n"
      "    $printtimescale(c1);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical name 'nosuch' resolves to no "
                            "declaration",
                            8, "23.8"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
  EXPECT_EQ(out.find("(nosuch)"), std::string::npos) << out;
}

}  // namespace
