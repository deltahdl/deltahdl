#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(TimescaleRetrievalElab, APackageArgumentNamesThePackage) {
  EXPECT_TRUE(
      ElabOk("package p; timeunit 1us / 1ns; endpackage\n"
             "module top;\n"
             "  timeunit 1ns / 1ps;\n"
             "  int u, r;\n"
             "  initial begin\n"
             "    u = $timeunit(p);\n"
             "    r = $timeprecision(p);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(TimescaleRetrievalElab, ATopModulesOwnNameNamesItsInstance) {
  EXPECT_TRUE(
      ElabOk("module dut;\n"
             "  timeunit 100us / 10ns;\n"
             "  int u, r;\n"
             "  initial begin\n"
             "    u = $timeunit(dut);\n"
             "    r = $timeprecision(dut);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(TimescaleRetrievalElab, AnArgumentNamingNothingIsReportedOnce) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int u;\n"
      "  initial u = $timeunit(nosuch);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical name 'nosuch' resolves to no "
                            "declaration",
                            3, "23.8"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

TEST(TimescaleRetrievalElab, DISABLED_AnArgumentBeyondTheSyntaxIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  timeunit 1ns / 1ns;\n"
      "  int a;\n"
      "  initial begin\n"
      "    a = $timeunit();\n"
      "    a = $timeprecision();\n"
      "    a = $timeunit(1 + 2);\n"
      "    a = $timeprecision(1 + 2);\n"
      "    a = $timeunit(top, top);\n"
      "    a = $timeprecision(top, top);\n"
      "  end\n"
      "endmodule\n",
      f);
  for (uint32_t line = 5; line <= 10; ++line) {
    const char* name = line % 2 == 1 ? "$timeunit" : "$timeprecision";
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        std::string(name) + " takes no argument or one hierarchical identifier",
        line, "20.4.1"))
        << name << " at line " << line;
  }
  EXPECT_EQ(f.diag.ErrorCount(), 6u);
}

TEST(TimescaleRetrievalElab, TheFormsTheSyntaxGivesAreAccepted) {
  EXPECT_TRUE(
      ElabOk("timeunit 100ps / 10fs;\n"
             "module c;\n"
             "  timeunit 1us / 1ns;\n"
             "endmodule\n"
             "module top;\n"
             "  timeunit 1ns / 1ns;\n"
             "  c c1();\n"
             "  int a;\n"
             "  initial begin\n"
             "    a = $timeunit;\n"
             "    a = $timeprecision;\n"
             "    a = $timeunit(top);\n"
             "    a = $timeprecision(top.c1);\n"
             "    a = $timeunit($unit);\n"
             "    a = $timeprecision($root);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(TimescaleRetrievalElab, APrecisionArgumentNamingNothingIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int r;\n"
      "  initial r = $timeprecision(nosuch);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "hierarchical name 'nosuch' resolves to no "
                            "declaration",
                            3, "23.8"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

}  // namespace
