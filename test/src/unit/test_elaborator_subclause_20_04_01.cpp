#include <gtest/gtest.h>

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

}  // namespace
