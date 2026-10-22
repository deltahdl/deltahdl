#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// Syntax 20-3 (§20.4.1) takes as the argument of $timeunit and $timeprecision
// a hierarchical identifier naming a design element, and §3.2 counts a package
// among those, so `p` names the package rather than a value to resolve.
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

// A top-level module is instantiated under its own name (§23.3.1), and §23.8
// lets a hierarchical name start at a top-level instance, so `dut` names the
// instance the calls stand in.
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

// The argument still has to reach a design element: a name that reaches none
// heads a hierarchical name §23.8 cannot resolve, and is reported once, as
// that and not as a value read.
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
