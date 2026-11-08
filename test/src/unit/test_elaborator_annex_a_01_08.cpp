#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

namespace {

TEST(CheckerProcedures, InitialProcedureBesideAnInitializedVariable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "checker chk;\n"
      "  logic flag = 0;\n"
      "  initial a0: assert (1);\n"
      "endchecker\n",
      f, "chk");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CheckerProcedures, CheckerVariableAssignedInInitialIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "checker chk;\n"
      "  logic flag;\n"
      "  initial flag = 0;\n"
      "endchecker\n",
      f, "chk");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "checker variable 'flag' cannot be assigned in an "
                            "initial procedure",
                            3, "17.7.1"));
}

TEST(CheckerProcedures, CheckerWithPortsElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "checker chk(input logic clk, output bit ok);\n"
      "  logic sig;\n"
      "  assign ok = sig;\n"
      "endchecker\n",
      f, "chk");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CheckerProcedures, CheckerWithAssertionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "checker chk(input logic clk, input logic a, input logic b);\n"
      "  assert property (@(posedge clk) a |-> b);\n"
      "endchecker\n",
      f, "chk");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CheckerProcedures, CheckerWithMultipleItemsElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "checker chk;\n"
      "  logic flag = 0;\n"
      "  initial a0: assert (1);\n"
      "  always_ff @(posedge flag) flag <= ~flag;\n"
      "  final $display(\"done\");\n"
      "endchecker\n",
      f, "chk");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CheckerOrGenerateItem, AUdpInstanceIsNoCheckerItem) {
  ElabFixture f;
  ElaborateSrc(
      "checker c(logic a, logic z);\n"
      "  inv u(z, a);\n"
      "endchecker\n"
      "primitive inv(output o, input i);\n"
      "  table 0 : 1; 1 : 0; endtable\n"
      "endprimitive\n"
      "module top; logic x, y; c k(x, y); endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "primitive cannot be instantiated inside checker "
                            "'c'",
                            2, "A.1.8"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "primitive cannot be instantiated inside checker "
                             "'c'",
                             2, "24.3"));
}

}  // namespace
