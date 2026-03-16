#include "fixture_elaborator.h"

namespace {

TEST(CheckerProcedures, InitialWithVariableAssignment) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "checker chk;\n"
      "  logic flag;\n"
      "  initial flag = 0;\n"
      "endchecker\n",
      f, "chk");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
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
      "checker chk;\n"
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
      "  logic flag;\n"
      "  initial flag = 0;\n"
      "  always @(flag) flag <= ~flag;\n"
      "  final $display(\"done\");\n"
      "endchecker\n",
      f, "chk");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
