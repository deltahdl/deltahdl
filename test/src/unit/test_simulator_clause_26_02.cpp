#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(PackageDeclarationSim, VariableInitOccursBeforeInitialProcedure) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package pkg;\n"
      "  int x = 42;\n"
      "endpackage\n"
      "module top;\n"
      "  import pkg::*;\n"
      "  int observed;\n"
      "  initial observed = x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* observed = f.ctx.FindVariable("top.observed");
  ASSERT_NE(observed, nullptr);
  EXPECT_EQ(observed->value.ToUint64(), 42u);
}

TEST(PackageDeclarationSim, MultiplePackageVariablesInitBeforeProcedures) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package pkg;\n"
      "  int a = 5;\n"
      "  int b = 7;\n"
      "endpackage\n"
      "module top;\n"
      "  import pkg::*;\n"
      "  int sum;\n"
      "  initial sum = a + b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* sum = f.ctx.FindVariable("top.sum");
  ASSERT_NE(sum, nullptr);
  EXPECT_EQ(sum->value.ToUint64(), 12u);
}

}  // namespace
