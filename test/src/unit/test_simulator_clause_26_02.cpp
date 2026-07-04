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
  auto* observed = f.ctx.FindVariable("observed");
  ASSERT_NE(observed, nullptr);
  EXPECT_EQ(observed->value.ToUint64(), 42u);
}

// §26.2 requires package variable-declaration assignments to complete before
// any initial OR always procedure starts. Here an always_comb procedure samples
// the imported package variable; its initializer must already have run, so the
// captured value is the initialized one.
TEST(PackageDeclarationSim, PackageVariableInitObservedByAlwaysProcedure) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package pkg;\n"
      "  int seed = 55;\n"
      "endpackage\n"
      "module top;\n"
      "  import pkg::*;\n"
      "  int captured;\n"
      "  always_comb captured = seed;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* captured = f.ctx.FindVariable("captured");
  ASSERT_NE(captured, nullptr);
  EXPECT_EQ(captured->value.ToUint64(), 55u);
}

}  // namespace
