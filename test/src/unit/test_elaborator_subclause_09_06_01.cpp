

#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(WaitForkElaboration, WaitForkStandaloneElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    wait fork;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §9.6.1 states only that "The wait fork statement blocks process execution
// flow until all immediate child subprocesses ... have terminated", which makes
// it a timing control and states no prohibition of its own. The rule broken
// here is §9.2.2.2.2's, that an always_comb shall not contain timing controls,
// and the report names that subclause.
TEST(WaitForkInAlwaysComb, WaitForkInAlwaysCombErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a;\n"
      "  always_comb begin\n"
      "    wait fork;\n"
      "    a = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  const delta::Diagnostic* diag =
      FindDiag(f, "always_comb shall not contain timing controls");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "9.2.2.2.2");
}

}  // namespace
