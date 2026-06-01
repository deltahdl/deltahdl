#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(CycleDelayElab, WithoutDefaultClockingErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    ##5;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// §14.11: the missing-default-clocking diagnostic is conditional, not a blanket
// rejection of ##. When a default clocking block governs the current module the
// rule must stay silent, so the same cycle delay elaborates cleanly.
TEST(CycleDelayElab, WithDefaultClockingNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  default clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "  initial begin\n"
      "    ##5;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §14.11: the missing-default-clocking check applies to a cycle delay wherever
// it sits in a process body, not only at the top level. The validator descends
// into nested control flow, so a ## buried inside a branch is still rejected
// when no default clocking governs the module.
TEST(CycleDelayElab, NestedCycleDelayWithoutDefaultClockingErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    if (1) begin\n"
      "      ##5;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

}
