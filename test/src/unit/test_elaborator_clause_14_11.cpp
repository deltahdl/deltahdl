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

// §14.11: a cycle delay is not legal as an intra-assignment delay on a blocking
// assignment. A default clocking is present so the missing-default-clocking
// rule stays silent; the only remaining violation is the intra-assignment ##.
TEST(CycleDelayElab, IntraAssignBlockingCycleDelayErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  default clocking cb @(posedge clk);\n"
      "    output data;\n"
      "  endclocking\n"
      "  initial begin\n"
      "    a = ##3 b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// §14.11: the same prohibition applies to a nonblocking assignment carrying a
// cycle-delay intra-assignment timing control.
TEST(CycleDelayElab, IntraAssignNonblockingCycleDelayErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  default clocking cb @(posedge clk);\n"
      "    output data;\n"
      "  endclocking\n"
      "  initial begin\n"
      "    a <= ##3 b;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// §14.11: the intra-assignment cycle-delay prohibition applies wherever the
// offending assignment sits, not only at the top of a process body. The
// validator descends into nested control flow, so an intra-assignment ## buried
// inside a branch is still rejected even when a default clocking is present.
TEST(CycleDelayElab, NestedIntraAssignCycleDelayErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  default clocking cb @(posedge clk);\n"
      "    output data;\n"
      "  endclocking\n"
      "  initial begin\n"
      "    if (1) begin\n"
      "      a <= ##2 b;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// §14.11/§14.16: the prohibition targets plain assignments, not synchronous
// drives. A clocking-block variable driven through a member access with a cycle
// delay is a legal synchronous drive and must not be flagged.
TEST(CycleDelayElab, SynchronousDriveWithCycleDelayNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  default clocking cb @(posedge clk);\n"
      "    output data;\n"
      "  endclocking\n"
      "  initial begin\n"
      "    cb.data <= ##1 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
