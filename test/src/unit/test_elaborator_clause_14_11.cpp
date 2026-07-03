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

// §14.11 + §14.12: what constitutes a cycle is fixed by the default clocking in
// effect. §14.12 lets the default be established by a reference/assignment form
// -- `default clocking <name>;` naming an already-declared clocking block --
// rather than an inline default block. The missing-default-clocking rule must
// consume that reference form too and stay silent, since a default IS in
// effect.
TEST(CycleDelayElab, WithReferenceFormDefaultClockingNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "  default clocking cb;\n"
      "  initial begin\n"
      "    ##5;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §14.11: the missing-default-clocking requirement is stated for the current
// module, interface, checker, or program -- not only a module. A cycle delay in
// a program with no default clocking in effect is rejected. The scope is
// exercised end-to-end: the program is declared with real syntax and reached by
// instantiating it from a top module so the elaborator visits its body.
TEST(CycleDelayElab, ProgramScopeWithoutDefaultClockingErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "program p;\n"
      "  initial begin\n"
      "    ##5;\n"
      "  end\n"
      "endprogram\n"
      "module top;\n"
      "  p pi();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// §14.11: the same program with a default clocking in effect elaborates
// cleanly. Pairing this positive with the negative above isolates the
// diagnostic to the missing-default-clocking rule rather than any incidental
// program-scope error.
TEST(CycleDelayElab, ProgramScopeWithDefaultClockingNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "program p;\n"
      "  default clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "  initial begin\n"
      "    ##5;\n"
      "  end\n"
      "endprogram\n"
      "module top;\n"
      "  p pi();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §14.11: the interface is another enumerated scope for the requirement. A
// cycle delay in an instantiated interface with no default clocking is
// rejected.
TEST(CycleDelayElab, InterfaceScopeWithoutDefaultClockingErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface intf;\n"
      "  initial begin\n"
      "    ##5;\n"
      "  end\n"
      "endinterface\n"
      "module top;\n"
      "  intf ii();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// §14.11: the interface positive pair -- a default clocking in effect keeps the
// rule silent for the same cycle delay in interface scope.
TEST(CycleDelayElab, InterfaceScopeWithDefaultClockingNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface intf;\n"
      "  default clocking cb @(posedge clk);\n"
      "    input data;\n"
      "  endclocking\n"
      "  initial begin\n"
      "    ##5;\n"
      "  end\n"
      "endinterface\n"
      "module top;\n"
      "  intf ii();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §14.11: the checker is the fourth enumerated scope. A cycle delay in an
// instantiated checker with no default clocking is rejected.
TEST(CycleDelayElab, CheckerScopeWithoutDefaultClockingErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  checker chk;\n"
      "    initial begin\n"
      "      ##5;\n"
      "    end\n"
      "  endchecker\n"
      "  chk c1();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// §14.11: the checker positive pair -- a default clocking in effect keeps the
// rule silent for the same cycle delay in checker scope.
TEST(CycleDelayElab, CheckerScopeWithDefaultClockingNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  checker chk;\n"
      "    default clocking cb @(posedge clk);\n"
      "      input data;\n"
      "    endclocking\n"
      "    initial begin\n"
      "      ##5;\n"
      "    end\n"
      "  endchecker\n"
      "  chk c1();\n"
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

// §14.11: the intra-assignment prohibition is about the timing control, not the
// exact target shape. A cycle delay on a blocking assignment whose target is a
// bit-select of an ordinary variable is still an illegal intra-assignment delay
// -- the target is not a clocking-block variable, so it cannot be a synchronous
// drive. A default clocking is present so only the intra-assignment rule fires.
TEST(CycleDelayElab, IntraAssignBitSelectLhsCycleDelayErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  default clocking cb @(posedge clk);\n"
      "    output data;\n"
      "  endclocking\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a[3] = ##3 b[0];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// §14.11: the same holds for a part-select target on a nonblocking assignment.
// A slice of an ordinary variable is not a clockvar, so the leading ## is an
// illegal intra-assignment delay rather than a synchronous drive.
TEST(CycleDelayElab, IntraAssignPartSelectLhsCycleDelayErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  default clocking cb @(posedge clk);\n"
      "    output data;\n"
      "  endclocking\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a[3:0] <= ##2 b[3:0];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// §14.11: a concatenation target is another non-clockvar lvalue form. A cycle
// delay on a blocking assignment to a concatenation of ordinary variables is an
// illegal intra-assignment delay, not a synchronous drive, and must be
// rejected.
TEST(CycleDelayElab, IntraAssignConcatLhsCycleDelayErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  default clocking cb @(posedge clk);\n"
      "    output data;\n"
      "  endclocking\n"
      "  logic [3:0] a, b;\n"
      "  logic [7:0] c;\n"
      "  initial begin\n"
      "    {a, b} = ##3 c;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.has_errors);
}

// §14.11/§14.16: a bit-select of a clocking output variable is still a
// synchronous drive, so a leading cycle delay on it is legal. The tightened
// discriminator must peel the select and recognize the clockvar underneath
// rather than treating any non-identifier target as an intra-assignment.
TEST(CycleDelayElab, SynchronousDriveBitSelectWithCycleDelayNoError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] data;\n"
      "  default clocking cb @(posedge clk);\n"
      "    output data;\n"
      "  endclocking\n"
      "  initial begin\n"
      "    cb.data[3] <= ##1 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
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
