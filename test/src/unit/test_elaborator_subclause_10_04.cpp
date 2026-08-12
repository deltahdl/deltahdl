#include "fixture_simulator.h"

using namespace delta;

namespace {

// §10.4: the left-hand side of a procedural assignment shall be a variable.
// Positive anchor — a variable LHS is accepted, confirming the net-target check
// does not reject legitimate variable targets.
TEST(ProceduralAssignmentElaboration, VariableLhsIsAccepted) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic v;\n"
      "  initial begin\n"
      "    v = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §10.4 states "The left-hand side shall be a variable that receives the
// assignment from the right-hand side". §6.5 states the same rule from the
// net's side, in the words the report uses: "A net cannot be procedurally
// assigned."
// The check tests the target against the module's net names, so it enforces
// §6.5 and the report names that subclause.
TEST(ProceduralAssignmentElaboration, ProceduralAssignToNetIsError) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  wire w;\n"
      "  initial begin\n"
      "    w = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  const delta::Diagnostic* diag =
      FindDiag(f, "cannot be the target of a procedural assignment");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "6.5");
}

TEST(ProceduralAssignmentElaboration, NonblockingAssignToNetIsError) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  wire w;\n"
      "  initial begin\n"
      "    w <= 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  const delta::Diagnostic* diag =
      FindDiag(f, "cannot be the target of a procedural assignment");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "6.5");
}

TEST(ProceduralAssignmentElaboration, SelectOfNetBaseIsError) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  wire [7:0] w;\n"
      "  initial begin\n"
      "    w[0] = 1'b1;\n"
      "  end\n"
      "endmodule\n",
      f);
  const delta::Diagnostic* diag =
      FindDiag(f, "cannot be the target of a procedural assignment");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "6.5");
}

TEST(ProceduralAssignmentElaboration, ConcatenationContainingNetIsError) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  wire w;\n"
      "  logic v;\n"
      "  initial begin\n"
      "    {v, w} = 2'b11;\n"
      "  end\n"
      "endmodule\n",
      f);
  const delta::Diagnostic* diag =
      FindDiag(f, "cannot be the target of a procedural assignment");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "6.5");
}

}  // namespace
