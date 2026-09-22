#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"

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

// §10.4 requires that the left-hand side of a procedural assignment be a
// variable, and admits four forms for it: a singular variable (§6.4), an
// aggregate variable (Clause 7), a bit-select, part-select or slice of a packed
// array, and a slice of an unpacked array. A net is none of the four, so the
// report cites §10.4. §6.5 says that a net cannot be procedurally assigned, but
// says it as what follows for a net from the requirement §10.4 places on the
// assignment, so it is not the citation however the check is written -- this
// one reads the module's net names, which is a mechanism and not the rule.
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot be the target of a procedural assignment",
                            4, "10.4"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot be the target of a procedural assignment",
                            4, "10.4"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot be the target of a procedural assignment",
                            4, "10.4"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot be the target of a procedural assignment",
                            5, "10.4"));
}

}  // namespace
