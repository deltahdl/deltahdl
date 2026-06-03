#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(AssignmentWithinExpressionElaboration, SimpleAssignInExprInProcedural) {
  EXPECT_TRUE(ElabOk(
      "module t;\n"
      "  logic a, b;\n"
      "  initial if ((a = b)) ;\n"
      "endmodule\n"));
}

TEST(AssignmentWithinExpressionElaboration, CompoundAssignInExprInProcedural) {
  EXPECT_TRUE(ElabOk(
      "module t;\n"
      "  int a;\n"
      "  initial a = (a += 1);\n"
      "endmodule\n"));
}

TEST(AssignmentWithinExpressionElaboration,
     AssignInEventExpressionIsIllegal) {
  EXPECT_FALSE(ElabOk(
      "module t;\n"
      "  logic a, b;\n"
      "  always @(a = b) ;\n"
      "endmodule\n"));
}

TEST(AssignmentWithinExpressionElaboration,
     AssignInContinuousAssignIsIllegal) {
  EXPECT_FALSE(ElabOk(
      "module t;\n"
      "  logic a, b, c;\n"
      "  assign c = (a = b);\n"
      "endmodule\n"));
}

// §11.3.6: an assignment operator is illegal in an expression within a
// procedural continuous assignment.
TEST(AssignmentWithinExpressionElaboration,
     AssignInProceduralContinuousAssignIsIllegal) {
  EXPECT_FALSE(ElabOk(
      "module t;\n"
      "  logic a, b, c;\n"
      "  initial assign c = (a = b);\n"
      "endmodule\n"));
}

// The same procedural continuous assignment without an embedded assignment
// operator is legal, confirming it is the assignment-in-expression that is
// rejected above.
TEST(AssignmentWithinExpressionElaboration,
     ProceduralContinuousAssignWithoutEmbeddedAssignIsLegal) {
  EXPECT_TRUE(ElabOk(
      "module t;\n"
      "  logic a, c;\n"
      "  initial assign c = a;\n"
      "endmodule\n"));
}

}
