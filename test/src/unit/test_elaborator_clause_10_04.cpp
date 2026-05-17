#include "fixture_simulator.h"

using namespace delta;

namespace {

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
  EXPECT_TRUE(f.has_errors);
}

// §10.4: "The left-hand side shall be a variable." Compound assignments
// (`+=`, `<<=`, …) parse to kBlockingAssign so the blocking case above
// already exercises the elaborator's check for them. The nonblocking case
// drives the kNonblockingAssign branch in CollectProcTargets, which is a
// distinct production-code path and so warrants its own observer.
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
  EXPECT_TRUE(f.has_errors);
}

// §10.4: the "shall be a variable" rule applies to every LHS form §10.4
// enumerates, not just bare identifiers. A bit-select / part-select whose
// base is a net is still selecting from a net, so the rule rejects it.
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
  EXPECT_TRUE(f.has_errors);
}

// §10.4: a concatenation LHS combines several lvalues; if any element
// targets a net, the rule still rejects the whole assignment.
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
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
