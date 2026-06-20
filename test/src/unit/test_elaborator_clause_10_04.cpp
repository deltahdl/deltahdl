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
