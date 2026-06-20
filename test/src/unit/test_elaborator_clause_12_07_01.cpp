#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(LoopStatementElaboration, ForLoopTypedInit) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i++) x = i[7:0];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LoopStatementElaboration, ForLoopUntypedInit) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    for (i = 0; i < 10; i = i + 1) x = i[7:0];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LoopStatementElaboration, NestedLoops) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 4; i++) begin\n"
      "      for (int j = 0; j < 4; j++) begin\n"
      "        x = i[7:0] + j[7:0];\n"
      "      end\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LoopStatementElaboration, ForCompoundAssignStepElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 20; i += 2) x = i[7:0];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LoopStatementElaboration, ForCommaSeparatedTypedInitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    for (int i = 0, int j = 4; i < j; i++, j--)\n"
      "      x = i[7:0];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LoopStatementElaboration, ForTypedInitNotVisibleAfterLoop) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i++) begin\n"
      "    end\n"
      "    i = 5;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// A for-loop whose initialization does not declare its control variable
// creates no implicit block, so the outer variable stays in scope after the
// loop and may still be referenced.
TEST(LoopStatementElaboration, UntypedForInitVarVisibleAfterLoop) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    for (i = 0; i < 10; i = i + 1) begin\n"
      "    end\n"
      "    i = 5;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
