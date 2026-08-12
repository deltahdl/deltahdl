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

// §12.7.1 states that declaring the control variables in the for_initialization
// "creates an implicit begin-end block around the loop", and that "This block
// creates a new hierarchical scope, making the variables local to the loop
// scope". The elaborator keeps that rule by never admitting the name outside
// the loop, so the reference after the loop is left with no declaration at all
// and is reported under §23.9, which states the scope rules that decide where a
// name is visible.
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
  const delta::Diagnostic* diag = FindDiag(f, "undeclared identifier 'i'");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "23.9");
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
