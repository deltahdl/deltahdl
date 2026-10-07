#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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
// wraps the loop in an implicit begin-end block, and that the block is a new
// hierarchical scope to which the variables are local. The elaborator keeps
// that rule by never admitting the name outside the loop, so the reference
// after the loop is left with no declaration at all and is reported under
// §23.9, which states the scope rules that decide where a name is visible.
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "undeclared identifier 'i'",
                            5, "23.9"));
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

// §12.7.1's implicit block ends with the loop for a read as it does for an
// assignment, so the loop's `i` named in a display after the loop resolves to
// nothing, and §23.9 reports it.
TEST(LoopStatementElaboration, ForTypedInitNotReadableAfterLoop) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 3; i++) ;\n"
      "    $display(\"i=%0d\", i);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier 'i'", 4,
                            "23.9"));
}

// The same boundary holds in a function body, whose reads are checked by a
// walk of their own.
TEST(LoopStatementElaboration, ForTypedInitNotReadableAfterLoopInFunction) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int x;\n"
      "  function int f();\n"
      "    for (int i = 0; i < 3; i++) ;\n"
      "    x = i;\n"
      "    return 0;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "reference to unresolved identifier 'i'", 5,
                            "23.9"));
}

// Inside the loop the declared variables are in scope: in the condition, in
// the step, in the body, and in a later initializer of the same
// initialization.
TEST(LoopStatementElaboration, ForTypedInitReadableInsideLoop) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int x;\n"
      "  initial begin\n"
      "    for (int i = 0, int j = i + 1; i < j; i = i + 1)\n"
      "      x = i + j;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// An initialization that assigns a module variable declares nothing, so that
// variable is still read after the loop.
TEST(LoopStatementElaboration, UntypedForInitVarReadableAfterLoop) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  integer i;\n"
      "  int x;\n"
      "  initial begin\n"
      "    for (i = 0; i < 3; i = i + 1) ;\n"
      "    x = i;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
