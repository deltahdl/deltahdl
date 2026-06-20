#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(LoopStatementElaboration, ForeachLoop) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [4];\n"
      "  logic [7:0] total;\n"
      "  initial begin\n"
      "    foreach (arr[i]) total = total + arr[i];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LoopStatementElaboration, ForeachMultiDimElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] matrix [0:3][0:3];\n"
      "  initial begin\n"
      "    foreach (matrix[i, j]) matrix[i][j] = 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §12.7.3 — the number of loop variables shall not exceed the number of array
// dimensions.
TEST(LoopStatementElaboration, ForeachTooManyLoopVarsIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr [4];\n"
      "  initial begin\n"
      "    foreach (arr[i, j]) arr[i] = j;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(LoopStatementElaboration, ForeachLoopVarCountAtDimLimitOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [4];\n"
      "  initial begin\n"
      "    foreach (arr[i, j]) arr[i][j] = 1'b0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §12.7.3 — foreach loop variables are read-only.
TEST(LoopStatementElaboration, ForeachLoopVarAssignIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr [4];\n"
      "  initial begin\n"
      "    foreach (arr[i]) i = 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(LoopStatementElaboration, ForeachLoopVarIncrementIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr [4];\n"
      "  initial begin\n"
      "    foreach (arr[i]) i++;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

TEST(LoopStatementElaboration, ForeachAssignArrayElementOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int arr [4];\n"
      "  initial begin\n"
      "    foreach (arr[i]) arr[i] = i;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §12.7.3 — the read-only rule applies regardless of the assignment form;
// a nonblocking assignment to a loop variable is just as illegal.
TEST(LoopStatementElaboration, ForeachLoopVarNonblockingAssignIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr [4];\n"
      "  initial begin\n"
      "    foreach (arr[i]) i <= 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §12.7.3 — a loop variable may not reuse the array's identifier.
TEST(LoopStatementElaboration, ForeachLoopVarSameNameAsArrayIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int arr [4];\n"
      "  int x;\n"
      "  initial begin\n"
      "    foreach (arr[arr]) x = arr;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §12.7.3 — the identifier-clash rule covers every loop-variable slot, not
// just the first one.
TEST(LoopStatementElaboration, ForeachLaterLoopVarSameNameAsArrayIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] matrix [0:3][0:3];\n"
      "  int x;\n"
      "  initial begin\n"
      "    foreach (matrix[i, matrix]) x = i;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
