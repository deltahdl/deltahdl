#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §9.2.3: final procedure with delay produces an error.
TEST(ElabClause09_02_03, DelayInFinalErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  final #5 x = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §9.2.3: final procedure with event control produces an error.
TEST(ElabClause09_02_03, EventControlInFinalErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic clk, x;\n"
      "  final @(posedge clk) x = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §9.2.3: final procedure with wait produces an error.
TEST(ElabClause09_02_03, WaitInFinalErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  final wait(x) x = 0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §9.2.3: final procedure with fork-join produces an error.
TEST(ElabClause09_02_03, ForkJoinInFinalErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  final begin\n"
      "    fork\n"
      "      a = 1;\n"
      "      b = 0;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §9.2.3: Valid final procedure with simple assignment, no errors.
TEST(ElabClause09_02_03, ValidFinalNoErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  final x = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §9.2.3: Valid final procedure with begin-end block, no errors.
TEST(ElabClause09_02_03, ValidFinalBlockNoErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [31:0] a, b;\n"
      "  final begin\n"
      "    a = 1;\n"
      "    b = 2;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §9.2.3: final elaborates to kFinal process kind.
TEST(ElabClause09_02_03, ElaboratesToCorrectKind) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  final x = 99;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  bool found = false;
  for (auto& p : design->top_modules[0]->processes) {
    if (p.kind == RtlirProcessKind::kFinal) found = true;
  }
  EXPECT_TRUE(found);
}

// §9.2.3: Multiple final procedures coexist.
TEST(ElabClause09_02_03, MultipleFinalProcedures) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [31:0] a, b;\n"
      "  final a = 1;\n"
      "  final b = 2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  int count = 0;
  for (auto& p : design->top_modules[0]->processes) {
    if (p.kind == RtlirProcessKind::kFinal) ++count;
  }
  EXPECT_EQ(count, 2);
}

// §9.2.3: final and initial coexist without errors.
TEST(ElabClause09_02_03, FinalAndInitialCoexist) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [31:0] x;\n"
      "  initial x = 10;\n"
      "  final x = 20;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  bool has_initial = false, has_final = false;
  for (auto& p : design->top_modules[0]->processes) {
    if (p.kind == RtlirProcessKind::kInitial) has_initial = true;
    if (p.kind == RtlirProcessKind::kFinal) has_final = true;
  }
  EXPECT_TRUE(has_initial);
  EXPECT_TRUE(has_final);
}

// §9.3.2: fork/join in final is an error.
TEST(ElabClause09_03_02, ForkInFinalErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  final begin\n"
      "    fork\n"
      "      a = 1;\n"
      "      b = 0;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §9.6.1: Wait fork is a timing control, error in final.
TEST(ElabClause09_06_01, WaitForkInFinalErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a;\n"
      "  final begin\n"
      "    wait fork;\n"
      "    a = 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
