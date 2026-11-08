#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ConstConstantElaboration, ConstWithoutInitializerIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  const int x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "const variable 'x' must be initialized", 2,
                            "6.20.6"));
}

TEST(ConstConstantElaboration, ConstIntWithInitializerSucceeds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  const int x = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ConstConstantElaboration, ConstReassignmentIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  const int x = 5;\n"
      "  initial x = 10;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'x'",
                            3, "6.20"));
}

TEST(ConstConstantElaboration, ConstNonblockingReassignmentIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  const int x = 5;\n"
      "  initial x <= 10;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'x'",
                            3, "6.20"));
}

TEST(ConstConstantElaboration, ConstReassignmentInAlwaysFfIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  const int x = 5;\n"
      "  logic clk;\n"
      "  always_ff @(posedge clk) x <= 10;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "assignment to constant 'x'",
                            4, "6.20"));
}

TEST(ConstConstantElaboration, ConstInitializedFromParameterSucceeds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top #(parameter P = 5);\n"
      "  const int x = P;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ConstConstantElaboration, ConstInitializedFromLocalparamSucceeds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  localparam LP = 10;\n"
      "  const int x = LP;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ConstConstantElaboration, ConstInitializedFromAnotherConstSucceeds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  const int a = 5;\n"
      "  const int b = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ConstConstantElaboration, ConstCreatesVariable) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  const int LIMIT = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& v : mod->variables) {
    if (v.name == "LIMIT") {
      found = true;
      EXPECT_NE(v.init_expr, nullptr);
    }
  }
  EXPECT_TRUE(found);
}

TEST(ConstConstantElaboration, ConstInitializedFromEnumNameSucceeds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef enum int {RED, GREEN, BLUE} color_t;\n"
      "  const int x = GREEN;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ConstConstantElaboration, ConstInitializedFromConstantFunctionSucceeds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  function automatic int double_it(int v);\n"
      "    return v * 2;\n"
      "  endfunction\n"
      "  const int x = double_it(21);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ConstConstantElaboration, ConstWithHierarchicalNameInitializerSucceeds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  const logic option = a.b.c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ConstConstantElaboration, ConstInitializedFromGenvarSucceeds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 2; i = i + 1) begin : g\n"
      "    const int x = i;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ConstConstantElaboration, ConstAutomaticAcceptsRuntimeInitializer) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  function automatic int add_one(int a);\n"
      "    const int local_c = a + 1;\n"
      "    return local_c;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ConstConstantElaboration, ConstClassHandleDeclarationSucceeds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int x;\n"
      "  function new(int a);\n"
      "    x = a;\n"
      "  endfunction\n"
      "endclass\n"
      "module top;\n"
      "  const C obj = new(5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ConstConstantElaboration, ConstClassHandleReassignmentIsError) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "  function new();\n"
      "  endfunction\n"
      "endclass\n"
      "module top;\n"
      "  const C obj = new();\n"
      "  initial obj = new();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment to constant 'obj'", 7, "6.20"));
}

TEST(ConstConstantElaboration, ConstObjectMemberWriteSucceeds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int x;\n"
      "  function new();\n"
      "  endfunction\n"
      "endclass\n"
      "module top;\n"
      "  const C obj = new();\n"
      "  initial obj.x = 5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
