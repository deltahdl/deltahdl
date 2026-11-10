#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "fixture_simulator.h"
#include "helpers_param_value.h"
#include "helpers_param_value_assignability.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"

using namespace delta;

namespace {

TEST(LocalparamElaboration, ParameterAndLocalparamCoexist) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter int WIDTH = 8;\n"
      "  localparam int DEPTH = 16;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found_width = false, found_depth = false;
  for (const auto& p : mod->params) {
    if (p.name == "WIDTH") {
      EXPECT_EQ(p.resolved_value, 8);
      EXPECT_FALSE(p.is_localparam);
      found_width = true;
    }
    if (p.name == "DEPTH") {
      EXPECT_EQ(p.resolved_value, 16);
      EXPECT_TRUE(p.is_localparam);
      found_depth = true;
    }
  }
  EXPECT_TRUE(found_width);
  EXPECT_TRUE(found_depth);
}

TEST(LocalparamElaboration, LocalparamDerivedFromParameter) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  parameter int WIDTH = 8;\n"
      "  localparam int DOUBLE = WIDTH * 2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& p : mod->params) {
    if (p.name == "DOUBLE") {
      EXPECT_TRUE(p.is_resolved);
      EXPECT_EQ(p.resolved_value, 16);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(LocalparamElaboration, ImplicitTypeLocalparamResolvesValue) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  localparam X = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (auto& p : mod->params) {
    if (p.name == "X") {
      found = true;
      EXPECT_TRUE(p.is_localparam);
      EXPECT_TRUE(p.is_resolved);
      EXPECT_EQ(p.resolved_value, 42);
    }
  }
  EXPECT_TRUE(found);
}

TEST(LocalparamElaboration, DefparamOnLocalparamIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module child;\n"
      "  localparam int WIDTH = 4;\n"
      "endmodule\n"
      "module top;\n"
      "  child u0();\n"
      "  defparam u0.WIDTH = 16;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "defparam cannot override a local parameter", 6,
                            "23.10.1"));
}

TEST(LocalparamElaboration, NamedInstanceOverrideOfLocalparamIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module child #(localparam int LP = 4)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.LP(9)) u0();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "module 'child' has no parameter 'LP'", 4,
                            "23.10.2.2"));
}

TEST(LocalparamElaboration, PositionalInstanceOverrideOfLocalparamIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module child #(localparam int LP = 4)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(9) u0();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "too many positional parameter overrides for module 'child'", 4,
      "23.10.2.1"));
}

TEST(LocalparamElaboration, LocalparamFollowsOverriddenParameter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int W = 8);\n"
      "  localparam int W2 = W * 2;\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.W(16)) u0();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* top = design->top_modules[0];
  ASSERT_FALSE(top->children.empty());
  auto* child = top->children[0].resolved;
  ASSERT_NE(child, nullptr);
  bool found = false;
  for (const auto& p : child->params) {
    if (p.name == "W2") {
      found = true;
      EXPECT_TRUE(p.is_localparam);
      EXPECT_TRUE(p.is_resolved);
      EXPECT_EQ(p.resolved_value, 32);
    }
  }
  EXPECT_TRUE(found);
}

TEST(LocalparamElaboration, LocalparamFollowsDefparamModifiedParameter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child #(parameter int W = 8);\n"
      "  localparam int W2 = W * 2;\n"
      "endmodule\n"
      "module top;\n"
      "  child u0();\n"
      "  defparam u0.W = 16;\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* child = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(child, nullptr);
  bool found = false;
  for (const auto& p : child->params) {
    if (p.name == "W2") {
      found = true;
      EXPECT_TRUE(p.is_localparam);
      EXPECT_TRUE(p.is_resolved);
      EXPECT_EQ(p.resolved_value, 32);
    }
  }
  EXPECT_TRUE(found);
}

TEST(LocalparamElaboration, StickyLocalparamPortRejectsInstanceOverride) {
  ElabFixture f;
  ElaborateSrc(
      "module child #(parameter int A = 1, localparam int B = 2, int C = "
      "3)();\n"
      "endmodule\n"
      "module top;\n"
      "  child #(.C(9)) u0();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "module 'child' has no parameter 'C'", 4,
                            "23.10.2.2"));
}

TEST(LocalparamElaboration, NonConstantIdentifierInitializerIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int v;\n"
      "  localparam int N = v;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "localparam 'N' initializer is not a constant expression", 3, "6.20.4"));
}

TEST(LocalparamElaboration, NonConstantBinaryInitializerIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int v;\n"
      "  localparam int N = v + 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "localparam 'N' initializer is not a constant expression", 3, "6.20.4"));
}

TEST(LocalparamElaboration, SpecializationOverrideThatDoesNotFoldIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "class C #(int P = 1);\n"
      "endclass\n"
      "module m;\n"
      "  int v;\n"
      "  localparam int N = C#(v)::P;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "localparam 'N' initializer is not a constant expression", 5, "6.20.4"));
}

TEST(LocalparamElaboration, ConstantIdentifierInitializerIsAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  localparam int K = 4;\n"
      "  localparam int N = K;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LocalparamElaboration, NonConstantInitializerInAGenerateBlockIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int v;\n"
      "  if (1) begin\n"
      "    localparam int N = v;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "localparam 'N' initializer is not a constant expression", 4, "6.20.4"));
}

TEST(LocalparamElaboration,
     NonConstantInitializerInAGenerateElseArmIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int v;\n"
      "  if (0) begin\n"
      "    localparam int A = 1;\n"
      "  end else begin\n"
      "    localparam int B = v;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "localparam 'B' initializer is not a constant expression", 6, "6.20.4"));
}

TEST(LocalparamElaboration,
     NonConstantInitializerInAGenerateCaseArmIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int v;\n"
      "  localparam int S = 0;\n"
      "  case (S)\n"
      "    0: begin\n"
      "      localparam int N = v;\n"
      "    end\n"
      "  endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "localparam 'N' initializer is not a constant expression", 6, "6.20.4"));
}

TEST(LocalparamElaboration, NonConstantInitializerInAPackageIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  int v;\n"
      "  localparam int N = v;\n"
      "endpackage\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "localparam 'N' initializer is not a constant expression", 3, "6.20.4"));
}

TEST(LocalparamElaboration,
     NonConstantPackageParameterIsReportedAsALocalparam) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  int v;\n"
      "  parameter int N = v;\n"
      "endpackage\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "localparam 'N' initializer is not a constant expression", 3, "6.20.4"));
}

TEST(LocalparamElaboration,
     NonConstantInitializerAtCompilationUnitScopeIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "int v;\n"
      "localparam int N = v;\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "localparam 'N' initializer is not a constant expression", 2, "6.20.4"));
}

TEST(LocalparamElaboration, ConstantInitializerInAGenerateBlockIsAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  if (1) begin\n"
      "    localparam int K = 4;\n"
      "    localparam int N = K + 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LocalparamElaboration,
     GenerateBlockLocalparamFoldsAnEnumConstantOfItsOwnBlock) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  if (1) begin : g\n"
      "    typedef enum { A = 3, B = 5 } e_t;\n"
      "    localparam int X = B;\n"
      "    if (1) begin : h\n"
      "      localparam int Y = A | B;\n"
      "    end\n"
      "  end\n"
      "  case (1)\n"
      "    1: begin : c\n"
      "      enum { C = 2, D = 9 } v;\n"
      "      localparam int Z = D;\n"
      "    end\n"
      "  endcase\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* x = FindParam(design, "m", "X");
  ASSERT_NE(x, nullptr);
  EXPECT_EQ(x->resolved_value, 5);
  const auto* y = FindParam(design, "m", "Y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->resolved_value, 7);
  const auto* z = FindParam(design, "m", "Z");
  ASSERT_NE(z, nullptr);
  EXPECT_EQ(z->resolved_value, 9);
}

TEST(LocalparamElaboration,
     EnumConstantOfItsOwnBlockIsAcceptedInEveryGenerateArm) {
  const char* const kSources[] = {
      "module m;\n  if (0) begin\n  end else begin\n"
      "    typedef enum { A, B } e_t;\n    localparam int N = B;\n"
      "  end\nendmodule\n",
      "module m;\n  for (genvar i = 0; i < 1; i++) begin : b\n"
      "    enum { A, B } v;\n    localparam int N = B + i;\n"
      "  end\nendmodule\n",
      "module m;\n  localparam int S = 0;\n  case (S)\n    0: begin\n"
      "      typedef enum { A, B } e_t;\n      localparam e_t N = B;\n"
      "    end\n  endcase\nendmodule\n",
  };
  ExpectEachAccepted(kSources);
}

TEST(LocalparamElaboration, GenvarInitializerInAGenerateLoopIsAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  genvar g;\n"
      "  for (g = 0; g < 2; g = g + 1) begin : b\n"
      "    localparam int L = g + 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LocalparamElaboration, PackageLocalparamReadingAnEarlierOneIsAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "package p;\n"
      "  localparam int K = 4;\n"
      "  localparam int N = K + 1;\n"
      "endpackage\n"
      "module m;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LocalparamElaboration,
     PackageParameterOringMembersOfAPackageEnumIsAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "package p;\n"
      "  typedef bit [7:0] flag_t;\n"
      "  typedef enum flag_t {\n"
      "    DEEP = (1 << 4), SHALLOW = (1 << 5), REFERENCE = (1 << 6)\n"
      "  } policy_e;\n"
      "  parameter RECURSION = (DEEP | SHALLOW | REFERENCE);\n"
      "endpackage\n"
      "module m;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LocalparamElaboration,
     PackageParameterTypedByAPackageEnumTakingAMemberIsAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "package p;\n"
      "  typedef enum {\n"
      "    UNINITIALIZED, PRE_INIT, INITIALIZING, INITIALIZED, ABORTED\n"
      "  } state_e;\n"
      "  parameter state_e POST_INIT = INITIALIZED;\n"
      "endpackage\n"
      "module m;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LocalparamElaboration,
     PackageParameterReadingAMemberOfABareEnumDeclarationIsAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "package p;\n"
      "  enum { LOW = 2, HIGH = 9 } level;\n"
      "  parameter int TOP = HIGH;\n"
      "endpackage\n"
      "module m;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(LocalparamElaboration, ModuleLocalparamOringItsOwnEnumMembersFolds) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  typedef enum { RED = 3, GREEN = 5 } color_t;\n"
      "  localparam int X = RED | GREEN;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* x = FindParam(design, "m", "X");
  ASSERT_NE(x, nullptr);
  EXPECT_TRUE(x->is_resolved);
  EXPECT_EQ(x->resolved_value, 7);
}

TEST(LocalparamElaboration,
     CompilationUnitLocalparamOringEnumMembersFoldsAndIsAccepted) {
  ElabFixture f;
  auto* design = Elaborate(
      "typedef enum { RED = 3, GREEN = 5 } color_t;\n"
      "localparam int X = RED | GREEN;\n"
      "module m;\n"
      "  localparam int Y = X;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* y = FindParam(design, "m", "Y");
  ASSERT_NE(y, nullptr);
  EXPECT_TRUE(y->is_resolved);
  EXPECT_EQ(y->resolved_value, 7);
}

TEST(LocalparamElaboration, CompilationUnitParameterFromAPackageParameter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "package p;\n"
      "  parameter int P = 4;\n"
      "endpackage\n"
      "parameter int X = p::P;\n"
      "module m;\n"
      "  localparam int Q = X;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(design, "Q"), 4);
}

TEST(LocalparamElaboration, LocalGroupEndsAtTheNextParameterKeyword) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module child #(parameter int A = 1, localparam int B = 2,\n"
                 "               int C = 3, parameter int D = 4) ();\n"
                 "  initial $display(\"%0d %0d %0d %0d\", A, B, C, D);\n"
                 "endmodule\n"
                 "module top; child #(.D(9)) u(); endmodule\n",
                 f),
      "1 2 3 9\n");
}

TEST(LocalparamElaboration, TypeParameterInALocalGroupRejectsAnOverride) {
  ElabFixture f;
  ElaborateSrc(
      "module m #(localparam int B = 2, type T = int) (); T x;\n"
      "endmodule\n"
      "module top; m #(.T(byte)) u(); endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "module 'm' has no parameter 'T'", 3, "23.10.2.2"));
}

TEST(LocalparamElaboration, TypeParameterInALocalGroupKeepsItsDefault) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module m #(localparam int B = 2, type T = int) (); T x;\n"
                 "endmodule\n"
                 "module top;\n"
                 "  m u();\n"
                 "  initial $display(\"%0d\", $bits(u.x));\n"
                 "endmodule\n",
                 f),
      "32\n");
}

}  // namespace
