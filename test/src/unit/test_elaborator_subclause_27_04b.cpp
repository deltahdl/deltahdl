#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <utility>

#include "common/diagnostic.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(GenerateElaboration, GenerateForSingleItemBodyWithoutBeginEnd) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top #(parameter N = 3) ();\n"
      "  generate\n"
      "    for (genvar i = 0; i < N; i = i + 1)\n"
      "      logic [7:0] v;\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->variables.size(), 3u);
}

TEST(GenerateElaboration, NestedLoopGenerateSameGenvarErrors) {
  ElabFixture f;
  ElabOk(
      "module mod_a();\n"
      "  genvar i;\n"
      "  for (i = 0; i < 5; i = i + 1) begin : a\n"
      "    for (i = 0; i < 5; i = i + 1) begin : b\n"
      "      logic [7:0] x;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "genvar 'i' is already in use by an enclosing loop "
                            "generate construct",
                            4, "27.4"));
}

TEST(GenerateElaboration, NestedLoopGenerateDistinctGenvarsElaborate) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top #(parameter N = 2) ();\n"
      "  genvar i, j;\n"
      "  generate\n"
      "    for (i = 0; i < N; i = i + 1) begin\n"
      "      for (j = 0; j < N; j = j + 1) begin\n"
      "        logic [7:0] x;\n"
      "      end\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->variables.size(), 4u);
}

TEST(GenerateElaboration, SiblingLoopGenerateReuseSameGenvarElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top();\n"
      "  genvar i;\n"
      "  generate\n"
      "    for (i = 0; i < 2; i = i + 1) begin\n"
      "      logic [7:0] a;\n"
      "    end\n"
      "    for (i = 0; i < 2; i = i + 1) begin\n"
      "      logic [7:0] b;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->variables.size(), 4u);
}

TEST(GenerateElaboration, GenerateForSparseGenvarRange) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top();\n"
      "  genvar i;\n"
      "  generate\n"
      "    for (i = 1; i < 16; i = i * 2) begin\n"
      "      logic [7:0] v;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->variables.size(), 4u);
}

TEST(GenerateElaboration, GenerateForIncrementIterationForm) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top();\n"
      "  genvar i;\n"
      "  generate\n"
      "    for (i = 0; i < 4; i++) begin\n"
      "      logic [7:0] v;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->variables.size(), 4u);
}

TEST(GenerateElaboration, GenerateForDecrementIterationForm) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top();\n"
      "  genvar i;\n"
      "  generate\n"
      "    for (i = 3; i >= 0; i--) begin\n"
      "      logic [7:0] v;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->variables.size(), 4u);
}

TEST(GenerateElaboration, GenerateForBoundFromLocalparam) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top();\n"
      "  localparam N = 4;\n"
      "  genvar i;\n"
      "  generate\n"
      "    for (i = 0; i < N; i = i + 1) begin\n"
      "      logic [7:0] v;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->variables.size(), 4u);
}

TEST(GenerateElaboration, NestedLoopGenerateInnerBoundUsesOuterGenvar) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top();\n"
      "  genvar i, j;\n"
      "  generate\n"
      "    for (i = 0; i < 3; i = i + 1) begin\n"
      "      for (j = 0; j < i; j = j + 1) begin\n"
      "        logic [7:0] x;\n"
      "      end\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->variables.size(), 3u);
}

TEST(GenerateElaboration, GenerateForInitStepMismatchIncrementFormErrors) {
  ElabFixture f;
  ElabOk(
      "module top();\n"
      "  genvar i, j;\n"
      "  generate\n"
      "    for (i = 0; i < 3; j++) begin\n"
      "      logic [7:0] x;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "generate-for init and step assign different genvars", 4, "27.4"));
}

TEST(GenerateElaboration, GenvarIsNotAmongTheModuleVariables) {
  ElabFixture f;
  auto* design = Elaborate(
      "module top();\n"
      "  genvar i;\n"
      "  generate\n"
      "    for (i = 0; i < 4; i++) begin\n"
      "      logic [7:0] v;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  for (const auto& v : mod->variables) {
    EXPECT_NE(v.name, "i");
  }
}

TEST(GenerateElaboration, LoopIterationsDoNotRedeclareTheSameInstanceName) {
  ElabFixture f;
  auto* design = Elaborate(
      "module child; endmodule\n"
      "module top;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 2; i = i + 1) begin\n"
      "    child c1();\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(GenerateElaboration, TwoInstancesOfOneNameInALoopBodyIsRedeclaration) {
  ElabFixture f;
  Elaborate(
      "module child; endmodule\n"
      "module top;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 2; i = i + 1) begin\n"
      "    child c1();\n"
      "    child c1();\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'c1'", 6, "23.9"));
}

TEST(GenerateElaboration, TwoInstancesOfOneNameInAModuleBodyIsRedeclaration) {
  ElabFixture f;
  Elaborate(
      "module child; endmodule\n"
      "module top;\n"
      "  child c1();\n"
      "  child c1();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'c1'", 4, "23.9"));
}

TEST(GenerateElaboration, GenerateForInitReferencesOwnGenvarNames27_4) {
  ElabFixture f;
  ElabOk(
      "module top();\n"
      "  generate\n"
      "    for (genvar i = i + 1; i < 3; i = i + 1) begin\n"
      "      logic [7:0] x;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "generate-for init reads the loop's own genvar", 3,
                            "27.4"));
}

TEST(GenerateElaboration,
     ImportedParameterDoesNotReachAnotherModulesGenerateFor) {
  ElabFixture f;
  ElaborateWithPreprocessor(
      "package p;\n"
      "  parameter int W = 0;\n"
      "endpackage\n"
      "module a;\n"
      "  import p::*;\n"
      "endmodule\n"
      "module b;\n"
      "  for (genvar i = W; i < 3; i = i + 1) begin : g\n"
      "    logic x;\n"
      "  end\n"
      "endmodule\n",
      f, "", true);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "generate-for init is not constant", 8, "27.4"));
}

TEST(GenerateElaboration, GenerateForBoundOnAVariableIsNotConstant) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [3:0] n;\n"
      "  for (genvar i = 0; i < n; i = i + 1) begin : g\n"
      "    logic x;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "generate-for termination expression is not constant", 3, "27.4"));
}

TEST(GenerateElaboration, GenerateForStepOnAVariableIsNotConstant) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [3:0] n;\n"
      "  for (genvar i = 0; i < 4; i = i + n) begin : g\n"
      "    logic x;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "generate-for iteration expression is not constant",
                            3, "27.4"));
}

TEST(GenerateElaboration,
     GenerateForBoundOnAnUndeclaredIdentifierIsNotConstant) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  for (genvar i = 0; i < W; i = i + 1) begin : g\n"
      "    logic x;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "generate-for termination expression is not constant", 2, "27.4"));
}

TEST(GenerateElaboration, GenerateForBoundThatFoldsToFalseIsNotReported) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  for (genvar i = 0; i < 0; i = i + 1) begin : g\n"
      "    logic x;\n"
      "  end\n"
      "endmodule\n",
      f);
  std::string reported;
  for (const auto& diag : f.diag.Diagnostics()) {
    if (diag.subclause != "27.4") continue;
    reported +=
        (diag.severity == DiagSeverity::kError ? "\n  error" : "\n  warning");
    reported += " at line " + std::to_string(diag.loc.line) + ": ";
    reported += diag.message;
  }
  EXPECT_EQ(reported, "")
      << "a loop generate whose bound folds to 0 is a legal "
         "zero-trip loop, and the run reported it under "
         "§27.4:"
      << reported;
}

TEST(GenerateElaboration, ReportedHeaderElaboratesAsALoopThatBuildsNothing) {
  ElabFixture f;
  auto* design = ElaborateSrcAllowingParseErrors(
      "module top();\n"
      "  genvar i;\n"
      "  for (i++; i < 4; i) begin : g\n"
      "    logic [7:0] x;\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a loop generate's initialization is written", 3,
                            "A.4.2"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a loop generate's iteration is written", 3,
                            "A.4.2"));
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  EXPECT_TRUE(design->top_modules[0]->variables.empty());
}

TEST(GenerateElaboration, GenvarReadOutsideALoopSchemeErrors) {
  ElabFixture f;
  ElabOk(
      "module top;\n"
      "  genvar i;\n"
      "  int k;\n"
      "  initial k = i;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "genvar 'i' is referenced outside a loop generate "
                            "scheme",
                            4, "27.4"));
}

TEST(GenerateElaboration, GenvarReadInItsLoopIsAccepted) {
  ElabFixture f;
  ElabOk(
      "module top;\n"
      "  genvar i;\n"
      "  int k;\n"
      "  for (i = 0; i < 2; i = i + 1) begin : g\n"
      "    int v = i;\n"
      "    initial k = i;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(GenerateElaboration, GenvarInConstantPositionsOutsideALoopErrors) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  genvar i;\n"
      "  parameter int P = i;\n"
      "  if (i == 0) begin : g\n"
      "    logic x;\n"
      "  end\n"
      "  case (i)\n"
      "    0: begin : h logic y; end\n"
      "  endcase\n"
      "  logic [i:0] v;\n"
      "  wire w; logic a;\n"
      "  assign #i w = a;\n"
      "endmodule\n",
      f);
  for (uint32_t line : {3u, 4u, 7u, 10u, 12u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "genvar 'i' is referenced outside a loop "
                              "generate scheme",
                              line, "27.4"));
  }
}

TEST(GenerateElaboration, GenvarInConstantPositionsInsideALoopAccepted) {
  EXPECT_TRUE(
      ElabOk("module top;\n"
             "  wire [3:0] w;\n"
             "  logic [3:0] a;\n"
             "  for (genvar i = 0; i < 2; i++) begin : l\n"
             "    localparam int P = i;\n"
             "    if (i == 0) begin : g\n"
             "      logic x;\n"
             "    end\n"
             "    case (i)\n"
             "      0: begin : h logic y; end\n"
             "      default: begin : d logic z; end\n"
             "    endcase\n"
             "    logic [i:0] v;\n"
             "    assign #i w[i] = a[i];\n"
             "  end\n"
             "endmodule\n"));
}

TEST(GenerateElaboration, LoopIndexNoEarlierGenvarDeclaresIsReported) {
  ElabFixture f;
  Elaborate(
      "module top;\n"
      "  integer n;\n"
      "  for (k = 0; k < 2; k = k + 1) begin : a end\n"
      "  for (n = 0; n < 2; n = n + 1) begin : b end\n"
      "  for (j = 0; j < 2; j = j + 1) begin : c end\n"
      "  genvar j;\n"
      "  for (genvar m = 0; m < 2; m++) begin : d end\n"
      "  genvar p;\n"
      "  for (p = 0; p < 2; p++) begin : e end\n"
      "endmodule\n",
      f);
  for (auto [name, line] :
       {std::pair<const char*, uint32_t>{"k", 3}, {"n", 4}, {"j", 5}}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              std::string("loop generate index '") + name +
                                  "' is declared by no genvar declaration",
                              line, "27.4"))
        << name;
  }
  for (const auto& diag : f.diag.Diagnostics()) {
    EXPECT_LT(diag.loc.line, 6u) << diag.message;
  }
}

TEST(GenerateElaboration, GenvarOfAnEnclosingScopeDeclaresALoopIndex) {
  ElabFixture f;
  Elaborate(
      "module top;\n"
      "  genvar i;\n"
      "  if (1) begin : g1\n"
      "    genvar q;\n"
      "    for (q = 0; q < 2; q++) begin : x end\n"
      "    for (i = 0; i < 2; i++) begin : y end\n"
      "  end\n"
      "  if (1) begin : g2\n"
      "    for (q = 0; q < 2; q++) begin : z end\n"
      "  end\n"
      "  for (genvar r = 0; r < 2; r++) begin : w end\n"
      "  for (r = 0; r < 2; r++) begin : u end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "loop generate index 'q' is declared by no genvar "
                            "declaration",
                            9, "27.4"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "loop generate index 'r' is declared by no genvar "
                            "declaration",
                            12, "27.4"));
  for (const auto& diag : f.diag.Diagnostics()) {
    if (diag.message.find("is declared by no genvar") == std::string::npos) {
      continue;
    }
    EXPECT_TRUE(diag.loc.line == 9 || diag.loc.line == 12) << diag.message;
  }
}

}  // namespace
