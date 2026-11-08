#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_elaborator.h"
#include "helpers_generate_block_items.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(SelectElaboration,
     ReversedPartSelectInAnAssertionPassStatementNames11_5_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:4] v;\n"
      "  logic [3:0] result;\n"
      "  logic ok;\n"
      "  initial assert (ok) result = v[4:7];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "part-select's first index must address a more", 5,
                            "11.5.1"));
}

TEST(SelectElaboration,
     ReversedPartSelectInAnAssertionFailStatementNames11_5_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:4] word;\n"
      "  logic [3:0] out;\n"
      "  logic passed;\n"
      "  initial assert (passed) else out = word[4:7];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "part-select's first index must address a more", 5,
                            "11.5.1"));
}

TEST(SelectElaboration, ReversedPartSelectInARandcaseItemNames11_5_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:4] bus;\n"
      "  logic [3:0] taken;\n"
      "  initial randcase 1: taken = bus[4:7]; endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "part-select's first index must address a more", 4,
                            "11.5.1"));
}

TEST(SelectElaboration, ReversedPartSelectInARandsequenceCodeBlockNames11_5_1) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:4] src;\n"
      "  logic [3:0] dst;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { dst = src[4:7]; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "part-select's first index must address a more", 6,
                            "11.5.1"));
}

TEST(SelectElaboration, SelectOnConcatLvalueInAForkArmNames11_4_12) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a, b;\n"
      "  initial begin\n"
      "    fork\n"
      "      {a, b}[2] = 1'b1;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "select of a concatenation shall not be used", 5,
                            "11.4.12"));
}

TEST(SelectElaboration,
     SelectOnConcatLvalueInAnAssertionPassStatementNames11_4_12) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a, b;\n"
      "  logic ok;\n"
      "  initial assert (ok) {a, b}[2] = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "select of a concatenation shall not be used", 4,
                            "11.4.12"));
}

TEST(SelectElaboration,
     SelectOnConcatLvalueInAnAssertionFailStatementNames11_4_12) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a, b;\n"
      "  logic ok;\n"
      "  initial assert (ok) else {a, b}[2] = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "select of a concatenation shall not be used", 4,
                            "11.4.12"));
}

TEST(SelectElaboration, SelectOnConcatLvalueInARandcaseItemNames11_4_12) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a, b;\n"
      "  initial randcase 1: {a, b}[2] = 1'b1; endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "select of a concatenation shall not be used", 3,
                            "11.4.12"));
}

TEST(SelectElaboration,
     SelectOnConcatLvalueInARandsequenceCodeBlockNames11_4_12) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a, b;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { {a, b}[2] = 1'b1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "select of a concatenation shall not be used", 5,
                            "11.4.12"));
}

TEST(SelectElaboration,
     SelectOnConcatLvalueInAForLoopInitializationNames11_4_12) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a, b;\n"
      "  int i;\n"
      "  initial for ({a, b}[2] = 1'b1; i < 1; i = i + 1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "select of a concatenation shall not be used", 4,
                            "11.4.12"));
}

TEST(SelectElaboration, SelectOnConcatLvalueInAForLoopStepNames11_4_12) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a, b;\n"
      "  int i;\n"
      "  initial for (i = 0; i < 1; {a, b}[2] = 1'b1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "select of a concatenation shall not be used", 4,
                            "11.4.12"));
}

TEST(SelectElaboration, SelectsOfTypedefDeclaredVectorsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  typedef logic [7:0] B;\n"
      "  typedef logic [1:0][3:0] T;\n"
      "  typedef int W;\n"
      "  B y; T x; W w;\n"
      "  logic [1:0] v; logic u;\n"
      "  initial begin\n"
      "    v = y[1:0]; u = y[4];\n"
      "    u = x[1][0]; v = x[0][3 -: 2];\n"
      "    u = w[31];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(SelectElaboration, SelectOfATypedefDeclaredScalarIsIllegal) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  typedef logic L;\n"
      "  L s;\n"
      "  logic u;\n"
      "  initial u = s[0];\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select or part-select of a scalar is illegal",
                            5, "11.5.1"));
}

TEST(PartSelectBoundsElaboration, ReversedPartSelectWithParametersReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t #(parameter W = 8);\n"
      "  localparam L = 0;\n"
      "  logic [W-1:0] v;\n"
      "  logic [7:0] u;\n"
      "  logic [3:0] y, z;\n"
      "  assign y = v[0:3];\n"
      "  assign z = u[L:3];\n"
      "endmodule\n",
      f);
  for (uint32_t line : {6u, 7u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "part-select's first index must address a more "
                              "significant bit than its second index",
                              line, "11.5.1"));
  }
}

TEST(PartSelectBoundsElaboration, BoundNamingAProceduresVariableReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic [7:0] v, y;\n"
      "  initial for (int i = 3; i < 4; i++) y = v[i:0];\n"
      "  initial begin\n"
      "    int k = 2;\n"
      "    y = v[k:0];\n"
      "  end\n"
      "  function automatic logic [7:0] f(int n);\n"
      "    return v[n:0];\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  for (uint32_t line : {3u, 6u, 9u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "non-indexed part-select bounds shall be "
                              "constant expressions",
                              line, "11.5.1"));
  }
}

TEST(PartSelectBoundsElaboration, BoundNamingABlocksConstantIsNotReported) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    typedef enum {A = 3} e_t;\n"
      "    let w = 2;\n"
      "    int k;\n"
      "    x[A:0] = 0;\n"
      "    x[w:0] = 0;\n"
      "    x[k:0] = 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  for (uint32_t line : {7u, 8u}) {
    EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                               "non-indexed part-select bounds shall be "
                               "constant expressions",
                               line, "11.5.1"));
  }
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "non-indexed part-select bounds shall be "
                            "constant expressions",
                            9, "11.5.1"));
}

TEST(SelectElaboration, SelectsInsideGenerateBlocksAreChecked) {
  EXPECT_TRUE(RejectedInsideGenerateBlocks(
      {"", "logic s; wire y;", "assign y = s[0];"},
      "bit-select or part-select of a scalar is illegal", "11.5.1"));
  EXPECT_TRUE(RejectedInsideGenerateBlocks(
      {"", "logic s, y;", "initial y = s[0];"},
      "bit-select or part-select of a scalar is illegal", "11.5.1"));
  EXPECT_TRUE(RejectedInsideGenerateBlocks(
      {"", "logic [7:0] v; wire [1:0] y;", "assign y = v[0+:0];"},
      "indexed part-select width must be a positive constant", "11.5.1"));
  EXPECT_TRUE(RejectedInsideGenerateBlocks(
      {"", "logic [7:0] v; logic [1:0] y;", "initial y = v[0+:0];"},
      "indexed part-select width must be a positive constant", "11.5.1"));
  EXPECT_TRUE(AcceptedInsideGenerateBlocks(
      {"", "logic [7:0] v; logic [1:0] y;", "initial y = v[0+:2];"}));
  {
    ElabFixture f;
    ElaborateSrc(
        "module m;\n"
        "  logic [7:0] v;\n"
        "  logic [1:0] y;\n"
        "  for (genvar i = 0; i < 2; i++) begin : g\n"
        "    initial y = v[0+:i];\n"
        "  end\n"
        "endmodule\n",
        f);
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "indexed part-select width must be a positive constant", 5, "11.5.1"));
  }
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] v;\n"
             "  logic [1:0] y;\n"
             "  for (genvar i = 1; i < 3; i++) begin : g\n"
             "    initial y = v[0+:i];\n"
             "  end\n"
             "endmodule\n"));
  {
    ElabFixture f;
    ElaborateSrc(
        "module m;\n"
        "  logic [7:0] v;\n"
        "  logic [1:0] y;\n"
        "  if (1) begin : g\n"
        "    localparam int W = 0;\n"
        "    initial y = v[0+:W];\n"
        "  end\n"
        "endmodule\n",
        f);
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "indexed part-select width must be a positive constant", 6, "11.5.1"));
  }
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [7:0] v;\n"
             "  logic [1:0] y;\n"
             "  if (1) begin : g\n"
             "    localparam int W = 2;\n"
             "    initial y = v[0+:W];\n"
             "  end\n"
             "endmodule\n"));
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic s;\n"
             "  logic y;\n"
             "  if (1) begin : g\n"
             "    logic [3:0] s;\n"
             "    initial y = s[0];\n"
             "  end\n"
             "endmodule\n"));
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  logic [3:0] s;\n"
             "  logic y;\n"
             "  if (1) begin : g1\n"
             "    logic s;\n"
             "  end\n"
             "  if (1) begin : g2\n"
             "    initial y = s[0];\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
