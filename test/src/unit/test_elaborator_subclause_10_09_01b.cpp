#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ArrayPatternElaboration, TypedPatternCountedAgainstItsPrefixType) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef logic [3:0] nib_t;\n"
      "  typedef int pair_t [2];\n"
      "  logic [15:0] x;\n"
      "  nib_t n;\n"
      "  int p [2];\n"
      "  assign x = type(x)'{8'd1, 8'd2};\n"
      "  initial n = nib_t'{1'b1, 1'b0};\n"
      "  initial p = pair_t'{1, 2, 3};\n"
      "  logic [23:0] y = type(logic [2:0][7:0])'{8'd1, 8'd2};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 2 elements, but array "
                            "dimension requires 16",
                            7, "10.9.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 2 elements, but array "
                            "dimension requires 4",
                            8, "10.9.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 3 elements, but array "
                            "dimension requires 2",
                            9, "10.9.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 2 elements, but array "
                            "dimension requires 3",
                            10, "10.9.1"));
  EXPECT_EQ(f.diag.ErrorCount(), 4u);
}

TEST(ArrayPatternElaboration, TypedPatternCountedOutsideAssignmentLikeContext) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef logic [1:0][7:0] w_t;\n"
      "  logic [15:0] r;\n"
      "  function automatic logic [15:0] f();\n"
      "    return w_t'{8'd1, 8'd2, 8'd3};\n"
      "  endfunction\n"
      "  initial r = w_t'{8'd1, 8'd2} + w_t'{8'd3};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 3 elements, but array "
                            "dimension requires 2",
                            5, "10.9.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 1 elements, but array "
                            "dimension requires 2",
                            7, "10.9.1"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

TEST(ArrayPatternElaboration, TypedPatternMatchingItsPrefixTypeOk) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  typedef logic [3:0] nib_t;\n"
             "  typedef int pair_t [2];\n"
             "  logic [1:0][7:0] x;\n"
             "  nib_t n;\n"
             "  int p [2];\n"
             "  logic [3:0] h;\n"
             "  parameter logic [1:0] P = 2'b01;\n"
             "  assign x = type(x)'{8'd1, 8'd2};\n"
             "  initial h = type(P)'{1'b1, 1'b0};\n"
             "  initial n = nib_t'{4{1'b1}};\n"
             "  initial p = pair_t'{1, 2};\n"
             "  initial begin\n"
             "    logic [1:0] h;\n"
             "    h = type(h)'{1'b1, 1'b0};\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ArrayPatternElaboration, TypedPatternWithPackageScopedPrefixCounted) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  typedef logic [3:0] T;\n"
      "  typedef int A [3];\n"
      "endpackage\n"
      "module m;\n"
      "  logic [3:0] y;\n"
      "  int a [3];\n"
      "  initial y = p::T'{1'b1, 1'b0};\n"
      "  initial a = p::A'{1, 2};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 2 elements, but array "
                            "dimension requires 4",
                            8, "10.9.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 2 elements, but array "
                            "dimension requires 3",
                            9, "10.9.1"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

TEST(ArrayPatternElaboration, PackageScopedPrefixIsNoVariableOfThatName) {
  EXPECT_TRUE(
      ElabOk("package p;\n"
             "  typedef logic [1:0] T;\n"
             "endpackage\n"
             "module m;\n"
             "  logic [3:0] p;\n"
             "  logic [1:0] y;\n"
             "  initial y = p::T'{1'b1, 1'b0};\n"
             "endmodule\n"));
}

TEST(ArrayPatternElaboration, TypedPatternThroughTypedefChainCounted) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef int a_t [3];\n"
      "  typedef a_t b_t;\n"
      "  typedef b_t c_t;\n"
      "  int v [3];\n"
      "  initial v = b_t'{1, 2};\n"
      "  initial v = c_t'{1, 2, 3, 4};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 2 elements, but array "
                            "dimension requires 3",
                            6, "10.9.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 4 elements, but array "
                            "dimension requires 3",
                            7, "10.9.1"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

TEST(ArrayPatternElaboration, TypeReferenceToBlockOrFormalCounted) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [1:0] x;\n"
      "  initial begin\n"
      "    logic [3:0] x;\n"
      "    x = type(x)'{1'b1, 1'b0};\n"
      "  end\n"
      "  function automatic logic [3:0] f(input logic [3:0] a);\n"
      "    return type(a)'{1'b1, 1'b0, 1'b1};\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 2 elements, but array "
                            "dimension requires 4",
                            5, "10.9.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 3 elements, but array "
                            "dimension requires 4",
                            8, "10.9.1"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

TEST(ArrayPatternElaboration, ResolvedPrefixTypesMatchingOk) {
  EXPECT_TRUE(
      ElabOk("package p;\n"
             "  typedef logic [3:0] T;\n"
             "  typedef int A [3];\n"
             "endpackage\n"
             "module m;\n"
             "  typedef int a_t [3];\n"
             "  typedef a_t b_t;\n"
             "  logic [3:0] y;\n"
             "  int v [3];\n"
             "  initial y = p::T'{1'b1, 1'b0, 1'b1, 1'b0};\n"
             "  initial v = p::A'{1, 2, 3};\n"
             "  initial v = b_t'{1, 2, 3};\n"
             "  function automatic logic [3:0] f(input logic [3:0] a);\n"
             "    return type(a)'{4{1'b1}};\n"
             "  endfunction\n"
             "endmodule\n"));
}

TEST(ArrayPatternElaboration, TypeReferenceToArrayTypedefCounted) {
  ElabFixture f;
  ElaborateSrc(
      "package p;\n"
      "  typedef int A [3];\n"
      "endpackage\n"
      "module m;\n"
      "  typedef int a_t [3];\n"
      "  int v [3];\n"
      "  initial v = type(a_t)'{1, 2};\n"
      "  initial v = type(p::A)'{1, 2, 3, 4};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 2 elements, but array "
                            "dimension requires 3",
                            7, "10.9.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 4 elements, but array "
                            "dimension requires 3",
                            8, "10.9.1"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

TEST(ArrayPatternElaboration, TypeReferenceToTypedefMatchingOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  typedef logic [3:0] T;\n"
             "endclass\n"
             "module m;\n"
             "  typedef logic [3:0] nib_t;\n"
             "  typedef int a_t [3];\n"
             "  int v [3];\n"
             "  logic [1:0][3:0] w;\n"
             "  logic [3:0] y;\n"
             "  initial v = type(a_t)'{1, 2, 3};\n"
             "  initial w = type(nib_t [1:0])'{4'h1, 4'h2};\n"
             "  initial y = type(C::T)'{4{1'b1}};\n"
             "endmodule\n"));
}

TEST(ArrayPatternElaboration, TypedPatternWithClassScopedPrefixCounted) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "  typedef int A [3];\n"
      "endclass\n"
      "module m;\n"
      "  int v [3];\n"
      "  initial v = C::A'{1, 2};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "assignment pattern has 2 elements, but array "
                            "dimension requires 3",
                            6, "10.9.1"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

TEST(ArrayPatternElaboration, TypedPatternWithClassScopedPrefixMatchingOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  typedef int A [3];\n"
             "endclass\n"
             "module m;\n"
             "  int v [3];\n"
             "  initial v = C::A'{1, 2, 3};\n"
             "endmodule\n"));
}

}  // namespace
