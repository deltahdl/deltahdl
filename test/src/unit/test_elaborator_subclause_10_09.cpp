#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <string_view>

#include "fixture_elaborator.h"
#include "fixture_simulator.h"
#include "helpers_generate_block_items.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(AssignmentPatternElaboration, ReplicationPatternElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0][7:0] x;\n"
      "  initial begin\n"
      "    x = '{4{8'hAB}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssignmentPatternElaboration, IntegerAtomTypePatternElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int x;\n"
      "  initial begin\n"
      "    x = int'{42};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssignmentPatternElaboration, ConstantAssignmentPatternElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  localparam int arr [3] = '{10, 20, 30};\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssignmentPatternElaboration, TypeReferencePatternElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [1:0][7:0] x;\n"
      "  initial x = type(x)'{8'd1, 8'd2};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssignmentPatternElaboration, LhsPositionalPatternElaborates) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  initial '{a, b} = 16'hABCD;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssignmentPatternElaboration, TypedPatternExpressionInPortIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module sub(input int a);\n"
      "endmodule\n"
      "module top;\n"
      "  sub u(.a(int'{42}));\n"
      "endmodule\n",
      f);
  EXPECT_EQ(FindDiag(f, "an assignment pattern cannot be connected"), nullptr);
}

TEST(AssignmentPatternElaboration, ErrorLhsNamedKeys) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  logic [7:0] x, y;\n"
      "  initial '{a: x, b: y} = p;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "LHS assignment pattern shall use positional notation only", 5, "10.9"));
}

TEST(AssignmentPatternElaboration, ErrorNonConstantInConstantPattern) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int x;\n"
      "  localparam int arr [3] = '{x, 2, 3};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "localparam 'arr' initializer is not a constant expression",
                    3, "6.20.4"));
}

TEST(AssignmentPatternElaboration, ConstantPatternWithParameterMembers) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter int A = 10;\n"
      "  parameter int B = 20;\n"
      "  localparam int arr [2] = '{A, B};\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssignmentPatternElaboration, ConstantPatternWithLocalparamMembers) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  localparam int A = 5;\n"
      "  localparam int arr [2] = '{A, A};\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'd0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssignmentPatternElaboration, ExpressionUsableOutsideAssignmentSide) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int x;\n"
      "  initial x = int'{40} + 2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssignmentPatternElaboration, ErrorTypedLhsPatternNamedKeys) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } pair_t;\n"
      "  pair_t p;\n"
      "  logic [7:0] x, y;\n"
      "  initial pair_t'{a: x, b: y} = p;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "LHS assignment pattern shall use positional notation only", 5, "10.9"));
}

TEST(AssignmentPatternElaboration, ErrorLhsPatternBitCountMismatch) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  initial '{a, b} = 32'hDEADBEEF;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "LHS assignment pattern needs 16 bits but RHS supplies 32 bits", 3,
      "10.9"));
}

TEST(AssignmentPatternElaboration, AKeyedLhsPatternInsideForkIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x, y;\n"
      "  logic [15:0] p;\n"
      "  initial fork\n"
      "    '{0: x, 1: y} = p;\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "LHS assignment pattern shall use positional notation only", 5, "10.9"));
}

TEST(AssignmentPatternElaboration,
     AKeyedLhsPatternInAForInitializerIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x, y;\n"
      "  logic [15:0] p;\n"
      "  integer i;\n"
      "  initial for ('{0: x, 1: y} = p; i < 2; i = i + 1) begin end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "LHS assignment pattern shall use positional notation only", 5, "10.9"));
}

TEST(AssignmentPatternElaboration, AKeyedLhsPatternInAForStepIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x, y;\n"
      "  logic [15:0] p;\n"
      "  integer i;\n"
      "  initial for (i = 0; i < 2; '{0: x, 1: y} = p) begin end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "LHS assignment pattern shall use positional notation only", 5, "10.9"));
}

TEST(AssignmentPatternElaboration,
     AKeyedLhsPatternInAnAssertionPassStatementIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x, y;\n"
      "  logic [15:0] p;\n"
      "  logic ok;\n"
      "  initial assert (ok) '{0: x, 1: y} = p;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "LHS assignment pattern shall use positional notation only", 5, "10.9"));
}

TEST(AssignmentPatternElaboration,
     AKeyedLhsPatternInAnAssertionFailStatementIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x, y;\n"
      "  logic [15:0] p;\n"
      "  logic ok;\n"
      "  initial assert (ok) else '{0: x, 1: y} = p;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "LHS assignment pattern shall use positional notation only", 5, "10.9"));
}

TEST(AssignmentPatternElaboration, AKeyedLhsPatternInARandcaseItemIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x, y;\n"
      "  logic [15:0] p;\n"
      "  initial randcase 1: '{0: x, 1: y} = p; endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "LHS assignment pattern shall use positional notation only", 4, "10.9"));
}

TEST(AssignmentPatternElaboration,
     AKeyedLhsPatternInARandsequenceCodeBlockIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x, y;\n"
      "  logic [15:0] p;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { '{0: x, 1: y} = p; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "LHS assignment pattern shall use positional notation only", 6, "10.9"));
}

TEST(AssignmentPatternElaboration,
     AKeyedLhsPatternInARandsequenceWeightCodeBlockIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x, y;\n"
      "  logic [15:0] p;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : alt := 1 { '{0: x, 1: y} = p; };\n"
      "      alt : { i = 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "LHS assignment pattern shall use positional notation only", 7, "10.9"));
}

TEST(AssignmentPatternElaboration, AMissizedLhsPatternInsideForkIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  initial fork\n"
      "    '{a, b} = 32'hDEADBEEF;\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "LHS assignment pattern needs 16 bits but RHS supplies 32 bits", 4,
      "10.9"));
}

TEST(AssignmentPatternElaboration,
     AMissizedLhsPatternInAForInitializerIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  integer i;\n"
      "  initial for ('{a, b} = 32'hDEADBEEF; i < 2; i = i + 1) begin end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "LHS assignment pattern needs 16 bits but RHS supplies 32 bits", 4,
      "10.9"));
}

TEST(AssignmentPatternElaboration, AMissizedLhsPatternInAForStepIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  integer i;\n"
      "  initial for (i = 0; i < 2; '{a, b} = 32'hDEADBEEF) begin end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "LHS assignment pattern needs 16 bits but RHS supplies 32 bits", 4,
      "10.9"));
}

TEST(AssignmentPatternElaboration,
     AMissizedLhsPatternInAnAssertionPassStatementIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  logic ok;\n"
      "  initial assert (ok) '{a, b} = 32'hDEADBEEF;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "LHS assignment pattern needs 16 bits but RHS supplies 32 bits", 4,
      "10.9"));
}

TEST(AssignmentPatternElaboration,
     AMissizedLhsPatternInAnAssertionFailStatementIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  logic ok;\n"
      "  initial assert (ok) else '{a, b} = 32'hDEADBEEF;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "LHS assignment pattern needs 16 bits but RHS supplies 32 bits", 4,
      "10.9"));
}

TEST(AssignmentPatternElaboration,
     AMissizedLhsPatternInARandcaseItemIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  initial randcase 1: '{a, b} = 32'hDEADBEEF; endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "LHS assignment pattern needs 16 bits but RHS supplies 32 bits", 3,
      "10.9"));
}

TEST(AssignmentPatternElaboration,
     AMissizedLhsPatternInARandsequenceCodeBlockIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { '{a, b} = 32'hDEADBEEF; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "LHS assignment pattern needs 16 bits but RHS supplies 32 bits", 5,
      "10.9"));
}

TEST(AssignmentPatternElaboration,
     AMissizedLhsPatternInARandsequenceWeightCodeBlockIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : alt := 1 { '{a, b} = 32'hDEADBEEF; };\n"
      "      alt : { i = 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "LHS assignment pattern needs 16 bits but RHS supplies 32 bits", 6,
      "10.9"));
}

TEST(AssignmentPatternElaboration, LhsPatternRulesReachFunctionBodies) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  function void fn();\n"
      "    '{0: a, 1: b} = 16'h0;\n"
      "    '{a, b} = 32'h0;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "LHS assignment pattern shall use positional notation only", 4, "10.9"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "LHS assignment pattern needs 16 bits but RHS supplies 32 bits", 5,
      "10.9"));
}

TEST(AssignmentPatternElaboration, KeyedLhsPatternInContAssignIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  assign '{0: a, 1: b} = 16'h0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "LHS assignment pattern shall use positional notation only", 3, "10.9"));
}

TEST(AssignmentPatternElaboration, UntypedPatternOnBothSidesIsError) {
  ElabFixture f;
  ElaborateSrc(
      "typedef struct packed { logic [7:0] x, y; } xy_t;\n"
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  initial '{a, b} = '{8'd1, 8'd2};\n"
      "  initial xy_t'{a, b} = '{8'd1, 8'd2};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an assignment between two untyped assignment "
                            "patterns gives neither a type",
                            4, "10.9"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "an assignment between two untyped assignment "
                             "patterns gives neither a type",
                             5, "10.9"));
}

TEST(AssignmentPatternElaboration, LhsPatternBitCountAgainstNamedRhs) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b; logic [31:0] p; logic [3:0] mem [2];\n"
      "  function logic [23:0] g(); return 0; endfunction\n"
      "  initial begin\n"
      "    '{a, b} = p;\n"
      "    '{a, b} = p[23:0];\n"
      "    '{a, b} = g();\n"
      "    '{a, b} = p[15:0];\n"
      "    '{a, b} = mem[1];\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "LHS assignment pattern needs 16 bits but RHS supplies 32 bits", 5,
      "10.9"));
  for (uint32_t line : {6u, 7u}) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(),
        "LHS assignment pattern needs 16 bits but RHS supplies 24 bits", line,
        "10.9"));
  }
  EXPECT_EQ(FindDiag(f, "but RHS supplies 4 bits"), nullptr);
}

TEST(AssignmentPatternElaboration, LhsPatternBitCountAgainstAnUnpackedArray) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef byte U[3];\n"
      "  U A; byte a, b, c; byte sq [2][2]; byte q[$];\n"
      "  initial begin\n"
      "    U'{a, b, c} = A;\n"
      "    '{a, b} = A;\n"
      "    '{a, b, c} = sq;\n"
      "    '{a, b, c} = q;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "LHS assignment pattern needs 16 bits but RHS supplies 24 bits", 6,
      "10.9"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "LHS assignment pattern needs 24 bits but RHS supplies 32 bits", 7,
      "10.9"));
  for (uint32_t line : {5u, 8u}) {
    EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                               "LHS assignment pattern needs", line, "10.9"));
  }
}

TEST(AssignmentPatternElaboration, TypedLhsPatternItemWidthMismatchIsError) {
  ElabFixture f;
  ElaborateSrc(
      "typedef struct packed { logic [3:0] x; logic [11:0] y; } pair_t;\n"
      "module m;\n"
      "  logic [11:0] y4; logic [3:0] x12;\n"
      "  initial pair_t'{y4, x12} = 16'h0;\n"
      "  initial pair_t'{x12, y4} = 16'h0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "LHS assignment pattern item has 12 bits but "
                            "member 'x' of its type has 4 bits",
                            4, "10.9"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "LHS assignment pattern item has", 5, "10.9"));
}

TEST(AssignmentPatternElaboration,
     UntypedPatternInNonAssignmentPositionIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, v; logic [15:0] c;\n"
      "  initial begin\n"
      "    if ('{1}) a = 1;\n"
      "    a = '{1} ? 8'd1 : 8'd2;\n"
      "    c = {'{8'd1}, a};\n"
      "    a = v['{0}];\n"
      "  end\n"
      "endmodule\n",
      f);
  for (uint32_t line : {4u, 5u, 6u, 7u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "assignment pattern without a type prefix "
                              "outside an assignment-like context",
                              line, "10.9"));
  }
}

TEST(AssignmentPatternElaboration, NestedKeyedPatternInATargetIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef struct packed { logic [3:0] a; logic [3:0] b; } pair_t;\n"
      "  typedef struct packed { pair_t l; pair_t r; } quad_t;\n"
      "  pair_t q, q2;\n"
      "  quad_t w;\n"
      "  logic [3:0] x, y, x2, y2;\n"
      "  initial begin\n"
      "    {pair_t'{a: x, b: y}, q} = w;\n"
      "    quad_t'{pair_t'{a: x, b: y}, q} = w;\n"
      "    {pair_t'{x, y}, q} = w;\n"
      "  end\n"
      "  assign {pair_t'{a: x2, b: y2}, q2} = w;\n"
      "endmodule\n",
      f);
  constexpr std::string_view kMessage =
      "LHS assignment pattern shall use positional notation only";
  for (uint32_t line : {8u, 9u, 12u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kMessage, line, "10.9"))
        << line;
  }
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kMessage, 10, "10.9"));
}

TEST(AssignmentPatternElaboration, LhsPatternInsideGenerateBlocksIsPositional) {
  EXPECT_TRUE(RejectedInsideGenerateBlocks(
      {"", "logic a, b;", "initial '{x: a, y: b} = 2'b0;"},
      "LHS assignment pattern shall use positional notation only", "10.9"));
  EXPECT_TRUE(RejectedInsideGenerateBlocks(
      {"", "wire a, b;", "assign '{x: a, y: b} = 2'b0;"},
      "LHS assignment pattern shall use positional notation only", "10.9"));
  EXPECT_TRUE(AcceptedInsideGenerateBlocks(
      {"", "logic a, b;", "initial '{a, b} = 2'b0;"}));
}

}  // namespace
