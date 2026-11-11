#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <string_view>

#include "fixture_elaborator.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(UnpackedArrayConcatElaboration, EmptyConcatToVectorIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a; int q[$];\n"
      "  initial a = {};\n"
      "  initial q = {};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an empty concatenation, {}, is assigned only to "
                            "an unpacked array",
                            3, "10.10"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "an empty concatenation, {}, is assigned only to "
                             "an unpacked array",
                             4, "10.10"));
}

TEST(UnpackedArrayConcatElaboration, ScalarItemsElaborate) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int A[3];\n"
      "  initial A = {1, 2, 3};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
}

TEST(UnpackedArrayConcatElaboration, ArrayItemExpansion) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int A [0:1] = '{10, 20};\n"
      "  int B [0:1] = '{30, 40};\n"
      "  int C [0:3];\n"
      "  initial begin\n"
      "    C = {A, B};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* c0 = f.ctx.FindVariable("C[0]");
  auto* c1 = f.ctx.FindVariable("C[1]");
  auto* c2 = f.ctx.FindVariable("C[2]");
  auto* c3 = f.ctx.FindVariable("C[3]");
  ASSERT_NE(c0, nullptr);
  ASSERT_NE(c1, nullptr);
  ASSERT_NE(c2, nullptr);
  ASSERT_NE(c3, nullptr);
  EXPECT_EQ(c0->value.ToUint64(), 10u);
  EXPECT_EQ(c1->value.ToUint64(), 20u);
  EXPECT_EQ(c2->value.ToUint64(), 30u);
  EXPECT_EQ(c3->value.ToUint64(), 40u);
}

TEST(UnpackedArrayConcatElaboration, DynamicArrayDeclInitUnsizedLiterals) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  byte b[] = { 1, 2, 3, 4 };\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(UnpackedArrayConcatElaboration, QueueDeclInitUnsizedLiterals) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q[$] = { 10, 20, 30 };\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(UnpackedArrayConcatElaboration, FixedArrayDeclInitUnsizedLiterals) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int a[3] = { 4, 5, 6 };\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(UnpackedArrayConcatElaboration, PackedVectorDeclInitUnsizedStillErrors) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x = { 1, 2 };\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "unsized constant is not allowed in a concatenation", 2, "11.4.12"));
}

TEST(UnpackedArrayConcatElaboration, AssociativeArrayTargetError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int aa[string];\n"
      "  initial aa = {1, 2, 3};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unpacked array concatenation cannot target an "
                            "associative array",
                            3, "10.10"));
}

TEST(UnpackedArrayConcatElaboration, QueueTargetElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q[$];\n"
      "  initial q = {1, 2, 3};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(UnpackedArrayConcatElaboration, DynamicArrayTargetElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int d[];\n"
      "  initial d = {1, 2, 3};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(UnpackedArrayConcatElaboration, MixedItemsForFixedSizeTarget) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int A[1:3] = '{1, 2, 3};\n"
      "  int B[1:9];\n"
      "  initial B = {A, 4, 5, A, 6};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(UnpackedArrayConcatElaboration, NestedBraceItemRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int A3[1:3];\n"
      "  int A9[1:9];\n"
      "  initial A9 = {A3, {A3, A3}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "nested concatenation in unpacked array "
                            "concatenation is not self-determined",
                            4, "10.10.3"));
}

TEST(UnpackedArrayConcatElaboration, NullItemRejectedForIntElementType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q[$];\n"
      "  initial q = {1, null, 3};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "null is not a legal item in an unpacked array "
                            "concatenation for this target element type",
                            3, "10.10"));
}

TEST(UnpackedArrayConcatElaboration, NullItemAllowedForChandleElementType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  chandle q[$];\n"
      "  initial q = {null, null};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(UnpackedArrayConcatElaboration, NullItemAllowedForClassElementType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "endclass\n"
      "module m;\n"
      "  C q[$];\n"
      "  initial q = {null, null};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(UnpackedArrayConcatElaboration, NullItemAllowedForEventElementType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  event q[$];\n"
      "  initial q = {null, null};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(UnpackedArrayConcatElaboration,
     NullItemInArrayConcatInAForkArmNames10_10) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int q[$];\n"
      "  initial begin\n"
      "    fork\n"
      "      q = {1, null, 3};\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "null is not a legal item in an unpacked array", 5,
                            "10.10"));
}

TEST(UnpackedArrayConcatElaboration,
     NullItemInArrayConcatInAnAssertionPassStatementNames10_10) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int q[$];\n"
      "  logic ok;\n"
      "  initial assert (ok) q = {1, null, 3};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "null is not a legal item in an unpacked array", 4,
                            "10.10"));
}

TEST(UnpackedArrayConcatElaboration,
     NullItemInArrayConcatInAnAssertionFailStatementNames10_10) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int q[$];\n"
      "  logic ok;\n"
      "  initial assert (ok) else q = {1, null, 3};\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "null is not a legal item in an unpacked array", 4,
                            "10.10"));
}

TEST(UnpackedArrayConcatElaboration,
     NullItemInArrayConcatInARandcaseItemNames10_10) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int q[$];\n"
      "  initial randcase 1: q = {1, null, 3}; endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "null is not a legal item in an unpacked array", 3,
                            "10.10"));
}

TEST(UnpackedArrayConcatElaboration,
     NullItemInArrayConcatInARandsequenceCodeBlockNames10_10) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int q[$];\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { q = {1, null, 3}; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "null is not a legal item in an unpacked array", 5,
                            "10.10"));
}

TEST(UnpackedArrayConcatElaboration,
     NullItemInArrayConcatInAForLoopInitializationNames10_10) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int q[$];\n"
      "  int i;\n"
      "  initial for (q = {1, null, 3}; i < 1; i = i + 1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "null is not a legal item in an unpacked array", 4,
                            "10.10"));
}

TEST(UnpackedArrayConcatElaboration,
     NullItemInArrayConcatInAForLoopStepNames10_10) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int q[$];\n"
      "  int i;\n"
      "  initial for (i = 0; i < 1; q = {1, null, 3}) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "null is not a legal item in an unpacked array", 4,
                            "10.10"));
}

TEST(UnpackedArrayConcatElaboration, AssociativeArrayTargetInForkArmError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int aa[string];\n"
      "  initial fork\n"
      "    aa = {1, 2, 3};\n"
      "  join\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unpacked array concatenation cannot target an "
                            "associative array",
                            4, "10.10"));
}

TEST(UnpackedArrayConcatElaboration,
     AssociativeArrayTargetInForInitializerError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int aa[string];\n"
      "  int i;\n"
      "  initial\n"
      "    for (aa = {1, 2, 3}; i < 1; i = i + 1)\n"
      "      i = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unpacked array concatenation cannot target an "
                            "associative array",
                            5, "10.10"));
}

TEST(UnpackedArrayConcatElaboration, AssociativeArrayTargetInForStepError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int aa[string];\n"
      "  int i;\n"
      "  initial\n"
      "    for (i = 0; i < 1; aa = {1, 2, 3})\n"
      "      i = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unpacked array concatenation cannot target an "
                            "associative array",
                            5, "10.10"));
}

TEST(UnpackedArrayConcatElaboration,
     AssociativeArrayTargetInAssertionPassStatementError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int aa[string];\n"
      "  logic ok;\n"
      "  initial assert (ok) aa = {1, 2, 3};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unpacked array concatenation cannot target an "
                            "associative array",
                            4, "10.10"));
}

TEST(UnpackedArrayConcatElaboration,
     AssociativeArrayTargetInAssertionFailStatementError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int aa[string];\n"
      "  logic armed;\n"
      "  initial assert (armed) else aa = {1, 2, 3};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unpacked array concatenation cannot target an "
                            "associative array",
                            4, "10.10"));
}

TEST(UnpackedArrayConcatElaboration,
     AssociativeArrayTargetInRandcaseItemError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int aa[string];\n"
      "  initial randcase 1: aa = {1, 2, 3}; endcase\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unpacked array concatenation cannot target an "
                            "associative array",
                            3, "10.10"));
}

TEST(UnpackedArrayConcatElaboration,
     AssociativeArrayTargetInRandsequenceCodeBlockError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int aa[string];\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { aa = {1, 2, 3}; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unpacked array concatenation cannot target an "
                            "associative array",
                            5, "10.10"));
}

TEST(UnpackedArrayConcatElaboration, BlockLocalQueueTargetAdmitsUnsizedItems) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef int q_t[$];\n"
      "  initial begin\n"
      "    int r[$];\n"
      "    q_t u;\n"
      "    r = {1, 2};\n"
      "    u = {3, 4, 5};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(UnpackedArrayConcatElaboration,
     FunctionLocalQueueTargetAdmitsUnsizedItems) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function automatic int f();\n"
      "    int r[$];\n"
      "    r = {1, 2};\n"
      "    return r.size();\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(UnpackedArrayConcatElaboration, BlockLocalQueueHidesModuleScalar) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int s;\n"
      "  int q[$];\n"
      "  initial begin\n"
      "    begin int s[$]; s = {1, 2}; end\n"
      "    q = {1, 2};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(UnpackedArrayConcatElaboration, BlockLocalScalarHidesModuleQueueError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q[$];\n"
      "  initial begin\n"
      "    int q;\n"
      "    q = {1, 2};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unsized constant is not allowed in a "
                            "concatenation",
                            5, "11.4.12"));
}

TEST(UnpackedArrayConcatElaboration, AssocDeclInitializedByConcatIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int aa[string] = {1, 2};\n"
      "  initial begin int bb[int] = {3}; end\n"
      "  int d[] = {1, 2}; int q[$] = {1, 2};\n"
      "endmodule\n",
      f);
  for (uint32_t line : {2u, 3u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "unpacked array concatenation cannot target an "
                              "associative array",
                              line, "10.10"));
  }
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "unpacked array concatenation cannot target an "
                             "associative array",
                             4, "10.10"));
}

TEST(UnpackedArrayConcatElaboration, IncompatibleItemIsError) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C c; int q[$]; C cq[$];\n"
      "  initial q = {c};\n"
      "  int r[$] = {1, null};\n"
      "  initial cq = {c, null};\n"
      "endmodule\n",
      f, "m");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class handle 'c' is not assignment compatible", 4,
                            "10.10"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "null is not a legal item in an unpacked array "
                            "concatenation",
                            5, "10.10"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "is not", 6, "10.10"));
}

TEST(UnpackedArrayConcatElaboration,
     DISABLED_ConcatenationOfArraysAsAnEqualityOperandIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int A3[1:3], A6[1:6]; bit e;\n"
      "  initial e = ({A3, A3} == A6);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an unpacked array concatenation has no "
                            "self-determined type",
                            3, "10.10"));
}

TEST(UnpackedArrayConcatElaboration, EqualityOfTwoArraysIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int A6[1:6]; bit e;\n"
      "  initial e = (A6 == A6);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(UnpackedArrayConcatElaboration,
     DISABLED_AssociativeTargetInEveryOtherContextIsRejected) {
  ElabFixture f;
  ElaborateSrc(
      "typedef int aa_t [int];\n"
      "module s(input var int x[int]); endmodule\n"
      "module m #(parameter int P[int] = {1, 2}); endmodule\n"
      "module t;\n"
      "  int a = 3, b = 4;\n"
      "  function aa_t f(); return {a, b}; endfunction\n"
      "  function void g(input int x[int]); endfunction\n"
      "  s u(.x({a, b}));\n"
      "  m mm();\n"
      "  initial g({a, b});\n"
      "endmodule\n",
      f);
  constexpr std::string_view kMessage =
      "unpacked array concatenation cannot target an associative array";
  for (const int kLine : {3, 6, 8, 10}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kMessage, kLine, "10.10"))
        << kLine;
  }
}

}  // namespace
