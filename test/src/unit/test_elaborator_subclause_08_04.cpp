#include <gtest/gtest.h>

#include <initializer_list>

#include "fixture_elaborator.h"
#include "helpers_generate_block_items.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ClassObjectElaboration, NullLiteralElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    automatic int x;\n"
      "    x = null;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ClassObjectElaboration, ClassHandleAssignNull) {
  EXPECT_TRUE(
      ElabOk("class C; endclass\n"
             "module m;\n"
             "  C c;\n"
             "  initial c = null;\n"
             "endmodule\n"));
}

TEST(ClassObjectElaboration, ClassHandleAssignHandle) {
  EXPECT_TRUE(
      ElabOk("class C; endclass\n"
             "module m;\n"
             "  C a, b;\n"
             "  initial a = b;\n"
             "endmodule\n"));
}

TEST(ClassObjectElaboration, ClassHandleEqualityAllowed) {
  EXPECT_TRUE(
      ElabOk("class C; endclass\n"
             "module m;\n"
             "  C a, b;\n"
             "  initial begin\n"
             "    automatic int r;\n"
             "    r = (a == b);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassObjectElaboration, ClassHandleCaseEqualityAllowed) {
  EXPECT_TRUE(
      ElabOk("class C; endclass\n"
             "module m;\n"
             "  C a, b;\n"
             "  initial begin\n"
             "    automatic int r;\n"
             "    r = (a === b);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassObjectElaboration, ClassHandleInequalityAllowed) {
  EXPECT_TRUE(
      ElabOk("class C; endclass\n"
             "module m;\n"
             "  C a;\n"
             "  initial begin\n"
             "    automatic int r;\n"
             "    r = (a != null);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassObjectElaboration, ClassHandleConditionalAllowed) {
  EXPECT_TRUE(
      ElabOk("class C; endclass\n"
             "module m;\n"
             "  C a, b, c;\n"
             "  initial begin\n"
             "    automatic int sel;\n"
             "    a = sel ? b : c;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassObjectElaboration, ClassHandleArithmeticError) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C a;\n"
      "  initial begin\n"
      "    automatic int r;\n"
      "    r = a + 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on class object handles",
                            6, "8.4"));
}

TEST(ClassObjectElaboration, ArithmeticOnAnObjectHandleNames8_4) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C a;\n"
      "  initial begin\n"
      "    automatic int r;\n"
      "    r = a + 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on class object handles",
                            6, "8.4"));
}

TEST(ClassObjectElaboration, ClassHandleRelationalError) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C a, b;\n"
      "  initial begin\n"
      "    automatic int r;\n"
      "    r = a < b;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on class object handles",
                            6, "8.4"));
}

TEST(ClassObjectElaboration, ClassHandleBitwiseError) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C a, b;\n"
      "  initial begin\n"
      "    automatic int r;\n"
      "    r = a & b;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on class object handles",
                            6, "8.4"));
}

TEST(ClassObjectElaboration, ClassHandleLogicalNegationError) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C a;\n"
      "  initial begin\n"
      "    automatic int r;\n"
      "    r = !a;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on class object handles",
                            6, "8.4"));
}

TEST(ClassObjectElaboration, ClassHandleIncrementError) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C a;\n"
      "  initial a++;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on class object handles",
                            4, "8.4"));
}

TEST(ClassObjectElaboration, ClassHandleShiftError) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C a;\n"
      "  initial begin\n"
      "    automatic int r;\n"
      "    r = a << 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on class object handles",
                            6, "8.4"));
}

TEST(ClassObjectElaboration, ClassHandleCompoundAssignError) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C a;\n"
      "  initial a += 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on class object handles",
                            4, "8.4"));
}

TEST(ClassObjectElaboration, ClassHandleBitSelectError) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C a;\n"
      "  initial begin\n"
      "    automatic int r;\n"
      "    r = a[0];\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select on class object handle is illegal", 6,
                            "8.4"));
}

TEST(ClassObjectElaboration, ClassHandleContAssignError) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C a, b;\n"
      "  assign a = b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "class object handle cannot be used in continuous assignment", 4,
      "10.3"));
}

TEST(ClassObjectElaboration, ClassVariableElaboratesOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class Pkt;\n"
      "  int data;\n"
      "endclass\n"
      "module top;\n"
      "  Pkt p;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ClassObjectElaboration, ClassHandleAssignmentOk) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  int data;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    Packet p1, p2;\n"
             "    p1 = new;\n"
             "    p2 = p1;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassObjectElaboration, ClassHandleCaseInequalityAllowed) {
  EXPECT_TRUE(
      ElabOk("class C; endclass\n"
             "module m;\n"
             "  C a, b;\n"
             "  initial begin\n"
             "    automatic int r;\n"
             "    r = (a !== b);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassObjectElaboration, ClassHandleEqualityWithNullAllowed) {
  EXPECT_TRUE(
      ElabOk("class C; endclass\n"
             "module m;\n"
             "  C a;\n"
             "  initial begin\n"
             "    automatic int r;\n"
             "    r = (a == null);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassObjectElaboration, ClassHandleDecrementError) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C a;\n"
      "  initial a--;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on class object handles",
                            4, "8.4"));
}

TEST(ClassObjectElaboration, ClassHandleCompareCompatibleOk) {
  EXPECT_TRUE(
      ElabOk("class Base; endclass\n"
             "class Child extends Base; endclass\n"
             "module m;\n"
             "  Base b;\n"
             "  Child c;\n"
             "  initial begin\n"
             "    automatic int r;\n"
             "    r = (b == c);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassObjectElaboration, ClassHandleCompareIncompatibleError) {
  ElabFixture f;
  ElaborateSrc(
      "class A; endclass\n"
      "class B; endclass\n"
      "module m;\n"
      "  A a;\n"
      "  B b;\n"
      "  initial begin\n"
      "    automatic int r;\n"
      "    r = (a == b);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "class handle comparison requires assignment compatible types", 8,
      "11.4.5"));
}

TEST(ClassObjectElaboration, ClassHandleAssignCompatibleOk) {
  EXPECT_TRUE(
      ElabOk("class Base; endclass\n"
             "class Child extends Base; endclass\n"
             "module m;\n"
             "  Base b;\n"
             "  Child c;\n"
             "  initial b = c;\n"
             "endmodule\n"));
}

TEST(ClassObjectElaboration, ClassHandleAssignIncompatibleError) {
  ElabFixture f;
  ElaborateSrc(
      "class A; endclass\n"
      "class B; endclass\n"
      "module m;\n"
      "  A a;\n"
      "  B b;\n"
      "  initial a = b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "class handle assignment requires assignment compatible types", 6,
      "8.4"));
}

TEST(ClassObjectElaboration, ClassHandleCastToNonClassTypeError) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C a;\n"
      "  initial begin\n"
      "    automatic int r;\n"
      "    r = int'(a);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot cast class object handle to a non-class "
                            "type",
                            6, "8.4"));
}

TEST(ClassObjectElaboration, NonClassValueCastToClassTypeError) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C a;\n"
      "  initial a = C'(5);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot cast non-class value to a class type", 4,
                            "8.4"));
}

TEST(ClassObjectElaboration, ClassHandleAssignParentToChildError) {
  ElabFixture f;
  ElaborateSrc(
      "class Base; endclass\n"
      "class Child extends Base; endclass\n"
      "module m;\n"
      "  Base b;\n"
      "  Child c;\n"
      "  initial c = b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "class handle assignment requires assignment compatible types", 6,
      "8.4"));
}

TEST(ClassObjectElaboration, ArithmeticOnAHandleInAForkArmIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C a;\n"
      "  initial begin\n"
      "    automatic int r;\n"
      "    fork\n"
      "      r = a + 1;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on class object handles",
                            7, "8.4"));
}

TEST(ClassObjectElaboration,
     ArithmeticOnAHandleInAForInitializationIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C a;\n"
      "  initial begin\n"
      "    automatic int r;\n"
      "    for (r = a + 1; r < 2; r = r + 1) ;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on class object handles",
                            6, "8.4"));
}

TEST(ClassObjectElaboration, ArithmeticOnAHandleInAForStepIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C a;\n"
      "  initial begin\n"
      "    automatic int r;\n"
      "    for (r = 0; r < 2; r = a + 1) ;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on class object handles",
                            6, "8.4"));
}

TEST(ClassObjectElaboration,
     ArithmeticOnAHandleInAnAssertionPassStmtIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C a;\n"
      "  initial begin\n"
      "    automatic int r;\n"
      "    assert (1) r = a + 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on class object handles",
                            6, "8.4"));
}

TEST(ClassObjectElaboration,
     ArithmeticOnAHandleInAnAssertionFailStmtIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C a;\n"
      "  initial begin\n"
      "    automatic int r;\n"
      "    assert (1) else r = a + 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on class object handles",
                            6, "8.4"));
}

TEST(ClassObjectElaboration, ArithmeticOnAHandleInARandcaseItemIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C a;\n"
      "  initial begin\n"
      "    automatic int r;\n"
      "    randcase\n"
      "      1 : r = a + 1;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on class object handles",
                            7, "8.4"));
}

TEST(ClassObjectElaboration,
     ArithmeticOnAHandleInARandsequenceCodeBlockIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C a;\n"
      "  initial begin\n"
      "    automatic int r;\n"
      "    randsequence(main)\n"
      "      main : { r = a + 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on class object handles",
                            7, "8.4"));
}

TEST(ClassObjectElaboration,
     ArithmeticOnAHandleInARandsequenceWeightCodeBlockIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C a;\n"
      "  initial begin\n"
      "    automatic int r;\n"
      "    randsequence(main)\n"
      "      main : alt := 5 { r = a + 1; };\n"
      "      alt : { ; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on class object handles",
                            7, "8.4"));
}

TEST(ClassObjectElaboration, ElementSelectOfAnArrayOfHandlesIsNoBitSelect) {
  ElabFixture f;
  ElaborateSrc(
      "class C; int v; endclass\n"
      "module m;\n"
      "  C h[string];\n"
      "  C a[2];\n"
      "  int r;\n"
      "  initial begin\n"
      "    r = h[\"a\"].v + a[1].v;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "bit-select on class object handle is illegal", 7,
                             "8.4"));
}

TEST(ClassObjectElaboration,
     ElementSelectOfABlockDeclaredArrayOfHandlesIsNoBitSelect) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "class C; int v = 7; endclass\n"
      "module m;\n"
      "  int r;\n"
      "  initial begin\n"
      "    C arr[2];\n"
      "    C d[];\n"
      "    arr[1] = new;\n"
      "    d = new[2];\n"
      "    d[0] = new;\n"
      "    r = arr[1].v * 10 + d[0].v;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ClassObjectElaboration, BitSelectOfABlockDeclaredHandleIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    automatic int r;\n"
      "    C h;\n"
      "    r = h[0];\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select on class object handle is illegal", 6,
                            "8.4"));
}

TEST(ClassObjectElaboration,
     HandleOperationsAreCheckedInSubroutinesAndMethods) {
  ElabFixture f;
  ElabOk(
      "class C; endclass\n"
      "class D;\n"
      "  C c;\n"
      "  C cs[2];\n"
      "  function void f(); int x; x = c + 1; x = cs.size(); endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C h;\n"
      "  int r;\n"
      "  task t(); r = h + 1; endtask\n"
      "  function int g(C a); return a + 1; endfunction\n"
      "  function C k(); k = h; endfunction\n"
      "  initial r = h + 1;\n"
      "endmodule\n",
      f);
  for (const int kLine : {5, 10, 11, 13}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "operator is not allowed on class object handles",
                              kLine, "8.4"))
        << kLine;
  }
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), "class object handle", 12, "8.4"));
}

TEST(ClassObjectElaboration, AHandleYieldedByAnExpressionIsAHandle) {
  ElabFixture f;
  ElabOk(
      "class N; N next; int x; int arr[2]; endclass\n"
      "package q; int v; endpackage\n"
      "module m;\n"
      "  N h, hs[2];\n"
      "  int ia[2];\n"
      "  typedef struct { int f; } s_t;\n"
      "  s_t s;\n"
      "  function N make(); return null; endfunction\n"
      "  function int ifn(); return 0; endfunction\n"
      "  int r;\n"
      "  initial begin\n"
      "    r = h.next + 1;\n"
      "    r = hs[0] + 1;\n"
      "    r = make() + 1;\n"
      "    r = h.x + 1;\n"
      "    r = ia[0] + 1;\n"
      "    r = ifn() + 1;\n"
      "    r = s.f + 1;\n"
      "    r = q::v + 1;\n"
      "    r = h.arr + 1;\n"
      "    r = h.nosuch + 1;\n"
      "    r = h[0] + 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  const char* const kMessage =
      "operator is not allowed on class object handles";
  for (const int kLine : {12, 13, 14}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kMessage, kLine, "8.4"))
        << kLine;
  }
  for (const int kLine : {15, 16, 17, 18, 19, 20, 21}) {
    EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kMessage, kLine, "8.4"))
        << kLine;
  }
}

TEST(ClassObjectElaboration, AParenthesizedHandleAssignmentIsAHandle) {
  EXPECT_TRUE(
      ElabOk("class C; task run(); endtask endclass\n"
             "class D extends C; endclass\n"
             "module m;\n"
             "  C h; C g = new; D d = new; logic b;\n"
             "  initial begin\n"
             "    ((h = g)).run();\n"
             "    b = ((h = d)) == null;\n"
             "    b = ((h = null)) == null;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassObjectElaboration, AParenthesizedAssignmentToAHandleElement) {
  EXPECT_TRUE(
      ElabOk("class C; endclass\n"
             "module m;\n"
             "  typedef struct { C h; } s_t;\n"
             "  C arr [2]; C g = new; s_t s; logic b;\n"
             "  initial begin\n"
             "    b = ((arr[0] = g)) == null;\n"
             "    b = ((s.h = g)) == null;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassObjectElaboration, AParenthesizedIncompatibleHandleAssignment) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "class E; endclass\n"
      "module m;\n"
      "  C h; E e = new; logic b;\n"
      "  initial b = ((h = e)) == null;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "class handle assignment requires assignment compatible types", 5,
      "8.4"));
}

TEST(ClassObjectElaboration, AParenthesizedIntegralAssignmentToAHandle) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C h; logic b;\n"
      "  initial b = ((h = 1)) == null;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cannot assign non-class value to class object handle", 4, "8.4"));
}

TEST(ClassObjectElaboration, AParenthesizedHandleAssignmentToAnInt) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C g = new; int n; logic b;\n"
      "  initial b = ((n = g)) == 0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cannot assign class object handle to a non-class variable", 4, "8.4"));
}

TEST(ClassObjectElaboration, AParenthesizedCompoundAssignmentToAHandle) {
  ElabFixture f;
  ElaborateSrc(
      "class C; endclass\n"
      "module m;\n"
      "  C h; logic b;\n"
      "  initial b = ((h += 1)) == null;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on class object handles",
                            4, "8.4"));
}

TEST(ClassObjectElaboration,
     ClassHandleInContAssignInsideGenerateBlocksIsRejected) {
  EXPECT_TRUE(RejectedInsideGenerateBlocks(
      {"class C; endclass ", "C h; wire w;", "assign w = h;"},
      "class object handle cannot be used in continuous assignment", "10.3"));
  EXPECT_TRUE(AcceptedInsideGenerateBlocks(
      {"class C; endclass ", "C h; wire w;", "assign w = (h == null);"}));
}

}  // namespace
