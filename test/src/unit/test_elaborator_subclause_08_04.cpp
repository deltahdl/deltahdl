#include "fixture_elaborator.h"
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

// §8.4 lists every operator valid on an object handle -- equality, case
// equality, the conditional operator, and assignment of a compatible handle or
// of null -- and Table 8-1 records arithmetic on a handle as not allowed. The
// subclause on the report is what tells this rejection from an ordinary type
// mismatch in the same assignment, which is §10.8's rule and not §8.4's.
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

// The subclause asserted is the one the emission site passes, and
// Elaborator::ValidateClassHandleContAssign in
// src/elaborator/elaborator_validate_class_handles.cpp passes §10.3, where a
// continuous assignment's driver is defined, rather than §8.4.
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

// §8.4 allows == and != on two handles; which pairs of handles they may be
// applied to is §11.4.5's "one of the operands is assignment compatible with
// the other". That is the subclause the site in
// src/elaborator/elaborator_validate_class_handles.cpp passes for two
// unrelated classes, so it is the one asserted here.
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

// Table 8-1 lists casting of a SystemVerilog object handle as "Limited" (in
// contrast to the unrestricted casting of a C pointer). One consequence of that
// limit is that a handle cannot be reinterpreted as an unrelated non-class
// value: casting it to a plain integral type is rejected.
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

// The dual of the previous check: the limited casting of Table 8-1 also forbids
// producing a class handle out of an ordinary (non-class, non-null) value, so
// casting an integer literal to a class type is rejected.
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

}  // namespace
