#include "fixture_elaborator.h"

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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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

TEST(ClassObjectElaboration, ClassVariableDeclarationOk) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  int data;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p1;\n"
             "endmodule\n"));
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
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
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
