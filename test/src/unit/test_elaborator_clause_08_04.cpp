#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ElabA84, PrimaryNullElaborates) {
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

TEST(ElabA84, ClassHandleAssignNull) {
  EXPECT_TRUE(
      ElabOk("class C; endclass\n"
             "module m;\n"
             "  C c;\n"
             "  initial c = null;\n"
             "endmodule\n"));
}

TEST(ElabA84, ClassHandleAssignHandle) {
  EXPECT_TRUE(
      ElabOk("class C; endclass\n"
             "module m;\n"
             "  C a, b;\n"
             "  initial a = b;\n"
             "endmodule\n"));
}

TEST(ElabA84, ClassHandleEqualityAllowed) {
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

TEST(ElabA84, ClassHandleCaseEqualityAllowed) {
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

TEST(ElabA84, ClassHandleInequalityAllowed) {
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

TEST(ElabA84, ClassHandleConditionalAllowed) {
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

TEST(ElabA84, ClassHandleArithmeticError) {
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

TEST(ElabA84, ClassHandleRelationalError) {
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

TEST(ElabA84, ClassHandleBitwiseError) {
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

TEST(ElabA84, ClassHandleLogicalNegationError) {
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

TEST(ElabA84, ClassHandleIncrementError) {
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

TEST(ElabA84, ClassHandleShiftError) {
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

TEST(ElabA84, ClassHandleCompoundAssignError) {
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

TEST(ElabA84, ClassHandleBitSelectError) {
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

TEST(ElabA84, ClassHandleContAssignError) {
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

}
