#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ConstraintElaboration, ClassWithConstraintDeclaration) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  constraint c { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ConstraintElaboration, ClassWithStaticConstraint) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  static constraint c { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ConstraintElaboration, ClassWithMultipleConstraints) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x, y;\n"
             "  constraint c1 { x > 0; }\n"
             "  constraint c2 { y > 0; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ConstraintElaboration, ClassWithConstraintPrototype) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  constraint c;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ConstraintElaboration, ClassWithExternConstraintPrototype) {
  // §18.5.2: with the explicit form of constraint prototype (the extern
  // keyword), it shall be an error if no corresponding external constraint
  // block is provided.
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  extern constraint c;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ConstraintElaboration, ClassWithPureConstraintPrototype) {
  // §18.5: it shall be an error to declare a pure constraint in a non-abstract
  // class (C here is not virtual).
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  pure constraint c;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ConstraintElaboration, ConstraintWithDynamicOverride) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  constraint :initial c { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ConstraintElaboration, ExternConstraintDeclaration) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  extern constraint c;\n"
             "endclass\n"
             "constraint C::c { x > 0; }\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ConstraintElaboration, ConstraintWithComplexBlock) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int a, b, c;\n"
             "  constraint order_c {\n"
             "    solve a before b;\n"
             "    a > 0;\n"
             "    soft b == 1;\n"
             "    if (a > 5) { b < 10; }\n"
             "    foreach (c[i]) c[i] > 0;\n"
             "    unique { a, b };\n"
             "    disable soft a;\n"
             "  }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

}  // namespace
