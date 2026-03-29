#include "fixture_elaborator.h"

using namespace delta;

namespace {

// === constraint_declaration in a class ===

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

// === constraint_prototype in a class ===

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
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  extern constraint c;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ConstraintElaboration, ClassWithPureConstraintPrototype) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  pure constraint c;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// === constraint_declaration with dynamic_override_specifiers ===

TEST(ConstraintElaboration, ConstraintWithDynamicOverride) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  constraint :initial c { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// === extern_constraint_declaration ===

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

// === constraint_block: complex block contents ===

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
