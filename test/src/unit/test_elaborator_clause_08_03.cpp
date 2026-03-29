#include "fixture_elaborator.h"

using namespace delta;

namespace {

// Footnote 7: In a parameter_declaration that is a class_item, the parameter
// keyword shall be a synonym for the localparam keyword.

TEST(ClassSyntaxElaboration, ParameterInClassBodyIsLocalparam) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  parameter int WIDTH = 8;\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(ClassSyntaxElaboration, MultipleParametersInClassBody) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  parameter int A = 1;\n"
             "  parameter int B = A + 1;\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// Footnote 8: It shall be illegal to use the final_specifier when declaring a
// pure virtual method or pure constraint.

TEST(ClassSyntaxElaboration, FinalOnPureConstraintError) {
  EXPECT_FALSE(
      ElabOk("virtual class Base;\n"
             "  pure constraint :final my_c;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// Footnote 25: The dynamic_override_specifiers shall only be legal on method
// declarations inside a non-interface class scope.

TEST(ClassSyntaxElaboration, DynamicOverrideInInterfaceClassError) {
  EXPECT_FALSE(
      ElabOk("interface class IC;\n"
             "  pure virtual function :initial void foo();\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(ClassSyntaxElaboration, DynamicOverrideExtendsInInterfaceClassError) {
  EXPECT_FALSE(
      ElabOk("interface class IC;\n"
             "  pure virtual function :extends void bar();\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(ClassSyntaxElaboration, DynamicOverrideFinalInInterfaceClassError) {
  EXPECT_FALSE(
      ElabOk("interface class IC;\n"
             "  pure virtual function :final void baz();\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(ClassSyntaxElaboration, DynamicOverrideInNonInterfaceClassOk) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  virtual function :initial void foo();\n"
             "  endfunction\n"
             "endclass\n"
             "module m; endmodule\n"));
}

}  // namespace
