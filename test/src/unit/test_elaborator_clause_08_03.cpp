#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ClassSyntaxElaboration, FinalOnPureConstraintError) {
  EXPECT_FALSE(
      ElabOk("virtual class Base;\n"
             "  pure constraint :final my_c;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// LRM 8.3 (footnote 8): the final specifier is illegal on a pure virtual
// method, the method counterpart of the pure-constraint rule above.
TEST(ClassSyntaxElaboration, FinalOnPureVirtualMethodError) {
  EXPECT_FALSE(
      ElabOk("virtual class Base;\n"
             "  pure virtual function :final void foo();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

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
