#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ClassConstraintElaboration, WeakReferenceDeclOk) {
  EXPECT_TRUE(
      ElabOk("class my_obj;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    weak_reference #(my_obj) wr;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassConstraintElaboration, WeakReferenceAsMemberOk) {
  EXPECT_TRUE(
      ElabOk("class my_obj;\n"
             "  int x;\n"
             "endclass\n"
             "class holder;\n"
             "  weak_reference #(my_obj) wr;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ClassConstraintElaboration, WeakReferenceNonClassTypeError) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  initial begin\n"
             "    weak_reference #(int) wr;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassConstraintElaboration, WeakReferenceAsFunctionArgOk) {
  EXPECT_TRUE(
      ElabOk("class my_obj;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  function void f(weak_reference #(my_obj) wr);\n"
             "  endfunction\n"
             "endmodule\n"));
}

TEST(ClassConstraintElaboration, WeakReferenceAsTaskArgOk) {
  EXPECT_TRUE(
      ElabOk("class my_obj;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  task t(weak_reference #(my_obj) wr);\n"
             "  endtask\n"
             "endmodule\n"));
}

// A weak_reference incorporated into another object as a class property is held
// to the same class-type restriction: a non-class parameter is a compiler error
// at the member-declaration site too.
TEST(ClassConstraintElaboration, WeakReferenceNonClassMemberError) {
  EXPECT_FALSE(
      ElabOk("class holder;\n"
             "  weak_reference #(int) wr;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// The class-type restriction applies wherever weak_reference#(T) is declared,
// including a subroutine argument. A non-class parameter on a function port is
// a compiler error just as it is on a variable declaration.
TEST(ClassConstraintElaboration, WeakReferenceNonClassFunctionArgError) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  function void f(weak_reference #(int) wr);\n"
             "  endfunction\n"
             "endmodule\n"));
}

// Same restriction on a task port: a non-class parameter type is rejected.
TEST(ClassConstraintElaboration, WeakReferenceNonClassTaskArgError) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  task t(weak_reference #(int) wr);\n"
             "  endtask\n"
             "endmodule\n"));
}

}  // namespace
