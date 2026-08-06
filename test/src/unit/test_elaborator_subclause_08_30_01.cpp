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

// A weak_reference declared directly as a module item (not inside a procedural
// block) is checked by a separate elaborator path than a block-local variable.
// A class parameter is accepted there just as it is for a procedural local.
TEST(ClassConstraintElaboration, WeakReferenceModuleItemDeclOk) {
  EXPECT_TRUE(
      ElabOk("class my_obj;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  weak_reference #(my_obj) wr;\n"
             "endmodule\n"));
}

// The module-item declaration path enforces the same restriction: a non-class
// parameter at module scope is a compiler error, exercising the module-level
// validator rather than the procedural-block one covered above.
TEST(ClassConstraintElaboration, WeakReferenceModuleItemNonClassError) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  weak_reference #(int) wr;\n"
             "endmodule\n"));
}

// The Overview's own example forward-declares the referent class with
// `typedef class my_obj;` before naming it as the weak_reference parameter. A
// forward-declared class is still a class type, so this exact form elaborates.
TEST(ClassConstraintElaboration, WeakReferenceForwardTypedefClassOk) {
  EXPECT_TRUE(
      ElabOk("typedef class my_obj;\n"
             "module m;\n"
             "  initial begin\n"
             "    weak_reference #(my_obj) weak_obj;\n"
             "  end\n"
             "endmodule\n"
             "class my_obj;\n"
             "  int x;\n"
             "endclass\n"));
}

// A typedef alias of a class denotes the same class type, so a
// weak_reference parameterized on the alias names a class type and shall be
// accepted just as the class name itself is. The parameter check follows the
// typedef through to the underlying class rather than demanding the raw class
// name at the use site.
TEST(ClassConstraintElaboration, WeakReferenceTypedefAliasOfClassOk) {
  EXPECT_TRUE(
      ElabOk("class my_obj;\n"
             "  int x;\n"
             "endclass\n"
             "typedef my_obj my_alias;\n"
             "module m;\n"
             "  initial begin\n"
             "    weak_reference #(my_alias) wr;\n"
             "  end\n"
             "endmodule\n"));
}

// The closest rejected neighbor of the accepting path: a parameter that names a
// user-defined type which is NOT a class (here a typedef enum). Unlike a
// built-in keyword such as `int`, the argument is a named type, so the check
// must resolve the name through the typedef table, find a non-class type, and
// still report the compiler error the rule requires.
TEST(ClassConstraintElaboration, WeakReferenceTypedefNonClassError) {
  EXPECT_FALSE(
      ElabOk("typedef enum {A, B} col_t;\n"
             "module m;\n"
             "  initial begin\n"
             "    weak_reference #(col_t) wr;\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
