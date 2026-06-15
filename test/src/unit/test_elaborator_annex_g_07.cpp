// IEEE 1800-2023 Annex G.7 (Std package -- Weak reference).
//
// Section G.7 presents the prototype of the built-in `weak_reference` class
// that the std package provides; its semantics are owned by clause 8.30. The
// prototype is:
//
//   class weak_reference #(type class T);
//     function new(T referent);
//     function T get();
//     function void clear();
//     static function longint get_id(T obj);
//   endclass
//
// These tests observe the elaborator providing that prototype out of the std
// package: `weak_reference` resolves as a built-in class without any user
// `class weak_reference` definition (Elaborator::RegisterCuScopeItems registers
// the std-package class name), the `#(type class T)` parameter is held to a
// class type, and the prototype's constructor, instance methods, and static
// get_id() elaborate at their call sites.

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// The std package supplies the class name; no user declaration is required for
// a parameterized weak_reference over a user class.
TEST(WeakReferenceStdPackageElaborator, BuiltInClassNeedsNoUserDefinition) {
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

// The prototype restricts the parameter to a class type (`type class T`): a
// built-in integer argument is rejected at elaboration.
TEST(WeakReferenceStdPackageElaborator, TypeParameterRejectsNonClassType) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  initial begin\n"
             "    weak_reference #(int) wr;\n"
             "  end\n"
             "endmodule\n"));
}

// Edge of the same `type class T` restriction: a named type that is not a class
// (here an enum typedef) is rejected too -- the class-type requirement is not
// satisfied merely by the argument being a named user type.
TEST(WeakReferenceStdPackageElaborator, TypeParameterRejectsNamedNonClassType) {
  EXPECT_FALSE(
      ElabOk("typedef enum {A, B} my_enum;\n"
             "module m;\n"
             "  initial begin\n"
             "    weak_reference #(my_enum) wr;\n"
             "  end\n"
             "endmodule\n"));
}

// The prototype constructor new(T referent), get(), and clear() elaborate at
// their call sites.
TEST(WeakReferenceStdPackageElaborator, PrototypeInstanceMethodsElaborate) {
  EXPECT_TRUE(
      ElabOk("class my_obj;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  my_obj strong_obj;\n"
             "  my_obj result;\n"
             "  weak_reference #(my_obj) wr;\n"
             "  initial begin\n"
             "    strong_obj = new();\n"
             "    wr = new(strong_obj);\n"
             "    result = wr.get();\n"
             "    wr.clear();\n"
             "  end\n"
             "endmodule\n"));
}

// The prototype's static get_id(T obj), reached through the parameterized class
// scope-resolution operator, elaborates and its longint result is usable in an
// expression.
TEST(WeakReferenceStdPackageElaborator, StaticGetIdElaborates) {
  EXPECT_TRUE(
      ElabOk("class my_obj;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    my_obj o;\n"
             "    longint id;\n"
             "    o = new();\n"
             "    id = weak_reference#(my_obj)::get_id(o);\n"
             "  end\n"
             "endmodule\n"));
}

// The built-in type resolves as a subroutine formal port type, and a prototype
// method (clear) elaborates on the formal at the callee site.
TEST(WeakReferenceStdPackageElaborator, WeakReferenceAsSubroutineFormalType) {
  EXPECT_TRUE(
      ElabOk("class my_obj;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  function void f(weak_reference #(my_obj) wr);\n"
             "    wr.clear();\n"
             "  endfunction\n"
             "endmodule\n"));
}

}  // namespace
