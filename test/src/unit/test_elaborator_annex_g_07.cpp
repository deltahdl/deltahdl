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

#include <gtest/gtest.h>

#include "elaborator/std_package.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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
  // A weak_reference declared inside a procedural block is a kVarDecl
  // statement, so ValidateLocalWeakRefDecls in
  // src/elaborator/elaborator_scope_rules.cpp answers for it and reports at the
  // declaration statement. The same rule reaches a class member and a
  // subroutine argument through different walks, and all four sites cite
  // §8.30.1, which is the subclause carrying the sentence they enforce. This
  // site cited §8.30 until #3058.
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  initial begin\n"
      "    weak_reference #(int) wr;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "weak_reference type parameter shall be a class "
                            "type",
                            3, "8.30.1"));
}

// Edge of the same `type class T` restriction: a named type that is not a class
// (here an enum typedef) is rejected too -- the class-type requirement is not
// satisfied merely by the argument being a named user type.
TEST(WeakReferenceStdPackageElaborator, TypeParameterRejectsNamedNonClassType) {
  ElabFixture f;
  ElabOk(
      "typedef enum {A, B} my_enum;\n"
      "module m;\n"
      "  initial begin\n"
      "    weak_reference #(my_enum) wr;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "weak_reference type parameter shall be a class "
                            "type",
                            4, "8.30.1"));
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

// §G.7: the prototype as src/elaborator/std_package.h writes it down -- the
// constructor new over one formal T referent with no default, get returning
// T and taking nothing, clear void and taking nothing, and the static
// get_id returning longint over T obj -- over a type parameter T restricted
// to a class type and given no default.
TEST(WeakReferenceStdPackageElaborator, ThePrototypeIsWrittenDown) {
  const auto& prototype = WeakReferencePrototype();
  ASSERT_EQ(prototype.size(), 4u);
  EXPECT_EQ(prototype[0].name, "new");
  ASSERT_EQ(prototype[0].formals.size(), 1u);
  EXPECT_EQ(prototype[0].formals[0].type, "T");
  EXPECT_EQ(prototype[0].formals[0].name, "referent");
  EXPECT_FALSE(prototype[0].formals[0].has_default);
  EXPECT_EQ(LeastActualsOf(prototype[0]), 1u);
  EXPECT_EQ(prototype[1].name, "get");
  EXPECT_EQ(prototype[1].return_type, "T");
  EXPECT_TRUE(prototype[1].formals.empty());
  EXPECT_EQ(prototype[2].name, "clear");
  EXPECT_EQ(prototype[2].return_type, "void");
  EXPECT_TRUE(prototype[2].formals.empty());
  EXPECT_EQ(prototype[3].name, "get_id");
  EXPECT_TRUE(prototype[3].is_static);
  EXPECT_EQ(prototype[3].return_type, "longint");
  ASSERT_EQ(prototype[3].formals.size(), 1u);
  EXPECT_EQ(prototype[3].formals[0].name, "obj");
  for (const StdMethodPrototype& method : prototype) {
    EXPECT_EQ(method.kind, StdMethodKind::kFunction);
  }
  EXPECT_EQ(&StdClassPrototype(StdPackageMember::kWeakReference), &prototype);
  EXPECT_TRUE(StdClassHasConstructor(StdPackageMember::kWeakReference));
  EXPECT_FALSE(StdClassIsFinal(StdPackageMember::kWeakReference));
  const StdTypeParameter kT =
      StdClassTypeParameterOf(StdPackageMember::kWeakReference)
          .value_or(StdTypeParameter{});
  EXPECT_EQ(kT.name, "T");
  EXPECT_TRUE(kT.default_type.empty());
  EXPECT_TRUE(kT.class_only);
}

// §G.7: a construction and a call on a weak_reference handle are checked
// against the prototype: new with no referent, get with an argument and a
// method the prototype does not declare are each rejected under §G.7 at the
// call, whether the handle is a module variable or one a procedural block
// declares with its construction, while new with a referent, get and clear
// beside them are accepted.
TEST(WeakReferenceStdPackageElaborator,
     ConstructionsAndCallsAreCheckedAgainstThePrototype) {
  ElabFixture f;
  ElabOk(
      "class my_obj;\n"
      "  int x;\n"
      "endclass\n"
      "module m;\n"
      "  my_obj strong_obj;\n"
      "  my_obj result;\n"
      "  weak_reference #(my_obj) wr;\n"
      "  initial begin\n"
      "    weak_reference #(my_obj) local_wr = new;\n"
      "    strong_obj = new();\n"
      "    wr = new;\n"
      "    wr = new(strong_obj);\n"
      "    result = wr.get(1);\n"
      "    wr.drop();\n"
      "    result = wr.get();\n"
      "    wr.clear();\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "constructor of class 'weak_reference' takes at "
                            "least 1 argument; 0 given",
                            9, "G.7"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "constructor of class 'weak_reference' takes at "
                            "least 1 argument; 0 given",
                            11, "G.7"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "method 'get' of class 'weak_reference' takes at "
                            "most 0 arguments; 1 given",
                            13, "G.7"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class 'weak_reference' declares no method 'drop'",
                            14, "G.7"));
  for (const auto& d : f.diag.Diagnostics()) {
    EXPECT_NE(d.loc.line, 12u);
    EXPECT_NE(d.loc.line, 15u);
    EXPECT_NE(d.loc.line, 16u);
  }
}

}  // namespace
