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
// These tests observe the parser recognizing the std-package type name
// (Parser::known_types_ seeds "weak_reference") so that a parameterized
// declaration, the constructor with a referent argument, and the prototype's
// instance and static method calls all parse without any user
// `class weak_reference` definition.

#include "fixture_parser.h"

using namespace delta;

namespace {

// `weak_reference` is a known std-package type name: a parameterized
// declaration over a user class parses with no user `class weak_reference`.
TEST(WeakReferenceStdPackageParser, ParameterizedDeclarationOfBuiltInType) {
  auto r = Parse(
      "class my_obj;\n"
      "  int x;\n"
      "endclass\n"
      "module m;\n"
      "  weak_reference #(my_obj) wr;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.has_errors);
}

// The prototype's new(T referent) constructor, get(), and clear() parse at
// their call sites.
TEST(WeakReferenceStdPackageParser, PrototypeInstanceMethodsParse) {
  auto r = Parse(
      "class my_obj;\n"
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
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.has_errors);
}

// The prototype declares get_id() as a static function reached through the
// parameterized class scope-resolution operator; its longint result parses in
// an expression position.
TEST(WeakReferenceStdPackageParser, StaticGetIdScopeResolutionParses) {
  auto r = Parse(
      "class my_obj;\n"
      "  int x;\n"
      "endclass\n"
      "module m;\n"
      "  my_obj o;\n"
      "  longint id;\n"
      "  initial begin\n"
      "    o = new();\n"
      "    id = weak_reference#(my_obj)::get_id(o);\n"
      "    if (weak_reference#(my_obj)::get_id(o) != 0) ;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.has_errors);
}

// The std-package type name is recognized as a subroutine formal port type, so
// a weak_reference handle can be declared as an argument.
TEST(WeakReferenceStdPackageParser, WeakReferenceAsSubroutineFormalType) {
  EXPECT_TRUE(
      ParseOk("class my_obj;\n"
              "  int x;\n"
              "endclass\n"
              "module m;\n"
              "  function void f(weak_reference #(my_obj) wr);\n"
              "    wr.clear();\n"
              "  endfunction\n"
              "endmodule\n"));
}

}  // namespace
