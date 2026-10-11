#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §6.19.5: an enumeration has the built-in methods §6.19.5.1 to §6.19.5.6 list
// and no others, nor any member, so a call or select naming anything else
// through an enumeration variable is reported, its type written as a typedef
// name or in the declaration itself.
TEST(EnumMethodElaboration, NameNoEnumMethodIsReported) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  typedef enum {A, B} e_t;\n"
      "  e_t e;\n"
      "  enum {C, D} f;\n"
      "  initial begin\n"
      "    e.foo();\n"
      "    e.h.run();\n"
      "    f.bar();\n"
      "    e.rand_mode(0);\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(
      diags, "'foo' is not a built-in method of the enumeration 'e'", 6,
      "6.19.5"));
  EXPECT_TRUE(ReportedError(
      diags, "'h' is not a built-in method of the enumeration 'e'", 7,
      "6.19.5"));
  EXPECT_TRUE(ReportedError(
      diags, "'bar' is not a built-in method of the enumeration 'f'", 8,
      "6.19.5"));
  EXPECT_TRUE(ReportedError(
      diags, "'rand_mode' is not a built-in method of the enumeration 'e'", 9,
      "6.19.5"));
}

TEST(EnumMethodElaboration, EveryEnumMethodIsAccepted) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  typedef enum {A, B, C} e_t;\n"
             "  e_t e;\n"
             "  int n;\n"
             "  string s;\n"
             "  initial begin\n"
             "    e = e.first();\n"
             "    e = e.last();\n"
             "    e = e.next();\n"
             "    e = e.prev(2);\n"
             "    n = e.num();\n"
             "    s = e.name();\n"
             "  end\n"
             "endmodule\n"));
}

// §18.8: a random property of a class, an enumeration among them, is named in
// a call of its rand_mode by a method of the class.
TEST(EnumMethodElaboration, RandModeOfAnEnumPropertyIsAccepted) {
  EXPECT_TRUE(
      ElabOk("class K;\n"
             "  rand enum {A, B} e;\n"
             "  function void hold();\n"
             "    e.rand_mode(0);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// §23.2.2: a port that is an enumeration is an enumeration variable of the
// module.
TEST(EnumMethodElaboration, PortsAreChecked) {
  ElabFixture f;
  ElabOk(
      "module m(input enum {A, B} e);\n"
      "  initial e.foo();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'foo' is not a built-in method of the enumeration 'e'", 2, "6.19.5"));
}

// §6.19.5 with §13.4.1: the result of a call returning an enumeration has the
// built-in methods of one and no others, whether the call is of a function of
// the module, f(), of a method of the class a handle holds, k.get(), or of
// process's status(), whose type is the enumeration state (§9.7).
TEST(EnumMethodElaboration, MethodOfAnEnumerationACallReturnsIsReported) {
  ElabFixture f;
  ElabOk(
      "class K;\n"
      "  typedef enum {C, D} s_t;\n"
      "  function s_t get(); return C; endfunction\n"
      "  function K me(); return this; endfunction\n"
      "endclass\n"
      "module m;\n"
      "  typedef enum {A, B} e_t;\n"
      "  function e_t f(); return A; endfunction\n"
      "  process p;\n"
      "  K k = new;\n"
      "  K ka [2];\n"
      "  e_t e;\n"
      "  initial begin\n"
      "    p = process::self();\n"
      "    p.status().run();\n"
      "    process::self().status().go();\n"
      "    p.self().status().stop();\n"
      "    f().foo();\n"
      "    k.get().bar();\n"
      "    e = f().next();\n"
      "    $display(p.status().name(), k.get().num());\n"
      "    $display(k.me().get().name(), ka[0].get().first());\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(diags,
                            "'run' is not a built-in method of the enumeration "
                            "that 'status()' returns",
                            15, "6.19.5"));
  EXPECT_TRUE(ReportedError(diags,
                            "'go' is not a built-in method of the enumeration "
                            "that 'status()' returns",
                            16, "6.19.5"));
  EXPECT_TRUE(ReportedError(diags,
                            "'stop' is not a built-in method of the "
                            "enumeration that 'status()' returns",
                            17, "6.19.5"));
  EXPECT_TRUE(ReportedError(
      diags,
      "'foo' is not a built-in method of the enumeration that 'f()' returns",
      18, "6.19.5"));
  EXPECT_TRUE(ReportedError(
      diags,
      "'bar' is not a built-in method of the enumeration that 'get()' returns",
      19, "6.19.5"));
  EXPECT_EQ(f.diag.ErrorCount(), 5u);
}

// §8.13 with §13.4.1: a method's return type is read in its class, where a
// type parameter or a typedef the class or a class it extends declares hides
// the module's type of the name, and an array typedef has the array methods;
// a call by a name alone in a method calls the class's method first, and the
// module's function where the class declares none.
TEST(EnumMethodElaboration, ClassMethodResultTypesAreReadInTheClass) {
  ElabFixture f;
  ElabOk(
      "package p;\n"
      "  typedef enum {P0, P1} pe_t;\n"
      "endpackage\n"
      "module m;\n"
      "  typedef enum {A, B} T;\n"
      "  typedef enum {X, Y} t_t;\n"
      "  typedef enum {M0, M1} m_t;\n"
      "  function T f(); return A; endfunction\n"
      "  class K #(type T = string);\n"
      "    typedef string t_t;\n"
      "    typedef string pe_t;\n"
      "    typedef enum {C, D} s_t;\n"
      "    typedef s_t sa_t [2];\n"
      "    function s_t get(); return C; endfunction\n"
      "    function T gett(); T v; return v; endfunction\n"
      "    function sa_t geta(); sa_t v; return v; endfunction\n"
      "    function p::pe_t getp(); return p::P0; endfunction\n"
      "    function t_t gets(); return "
      "; endfunction\n"
      "    function m_t getm(); return M0; endfunction\n"
      "  endclass\n"
      "  class D extends K;\n"
      "    function void use();\n"
      "      int n;\n"
      "      get().baz();\n"
      "      f().qux();\n"
      "      getm().corge();\n"
      "      n = gett().len();\n"
      "      n = geta().size();\n"
      "      n = getp().num();\n"
      "      n = gets().len();\n"
      "    endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(
      diags,
      "'baz' is not a built-in method of the enumeration that 'get()' returns",
      24, "6.19.5"));
  EXPECT_TRUE(ReportedError(
      diags,
      "'qux' is not a built-in method of the enumeration that 'f()' returns",
      25, "6.19.5"));
  EXPECT_TRUE(ReportedError(diags,
                            "'corge' is not a built-in method of the "
                            "enumeration that 'getm()' returns",
                            26, "6.19.5"));
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
}

// §G.6: a method process does not declare is reported as such, and its result
// is checked no further.
TEST(EnumMethodElaboration, UnknownProcessMethodResultIsLeftUnchecked) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  process p;\n"
      "  function process getp(); return process::self(); endfunction\n"
      "  initial begin\n"
      "    p = process::self();\n"
      "    p.bogus().run();\n"
      "    $display(getp().status().name());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class 'process' declares no method 'bogus'", 6,
                            "G.6"));
  EXPECT_EQ(f.diag.ErrorCount(), 1u);
}

}  // namespace
