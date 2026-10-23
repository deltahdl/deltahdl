#include <gtest/gtest.h>

#include <cstddef>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

// §37.42 detail 2: a method call applied to a value that no plain variable of
// the scope holds is the call the value's type gives it, as one applied to
// such a variable is: a method of the class the value is a handle of, or a
// built-in method of the string, the enumeration or the array it is (detail
// 11).
class MethodCallsOnValues : public VpiDesignRun {
 protected:
  // The number of method func calls the block top.b holds as statements, each
  // checked to be unnamed (§37.60 detail 1) and no user's (detail 11).
  static std::size_t BuiltInCallsOfTheBlock() {
    std::size_t count = 0;
    for (vpiHandle call : ObjectsOf(vpiMethodFuncCall, By("top.b"))) {
      EXPECT_EQ(vpi_get_str(vpiName, call), nullptr);
      EXPECT_EQ(vpi_get(vpiUserDefn, call), 0);
      ++count;
    }
    return count;
  }

  // That the block top.b holds a method task call of the task `run` a class of
  // the design declares, which the call reaches (§37.42).
  static void ExpectTheBlockCallsRun() {
    vpiHandle call = CallOf(vpiMethodTaskCall, By("top.b"), "run");
    ASSERT_NE(call, nullptr);
    EXPECT_EQ(vpi_get(vpiUserDefn, call), 1);
  }

  // That the method task call of `run` the block top.b holds reaches the task
  // `run` of the class defn `defn` (§37.42).
  static void ExpectTheBlockCallsRunOf(vpiHandle defn) {
    ASSERT_NE(defn, nullptr);
    vpiHandle call = CallOf(vpiMethodTaskCall, By("top.b"), "run");
    ASSERT_NE(call, nullptr);
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiTask, call)),
              VpiObjectOf(Named(vpiMethods, defn, "run")));
  }
};

// §9.7, §6.16 and §18.13.4: a built-in method's result takes the built-in
// methods of its kind, the enumeration process::status() returns and the
// string toupper() and a class's get_randstate() return (#7719, #7732).
TEST_F(MethodCallsOnValues, ABuiltInMethodsResultTakesTheMethodsOfItsKind) {
  Run("module top; process p; string s = \"ab\";\n"
      "  class K; endclass\n"
      "  K k = new;\n"
      "  initial begin : b\n"
      "    p = process::self();\n"
      "    void'(p.status().name());\n"
      "    void'(s.toupper().len());\n"
      "    void'(k.get_randstate().len());\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(BuiltInCallsOfTheBlock(), 3U);
}

// §13.4: the string a function or a class's method is declared to return takes
// the string's methods (#7719).
TEST_F(MethodCallsOnValues, ADeclaredStringResultTakesStringMethods) {
  Run("module top;\n"
      "  class K; function string get(); return \"k\"; endfunction endclass\n"
      "  function string f(); return \"f\"; endfunction\n"
      "  K k = new;\n"
      "  initial begin : b void'(f().len()); void'(k.get().len()); end\n"
      "endmodule\n");
  EXPECT_EQ(BuiltInCallsOfTheBlock(), 2U);
}

// §11.4.12.2: a concatenation of a string, and a multiple one, is a string
// (#7726).
TEST_F(MethodCallsOnValues, AStringConcatenationTakesStringMethods) {
  Run("module top; string s = \"ab\";\n"
      "  initial begin : b void'({s, \"x\"}.len()); void'({2{s}}.len()); end\n"
      "endmodule\n");
  EXPECT_EQ(BuiltInCallsOfTheBlock(), 2U);
}

// §6.24.1: a cast to string, or to an enumeration a typedef names, is a value
// of its casting type (#7726).
TEST_F(MethodCallsOnValues, ACastTakesTheMethodsOfItsCastingType) {
  Run("module top; typedef enum {A, B} e_t; int n = 5;\n"
      "  initial begin : b void'(string'(n).len()); void'(e_t'(1).name()); "
      "end\n"
      "endmodule\n");
  EXPECT_EQ(BuiltInCallsOfTheBlock(), 2U);
}

// §21.3.3: $sformatf returns a string (#7726).
TEST_F(MethodCallsOnValues, AStringSystemFunctionsResultTakesStringMethods) {
  Run("module top; int n = 5;\n"
      "  initial begin : b void'($sformatf(\"%0d\", n).len()); end\n"
      "endmodule\n");
  EXPECT_EQ(BuiltInCallsOfTheBlock(), 1U);
}

// §11.4.11: a conditional of two strings is a string, and one of two values of
// an enumeration a value of it (#7728).
TEST_F(MethodCallsOnValues, AConditionalTakesTheMethodsOfItsOperands) {
  Run("module top; typedef enum {A, B} e_t;\n"
      "  string s = \"a\", t = \"bc\"; e_t e = A, f = B; bit c = 1;\n"
      "  initial begin : b\n"
      "    void'((c ? s : t).len());\n"
      "    void'((c ? e : f).name());\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(BuiltInCallsOfTheBlock(), 2U);
}

// §7.4 and §7.10: an element of an array of strings is a string, and one of a
// queue of an enumeration a value of it (#7729).
TEST_F(MethodCallsOnValues, AnArrayElementTakesTheMethodsOfItsKind) {
  Run("module top; typedef enum {A, B} e_t;\n"
      "  string strs [2] = '{\"a\", \"bc\"}; e_t q [$] = '{B};\n"
      "  initial begin : b void'(strs[0].len()); void'(q[0].name()); end\n"
      "endmodule\n");
  EXPECT_EQ(BuiltInCallsOfTheBlock(), 2U);
}

// §8.5: a property selected from an element of an array of handles,
// objs[0].e, or from a call's result, f().s, takes the built-in methods of its
// kind (#7734, #7736).
TEST_F(MethodCallsOnValues, APropertyOfAValueTakesTheMethodsOfItsKind) {
  Run("module top; typedef enum {A, B} e_t;\n"
      "  class K; e_t e = B; string s = \"ab\"; endclass\n"
      "  K objs [2];\n"
      "  K k = new;\n"
      "  function K f(); return k; endfunction\n"
      "  initial begin : b\n"
      "    objs[0] = new;\n"
      "    void'(objs[0].e.name());\n"
      "    void'(f().s.len());\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(BuiltInCallsOfTheBlock(), 2U);
}

// §26.3: a package's string, queue and variable of an enumeration its typedef
// names, each named through the package, take the built-in methods of their
// kinds (#7735).
TEST_F(MethodCallsOnValues, APackagesVariableTakesTheMethodsOfItsKind) {
  Run("package p; typedef enum {A, B} e_t;\n"
      "  string s = \"ab\"; int q [$]; e_t e = B;\n"
      "endpackage\n"
      "module top;\n"
      "  initial begin : b\n"
      "    void'(p::s.len());\n"
      "    void'(p::q.size());\n"
      "    void'(p::e.name());\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(BuiltInCallsOfTheBlock(), 3U);
}

// §19.8: a covergroup instance has its predefined methods built in, whether a
// variable of the module, one a block declares, or a class property selected
// through a handle holds it (#7740).
TEST_F(MethodCallsOnValues, ACovergroupInstanceTakesItsPredefinedMethods) {
  Run("module top;\n"
      "  covergroup cg_t; endgroup\n"
      "  class C; cg_t cg; function new(); cg = new; endfunction endclass\n"
      "  cg_t cg = new;\n"
      "  C h = new;\n"
      "  initial begin : b\n"
      "    automatic cg_t local_cg = new;\n"
      "    cg.sample();\n"
      "    local_cg.sample();\n"
      "    h.cg.sample();\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(BuiltInCallsOfTheBlock(), 3U);
}

// §19.4 with §19.8: a covergroup a class embeds names the instance the class
// holds, whose predefined methods a handle reaches, o.cg.sample() (#7741).
TEST_F(MethodCallsOnValues, AnEmbeddedCovergroupTakesItsPredefinedMethods) {
  Run("module top;\n"
      "  class C; covergroup cg; endgroup\n"
      "    function new(); cg = new; endfunction\n"
      "  endclass\n"
      "  C o = new;\n"
      "  initial begin : b o.cg.sample(); end\n"
      "endmodule\n");
  EXPECT_EQ(BuiltInCallsOfTheBlock(), 1U);
}

// §15.5.3: a named event has its triggered() method built in, whether a
// variable of the module, one a block declares, or a class property selected
// through a handle holds it (#7744).
TEST_F(MethodCallsOnValues, ANamedEventTakesItsTriggeredMethod) {
  Run("module top;\n"
      "  class C; event ev; endclass\n"
      "  event ev;\n"
      "  C h = new;\n"
      "  initial begin : b\n"
      "    event local_ev;\n"
      "    void'(ev.triggered());\n"
      "    void'(local_ev.triggered());\n"
      "    void'(h.ev.triggered());\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(BuiltInCallsOfTheBlock(), 3U);
}

// §8.25 with §6.16: a property written with its class's type parameter is of
// the type the specialization binds the parameter to, else of the parameter's
// default, and a string's methods apply to it (#7742).
TEST_F(MethodCallsOnValues,
       APropertyOfATypeParameterTakesTheBoundTypesMethods) {
  Run("module top;\n"
      "  class C #(type T = int); T t; endclass\n"
      "  class E #(type U = string); U u; endclass\n"
      "  C #(string) g = new;\n"
      "  E e = new;\n"
      "  initial begin : b void'(g.t.len()); void'(e.u.len()); end\n"
      "endmodule\n");
  EXPECT_EQ(BuiltInCallsOfTheBlock(), 2U);
}

// §8.25: a property written with its class's type parameter holds a handle of
// the class the specialization binds the parameter to, whose method a call
// through it reaches (#7742).
TEST_F(MethodCallsOnValues, APropertyOfATypeParameterReachesTheBoundClass) {
  Run("module top;\n"
      "  class D; task run(); endtask endclass\n"
      "  class C #(type T = int); T t; endclass\n"
      "  C #(D) g = new;\n"
      "  D d = new;\n"
      "  initial begin : b g.t = d; g.t.run(); end\n"
      "endmodule\n");
  ExpectTheBlockCallsRunOf(Named(vpiClassDefn, By("top"), "D"));
}

// §8.23: a property written with a class its class declares within it holds a
// handle of that nested class rather than of a class of the module named alike,
// whose method a call through it reaches (#7743).
TEST_F(MethodCallsOnValues, APropertyOfANestedClassReachesTheNestedClass) {
  Run("module top;\n"
      "  class N; task run(); endtask endclass\n"
      "  class C;\n"
      "    class N; task run(); endtask endclass\n"
      "    N n = new;\n"
      "  endclass\n"
      "  C h = new;\n"
      "  initial begin : b h.n.run(); end\n"
      "endmodule\n");
  ExpectTheBlockCallsRunOf(
      Named(vpiInternalScope, Named(vpiClassDefn, By("top"), "C"), "N"));
}

// §26.3: a property written with a class behind its package's name holds a
// handle of the package's class rather than of a class of the module named
// alike, though the module imports nothing from the package.
TEST_F(MethodCallsOnValues, APropertyOfAPackagesClassReachesThePackagesClass) {
  Run("package pk; class D; task run(); endtask endclass endpackage\n"
      "module top;\n"
      "  class D; task run(); endtask endclass\n"
      "  class C; pk::D d = new; endclass\n"
      "  C h = new;\n"
      "  initial begin : b h.d.run(); end\n"
      "endmodule\n");
  ExpectTheBlockCallsRunOf(Named(vpiClassDefn, By("pk"), "D"));
}

// §11.3.6 with A.8.4: an assignment in parentheses, ((h = g)), is a handle of
// its left-hand side's class (#7720).
TEST_F(MethodCallsOnValues, AParenthesizedAssignmentTakesItsTargetsMethods) {
  Run("module top; class C; task run(); endtask endclass\n"
      "  C h; C g = new;\n"
      "  initial begin : b ((h = g)).run(); end\n"
      "endmodule\n");
  ExpectTheBlockCallsRun();
}

// §7.2: a class var a structure member's own structure member holds,
// s.inner.h, is reached through both structures (#7721).
TEST_F(MethodCallsOnValues, ANestedStructureMembersHandleTakesItsMethods) {
  Run("module top; class C; task run(); endtask endclass\n"
      "  typedef struct { int n; C h; } in_t;\n"
      "  typedef struct { int m; in_t inner; } out_t;\n"
      "  out_t s;\n"
      "  initial begin : b s.inner.h = new; s.inner.h.run(); end\n"
      "endmodule\n");
  ExpectTheBlockCallsRun();
}

// §9.3.4 and §23.6: a class var a named block declares, reached from another
// process through the block's name, b1.h, is a handle of its class (#7724).
TEST_F(MethodCallsOnValues, ANamedBlocksHandleReachedByNameTakesItsMethods) {
  Run("module top; class C; task run(); endtask endclass\n"
      "  initial begin begin : b1 static C h = new; static int n; n = 1; end "
      "end\n"
      "  initial begin : b #1; b1.h.run(); end\n"
      "endmodule\n");
  ExpectTheBlockCallsRun();
}

}  // namespace
}  // namespace delta
