#include <gtest/gtest.h>

#include <cstddef>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class MethodCallsOnValues : public VpiDesignRun {
 protected:
  static std::size_t BuiltInCallsOfTheBlock() {
    std::size_t count = 0;
    for (vpiHandle call : ObjectsOf(vpiMethodFuncCall, By("top.b"))) {
      EXPECT_EQ(vpi_get_str(vpiName, call), nullptr);
      EXPECT_EQ(vpi_get(vpiUserDefn, call), 0);
      ++count;
    }
    return count;
  }

  static void ExpectTheBlockCallsRun() {
    vpiHandle call = CallOf(vpiMethodTaskCall, By("top.b"), "run");
    ASSERT_NE(call, nullptr);
    EXPECT_EQ(vpi_get(vpiUserDefn, call), 1);
  }

  static void ExpectTheBlockCallsRunOf(vpiHandle defn) {
    ASSERT_NE(defn, nullptr);
    vpiHandle call = CallOf(vpiMethodTaskCall, By("top.b"), "run");
    ASSERT_NE(call, nullptr);
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiTask, call)),
              VpiObjectOf(Named(vpiMethods, defn, "run")));
  }
};

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

TEST_F(MethodCallsOnValues, ADeclaredStringResultTakesStringMethods) {
  Run("module top;\n"
      "  class K; function string get(); return \"k\"; endfunction endclass\n"
      "  function string f(); return \"f\"; endfunction\n"
      "  K k = new;\n"
      "  initial begin : b void'(f().len()); void'(k.get().len()); end\n"
      "endmodule\n");
  EXPECT_EQ(BuiltInCallsOfTheBlock(), 2U);
}

TEST_F(MethodCallsOnValues, AStringConcatenationTakesStringMethods) {
  Run("module top; string s = \"ab\";\n"
      "  initial begin : b void'({s, \"x\"}.len()); void'({2{s}}.len()); end\n"
      "endmodule\n");
  EXPECT_EQ(BuiltInCallsOfTheBlock(), 2U);
}

TEST_F(MethodCallsOnValues, ACastTakesTheMethodsOfItsCastingType) {
  Run("module top; typedef enum {A, B} e_t; int n = 5;\n"
      "  initial begin : b void'(string'(n).len()); void'(e_t'(1).name()); "
      "end\n"
      "endmodule\n");
  EXPECT_EQ(BuiltInCallsOfTheBlock(), 2U);
}

TEST_F(MethodCallsOnValues, AStringSystemFunctionsResultTakesStringMethods) {
  Run("module top; int n = 5;\n"
      "  initial begin : b void'($sformatf(\"%0d\", n).len()); end\n"
      "endmodule\n");
  EXPECT_EQ(BuiltInCallsOfTheBlock(), 1U);
}

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

TEST_F(MethodCallsOnValues, AnArrayElementTakesTheMethodsOfItsKind) {
  Run("module top; typedef enum {A, B} e_t;\n"
      "  string strs [2] = '{\"a\", \"bc\"}; e_t q [$] = '{B};\n"
      "  initial begin : b void'(strs[0].len()); void'(q[0].name()); end\n"
      "endmodule\n");
  EXPECT_EQ(BuiltInCallsOfTheBlock(), 2U);
}

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

TEST_F(MethodCallsOnValues, AParenthesizedAssignmentTakesItsTargetsMethods) {
  Run("module top; class C; task run(); endtask endclass\n"
      "  C h; C g = new;\n"
      "  initial begin : b ((h = g)).run(); end\n"
      "endmodule\n");
  ExpectTheBlockCallsRun();
}

TEST_F(MethodCallsOnValues, ANestedStructureMembersHandleTakesItsMethods) {
  Run("module top; class C; task run(); endtask endclass\n"
      "  typedef struct { int n; C h; } in_t;\n"
      "  typedef struct { int m; in_t inner; } out_t;\n"
      "  out_t s;\n"
      "  initial begin : b s.inner.h = new; s.inner.h.run(); end\n"
      "endmodule\n");
  ExpectTheBlockCallsRun();
}

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
