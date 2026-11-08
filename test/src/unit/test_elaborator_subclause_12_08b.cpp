#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

namespace {

TEST(JumpStatementElaboration, ReturnStringVariableFromIntFunctionIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int h();\n"
      "    string s;\n"
      "    return s;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return expression in function 'h' is not "
                            "assignment-compatible with the function's return "
                            "type",
                            4, "12.8"));
}

TEST(JumpStatementElaboration, ReturnClassHandleFromIntFunctionIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  class A; endclass\n"
      "  function int g(A a);\n"
      "    return a;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return expression in function 'g' is not "
                            "assignment-compatible with the function's return "
                            "type",
                            4, "12.8"));
}

TEST(JumpStatementElaboration, ReturnIntegralValuesFromIntFunctionOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int h(int k);\n"
      "    string s;\n"
      "    if (k > 0) return s.len();\n"
      "    return k;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(JumpStatementElaboration, ReturnUnrelatedHandleFromClassFunctionIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  class A; endclass\n"
      "  class B; endclass\n"
      "  function automatic A f();\n"
      "    B b = new;\n"
      "    return b;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return expression in function 'f' is not "
                            "assignment-compatible with the function's return "
                            "type",
                            6, "12.8"));
}

TEST(JumpStatementElaboration, ReturnIntegerFromClassFunctionIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  class A; endclass\n"
      "  function A g();\n"
      "    return 5;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return expression in function 'g' is not "
                            "assignment-compatible with the function's return "
                            "type",
                            4, "12.8"));
}

TEST(JumpStatementElaboration, ReturnFittingValuesFromNamedTypeFunctionsOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  class A; endclass\n"
      "  class D extends A; endclass\n"
      "  typedef int T;\n"
      "  function automatic A f(bit k);\n"
      "    D d = new;\n"
      "    if (k) return d;\n"
      "    return new;\n"
      "  endfunction\n"
      "  function T g();\n"
      "    return 1;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(JumpStatementElaboration, ReturnRealFromStringTypedefFunctionIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef string S;\n"
      "  function S g();\n"
      "    return 1.5;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return expression in function 'g' is not "
                            "assignment-compatible with the function's return "
                            "type",
                            4, "12.8"));
}

TEST(JumpStatementElaboration, ReturnTypeNamedByAClassTypedefIsTheClasssType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef enum {X, Y} t_t;\n"
      "  class K;\n"
      "    typedef string t_t;\n"
      "    function t_t gets(); return \"\"; endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(JumpStatementElaboration,
     ReturnOfANameANestedBlockHidesReadsTheBlocksType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  class A; endclass\n"
      "  function automatic A f(int v);\n"
      "    begin\n"
      "      A v = new;\n"
      "      return v;\n"
      "    end\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(JumpStatementElaboration, ReturnOfAnIntANestedBlockDeclaresIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  class A; endclass\n"
      "  function automatic A f(A v);\n"
      "    begin\n"
      "      int v = 1;\n"
      "      return v;\n"
      "    end\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return expression in function 'f' is not "
                            "assignment-compatible with the function's return "
                            "type",
                            6, "12.8"));
}

TEST(JumpStatementElaboration, ReturnOfAnArrayANestedBlockDeclaresElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  class A; endclass\n"
      "  typedef int pair_t[2];\n"
      "  function automatic pair_t f(A v);\n"
      "    begin\n"
      "      int v[2];\n"
      "      return v;\n"
      "    end\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(JumpStatementElaboration, ReturnOfANameAForLoopDeclaresReadsTheLoopsType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  class A; endclass\n"
      "  function automatic A f(int v);\n"
      "    for (A v = null; v != null; ) return v;\n"
      "    for (v = 0; v < 2; v++) ;\n"
      "    return null;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(JumpStatementElaboration, ReturnOfAnIntAForLoopDeclaresIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  class A; endclass\n"
      "  function automatic A f(A v);\n"
      "    for (int v = 0; v < 2; v++) return v;\n"
      "    return null;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return expression in function 'f' is not "
                            "assignment-compatible with the function's return "
                            "type",
                            4, "12.8"));
}

TEST(JumpStatementElaboration, ReturnOfAnIntIndexedForeachVariableIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  class A; endclass\n"
      "  int fx[4];\n"
      "  function automatic A f(A v);\n"
      "    int dyn[];\n"
      "    int q[$];\n"
      "    int grid[2][3];\n"
      "    bit [3:0] bits;\n"
      "    foreach (fx[v]) return v;\n"
      "    foreach (dyn[v]) return v;\n"
      "    foreach (q[v]) return v;\n"
      "    foreach (grid[, v]) return v;\n"
      "    foreach (bits[v]) return v;\n"
      "    return null;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  for (int line = 9; line <= 13; ++line) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "return expression in function 'f' is not "
                              "assignment-compatible with the function's "
                              "return type",
                              line, "12.8"))
        << line;
  }
}

TEST(JumpStatementElaboration, ForeachVariableOfAnUnreadDimensionHidesFormal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  class A; endclass\n"
      "  class H; int arr[4]; endclass\n"
      "  typedef int row_t[4];\n"
      "  bit [3:0] mod_bits;\n"
      "  function automatic int f(A v, H h);\n"
      "    int by_key[byte];\n"
      "    row_t row;\n"
      "    foreach (by_key[v]) return v;\n"
      "    foreach (row[v]) return v;\n"
      "    foreach (h.arr[v]) return v;\n"
      "    foreach (mod_bits[v]) return v;\n"
      "    return 0;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(JumpStatementElaboration, ReturnOfAModuleVariableIsCheckedAgainstType) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  class A; endclass\n"
      "  int g;\n"
      "  function automatic A f();\n"
      "    return g;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return expression in function 'f' is not "
                            "assignment-compatible with the function's return "
                            "type",
                            5, "12.8"));
}

TEST(JumpStatementElaboration, AFunctionsDeclarationHidesAModuleVariable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  class A; endclass\n"
      "  int g;\n"
      "  function automatic A f();\n"
      "    A g = new;\n"
      "    return g;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(JumpStatementElaboration, ReturnOfAClassPropertyIsCheckedAgainstType) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  class A; endclass\n"
      "  class B;\n"
      "    int count;\n"
      "    function A get();\n"
      "      return count;\n"
      "    endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return expression in function 'get' is not "
                            "assignment-compatible with the function's return "
                            "type",
                            6, "12.8"));
}

TEST(JumpStatementElaboration,
     ReturnOfAnInheritedPropertyIsCheckedAgainstType) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  class A; endclass\n"
      "  class P; int total; endclass\n"
      "  class D extends P;\n"
      "    function A first(); return total; endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return expression in function 'first' is not "
                            "assignment-compatible with the function's return "
                            "type",
                            5, "12.8"));
}

TEST(JumpStatementElaboration,
     ReturnOfAPropertyFromAnOutOfBlockMethodIsChecked) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  class A; endclass\n"
      "  class C;\n"
      "    int size;\n"
      "    extern function A pick();\n"
      "  endclass\n"
      "  function A C::pick();\n"
      "    return size;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return expression in function 'pick' is not "
                            "assignment-compatible with the function's return "
                            "type",
                            8, "12.8"));
}

TEST(JumpStatementElaboration, ReturnOfAPropertyFromAnEnumMethodIsChecked) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  class E;\n"
      "    int level;\n"
      "    function enum {LOW, HIGH} grade();\n"
      "      return level;\n"
      "    endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return expression in function 'grade' is not "
                            "assignment-compatible with the function's return "
                            "type",
                            5, "12.8"));
}

TEST(JumpStatementElaboration, ANearerDeclarationHidesAClassProperty) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  class A; endclass\n"
      "  class P; int item; int slot; endclass\n"
      "  class D extends P;\n"
      "    A item;\n"
      "    function A own(); return item; endfunction\n"
      "    function A local_one();\n"
      "      A slot = new;\n"
      "      return slot;\n"
      "    endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(JumpStatementElaboration, ReturnOfAVariableAroundAClassIsChecked) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  class A; endclass\n"
      "  int g;\n"
      "  class B;\n"
      "    function A get();\n"
      "      return g;\n"
      "    endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return expression in function 'get' is not "
                            "assignment-compatible with the function's return "
                            "type",
                            6, "12.8"));
}

TEST(JumpStatementElaboration, ReturnOfAUnitVariableFromAUnitClassIsChecked) {
  ElabFixture f;
  ElaborateSrc(
      "int g;\n"
      "class A; endclass\n"
      "class B;\n"
      "  function A get(); return g; endfunction\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return expression in function 'get' is not "
                            "assignment-compatible with the function's return "
                            "type",
                            4, "12.8"));
}

TEST(JumpStatementElaboration,
     ReturnOfAnEnclosingClassPropertyFromANestedClassIsChecked) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  class A; endclass\n"
      "  class O;\n"
      "    static int depth;\n"
      "    class I;\n"
      "      function A get(); return depth; endfunction\n"
      "    endclass\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return expression in function 'get' is not "
                            "assignment-compatible with the function's return "
                            "type",
                            6, "12.8"));
}

TEST(JumpStatementElaboration,
     ReturnOfAVariableAroundAClassFromAnOutOfBlockMethodIsChecked) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  class A; endclass\n"
      "  int g;\n"
      "  class C;\n"
      "    extern function A pick();\n"
      "  endclass\n"
      "  function A C::pick();\n"
      "    return g;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "return expression in function 'pick' is not "
                            "assignment-compatible with the function's return "
                            "type",
                            8, "12.8"));
}

TEST(JumpStatementElaboration, AClassDeclarationHidesAVariableAroundIt) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  class A; endclass\n"
      "  A p; A q; A e;\n"
      "  class B #(parameter int q = 1);\n"
      "    int p;\n"
      "    typedef enum {e, f} t;\n"
      "    function int one(); return p; endfunction\n"
      "    function int two(); return q; endfunction\n"
      "    function int three(); return e; endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(JumpStatementElaboration, AnUnknownBaseLeavesTheVariablesAroundUnread) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  class A; endclass\n"
      "  A g;\n"
      "  class P; int g; endclass\n"
      "  class B #(type T = P) extends T;\n"
      "    function int get(); return g; endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
