#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

namespace {

// §12.8 asks a return in a function returning a value for an expression of the
// right type, assignment compatible with the return type (§6.22.3) whatever
// form the expression takes. A string variable is no integral value without a
// cast (§6.16), and a class handle is none at all (§8.4).
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

// A string method giving an integral value is a call whose type this check
// does not read, and an int variable fits an int function.
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

// A return type written as a name is checked as the type it names: a class
// takes a handle of itself or of a class derived from it, and neither a handle
// of an unrelated class nor an integer (§8.4).
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

// A typedef of string takes no real, as string itself takes none.
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

// A class's own typedef hides a name the module declares (§8.10 with §23.9):
// the method's t_t is string, which takes the string literal, and not the
// module's enumeration, which would not.
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

// A begin-end block is a scope of its own (§23.9), so a variable it declares
// hides the formal of the same name, and a return inside it gives the
// block's variable. Here that is the class handle, which the class function
// takes, and not the int formal, which it would not.
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

// A nested block's unpacked array hides the class formal of its name too, so
// the return gives the array the function's array type takes, and no class
// handle.
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

// A variable a for loop's initialization declares is local to the loop
// (§12.7.1), so it hides the formal of its name, and a return inside the loop
// gives the loop's class handle, which the class function takes. A for loop
// that assigns the formal declares nothing.
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

// A foreach loop variable is local to the loop and hides the formal of its
// name (§12.7.3). Over a fixed-size, a dynamic or a queue dimension, unpacked
// or packed, it is an int, which the class function does not take. The
// module's array is walked as the function's own are, and a loop variable
// left out stands for no dimension.
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

// Over an associative dimension a foreach loop variable has the index type,
// here a byte, and a typedef's dimensions, a member's and those of a variable
// the function cannot see are not plain from the declarations in scope; each
// loop variable still hides the class formal, so none is read as one.
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

// A name the function does not declare is found in the module around it
// (§23.9), so the return gives the module's int, which the class function does
// not take.
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

// The function's own declaration hides the module's variable of its name, so
// the return gives the function's class handle.
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

// A name a class method does not declare is found among its class's properties
// (§8.4), so the return gives the property's int, which the method's class
// return type does not take.
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

// A property the class inherits is found too (§8.13).
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

// A method defined outside its class's body reads that class's properties as
// one written inside it does (§8.24).
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

// §6.19.3's check of a value returned from a function returning an enumeration
// reads no class method, so the property's int is reported here, not taken by
// the enumeration without a cast.
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

// A class's own property hides an inherited one of its name, and the method's
// own declaration hides a property, so each return gives a class handle.
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

}  // namespace
