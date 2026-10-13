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

}  // namespace
