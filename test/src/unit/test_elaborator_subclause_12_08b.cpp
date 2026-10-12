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

}  // namespace
