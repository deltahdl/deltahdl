#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(DefaultArgumentElaboration, MissingArgNoDefaultError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int add(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "  int x;\n"
      "  initial x = add(1);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "missing argument 'b' in call to 'add'", 6,
                            "13.5.3"));
}

// §13.5.3: an argument with no default shall be given, or the compiler issues
// an error. The report that does so names the subclause stating the rule, so a
// caller learns which rule was enforced without matching the wording of the
// message.
TEST(DefaultArgumentElaboration, MissingArgumentWithNoDefaultNames13_5_3) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int add(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "  int x;\n"
      "  initial x = add(1);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "missing argument 'b' in call to 'add'", 6,
                            "13.5.3"));
}

TEST(DefaultArgumentElaboration, MissingArgWithDefaultOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int inc(int a, int step = 1);\n"
      "    return a + step;\n"
      "  endfunction\n"
      "  int x;\n"
      "  initial x = inc(5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DefaultArgumentElaboration, AllDefaultsNoArgsOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function int compute(int a = 1, int b = 2);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "  int x;\n"
      "  initial x = compute();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DefaultArgumentElaboration, EmptyPlaceholderWithDefaultOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task read(int j = 0, int k, int data = 1);\n"
      "  endtask\n"
      "  initial read(, 5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DefaultArgumentElaboration, EmptyPlaceholderNoDefaultError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task read(int j = 0, int k, int data = 1);\n"
      "  endtask\n"
      "  initial read(1, , 7);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "missing argument 'k' in call to 'read'", 4,
                            "13.5.3"));
}

TEST(DefaultArgumentElaboration, DefaultOnNonAnsiDeclError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function int foo;\n"
      "    input int x = 5;\n"
      "    foo = x;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "default argument values are only allowed with", 2,
                            "13.5.3"));
}

TEST(DefaultArgumentElaboration, DefaultRefsDeclaringScopeOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, w;\n"
      "  task t1(output logic o = a);\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DefaultArgumentElaboration, DefaultRefsUndeclaredNameError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic a, w;\n"
      "  task t2(output logic o = b);\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "default value for 'o' references 'b'", 3,
                            "13.5.3"));
}

// §11.9: the member a tagged union expression names is a member of the union
// type its context gives it, no name of any scope, so a default value of
// `tagged Invalid` references nothing §13.5.3 has to resolve (#6353).
TEST(DefaultArgumentElaboration, TaggedMemberNameInDefaultIsNoName) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef union tagged { void Invalid; int Valid; } VInt;\n"
      "  function void h(VInt a, VInt b = tagged Invalid); endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// The value a tagged expression carries is an expression of the default, and
// a name in it is still resolved in the declaring scope.
TEST(DefaultArgumentElaboration, TaggedMemberValueInDefaultIsResolved) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  typedef union tagged { void Invalid; int Valid; } VInt;\n"
      "  function void h(VInt b = tagged Valid k); endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "default value for 'b' references 'k' which is not "
                            "declared in the subroutine's declaring scope",
                            3, "13.5.3"));
}

}  // namespace
