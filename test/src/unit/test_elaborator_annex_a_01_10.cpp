#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ConstraintElaboration, ClassWithConstraintDeclaration) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  constraint c { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ConstraintElaboration, ClassWithStaticConstraint) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  static constraint c { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ConstraintElaboration, ClassWithMultipleConstraints) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x, y;\n"
             "  constraint c1 { x > 0; }\n"
             "  constraint c2 { y > 0; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ConstraintElaboration, ClassWithConstraintPrototype) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  constraint c;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ConstraintElaboration, ClassWithExternConstraintPrototype) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  rand int x;\n"
      "  extern constraint c;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "explicit constraint prototype 'c' in class 'C' "
                            "has no external constraint block",
                            3, "18.5.1"));
}

TEST(ConstraintElaboration, ClassWithPureConstraintPrototype) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  rand int x;\n"
      "  pure constraint c;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "pure constraint 'c' needs an abstract class, and "
                            "class 'C' is not declared virtual",
                            3, "18.5.2"));
}

TEST(ConstraintElaboration, ConstraintWithDynamicOverride) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  constraint :initial c { x > 0; }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ConstraintElaboration, ExternConstraintDeclaration) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "  extern constraint c;\n"
             "endclass\n"
             "constraint C::c { x > 0; }\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ConstraintElaboration, ConstraintWithComplexBlock) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int a, b, c;\n"
             "  constraint order_c {\n"
             "    solve a before b;\n"
             "    a > 0;\n"
             "    soft b == 1;\n"
             "    if (a > 5) { b < 10; }\n"
             "    foreach (c[i]) c[i] > 0;\n"
             "    unique { a, b };\n"
             "    disable soft a;\n"
             "  }\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

constexpr const char* kNoArrayMethod =
    "'()' follows a constraint_primary that is no array built-in method";

TEST(ConstraintElaboration, ParenthesesOnANonArrayMethodPrimaryAreErrors) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  rand int x, y;\n"
      "  rand int a [];\n"
      "  string s;\n"
      "  function int f(); return 1; endfunction\n"
      "  static function int g(); return 1; endfunction\n"
      "  constraint c1 { disable soft randomize(); }\n"
      "  constraint c2 { solve f() before x; }\n"
      "  constraint c3 { solve x before C::g(); }\n"
      "  constraint c4 { disable soft a.foo(); }\n"
      "  constraint c5 { solve x.size() before y; }\n"
      "  constraint c6 { if (x > 0) { disable soft s.len(); } }\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoArrayMethod, 7, "A.1.10"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoArrayMethod, 8, "A.1.10"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoArrayMethod, 9, "A.1.10"));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kNoArrayMethod, 10, "A.1.10"));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kNoArrayMethod, 11, "A.1.10"));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kNoArrayMethod, 12, "A.1.10"));
}

TEST(ConstraintElaboration, ParenthesesOnAnArrayMethodPrimaryAreAccepted) {
  ElabFixture f;
  ElabOk(
      "typedef int arr_t [];\n"
      "class D;\n"
      "  rand int q [$];\n"
      "endclass\n"
      "class C;\n"
      "  rand int x;\n"
      "  rand int a [];\n"
      "  rand arr_t t;\n"
      "  rand D d;\n"
      "  function int f(); return 1; endfunction\n"
      "  constraint c1 { solve a.size() before x; disable soft a.size(); }\n"
      "  constraint c2 { solve t.size() before x; }\n"
      "  constraint c3 { solve d.q.size() before x; }\n"
      "  constraint c4 { x == f(); }\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kNoArrayMethod, 11, "A.1.10"));
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kNoArrayMethod, 12, "A.1.10"));
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kNoArrayMethod, 13, "A.1.10"));
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kNoArrayMethod, 14, "A.1.10"));
}

TEST(ConstraintElaboration, ParenthesesOnAClassHandlePrimaryAreErrors) {
  ElabFixture f;
  ElabOk(
      "class D;\n"
      "  function int size(); return 1; endfunction\n"
      "endclass\n"
      "class C;\n"
      "  rand int x;\n"
      "  D d;\n"
      "  constraint c { solve d.size() before x; }\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoArrayMethod, 7, "A.1.10"));
}

TEST(ConstraintElaboration, ParenthesesOnAnInlineNonArrayPrimaryAreErrors) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  rand int x;\n"
      "  rand int a [];\n"
      "endclass\n"
      "module m;\n"
      "  int arr [];\n"
      "  initial begin\n"
      "    static C c = new;\n"
      "    void'(c.randomize() with { disable soft x.size(); });\n"
      "    void'(c.randomize() with { disable soft a.size(); });\n"
      "    void'(c.randomize() with { disable soft arr.size(); });\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoArrayMethod, 9, "A.1.10"));
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kNoArrayMethod, 10, "A.1.10"));
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kNoArrayMethod, 11, "A.1.10"));
}

}  // namespace
