#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// These tests observe the elaborator rule of 18.5.4 (and its footnote 13): the
// range_list of a uniqueness constraint shall contain only expressions that
// denote singular or array variables. The rule is about what an operand
// denotes, so it lives at the elaborator stage; the parser accepts the
// range_list tokens regardless. Each program is built from real class source so
// the check runs over the elaborated constraint, not a hand-built state.

// 18.5.4: a group of singular variables denotes variables and is accepted.
TEST(UniqueMemberForms, SingularVariableGroupAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand byte a;\n"
             "  rand byte b;\n"
             "  rand byte excluded;\n"
             "  constraint u { unique {a, b, excluded}; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.5.4: a slice of an unpacked array denotes an array variable, so a group
// mixing a slice with singular variables (the unique {b, a[2:3], excluded}
// example) is accepted.
TEST(UniqueMemberForms, ArraySliceMemberAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand byte a[5];\n"
             "  rand byte b;\n"
             "  rand byte excluded;\n"
             "  constraint u { unique {b, a[2:3], excluded}; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.5.4 / footnote 13: a range_list member shall denote a variable. A literal
// denotes no variable, so a group naming one is rejected.
TEST(UniqueMemberForms, LiteralMemberRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand byte a;\n"
             "  constraint u { unique {a, 5}; }\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a uniqueness constraint member shall denote a "
                            "singular or array variable",
                            3, "18.5.4"));
}

// 18.5.4 / footnote 13: an arithmetic expression is not a variable reference,
// so a group naming one is rejected.
TEST(UniqueMemberForms, ArithmeticExpressionMemberRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand byte a;\n"
             "  rand byte b;\n"
             "  constraint u { unique {a + b}; }\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a uniqueness constraint member shall denote a "
                            "singular or array variable",
                            4, "18.5.4"));
}

// 18.5.4: a singular member may be of real type as well as integral, so a group
// of real variables denotes variables and is accepted — the admitted-operand
// form exercised here is the real singular variable.
TEST(UniqueMemberForms, SingularRealVariableGroupAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand real a;\n"
             "  rand real b;\n"
             "  constraint u { unique {a, b}; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.5.4: a whole unpacked array variable (not only a slice of one) is an
// admitted member form, so a group naming an array beside a singular variable
// is accepted.
TEST(UniqueMemberForms, WholeUnpackedArrayMemberAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand byte a[5];\n"
             "  rand byte b;\n"
             "  constraint u { unique {a, b}; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.5.4 / footnote 13: a member/scope-qualified reference still denotes a
// variable. A group written with the explicit object handle (this.x) is
// accepted — this exercises the member-access member form, a distinct path from
// a bare identifier or an array select.
TEST(UniqueMemberForms, QualifiedMemberReferenceAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand byte a;\n"
             "  rand byte b;\n"
             "  constraint u { unique {this.a, this.b}; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.5.4: a member shall be of integral or real type. A string variable is
// plainly neither, so a group naming one is rejected even though the string
// does denote a variable.
TEST(UniqueMemberForms, NonIntegralNonRealMemberRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int a;\n"
             "  string s;\n"
             "  constraint u { unique {a, s}; }\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a uniqueness constraint member shall be of "
                            "integral or real type",
                            4, "18.5.4"));
}

// 18.5.4: no randc variable shall appear in the group, so a group naming a
// randc variable beside a rand one is rejected at the randc member.
TEST(UniqueMemberForms, RandcMemberRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  randc bit [1:0] a;\n"
             "  rand bit [1:0] b;\n"
             "  constraint u { unique {b, a}; }\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a uniqueness constraint member shall not be "
                            "a randc variable",
                            4, "18.5.4"));
}

// 18.5.4: an inherited randc variable is as much a randc variable of the
// group as one the class declares itself.
TEST(UniqueMemberForms, InheritedRandcMemberRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class B;\n"
             "  randc bit [2:0] a;\n"
             "endclass\n"
             "class C extends B;\n"
             "  rand bit [2:0] b[2];\n"
             "  constraint u { unique {b, a}; }\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a uniqueness constraint member shall not be "
                            "a randc variable",
                            6, "18.5.4"));
}

// 18.5.4 with 18.7: an inline constraint block holds a uniqueness constraint as
// a class's constraint block does, so the ban on a randc member reaches the
// group of randomize() with called through a handle in a module, whether the
// handle is declared in the module or in the procedure.
TEST(UniqueMemberForms, InlineRandcMemberThroughHandleRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand bit [1:0] a;\n"
             "  randc bit [1:0] b;\n"
             "endclass\n"
             "module m;\n"
             "  C c = new;\n"
             "  initial begin\n"
             "    C d;\n"
             "    d = new;\n"
             "    void'(c.randomize() with { unique {a, b}; });\n"
             "    void'(d.randomize() with { unique {b, a}; });\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a uniqueness constraint member shall not be a randc variable", 10,
      "18.5.4"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a uniqueness constraint member shall not be a randc variable", 11,
      "18.5.4"));
}

// 18.5.4 with 18.7: the same holds for randomize() with called on the object
// itself in one of its methods, with or without this.
TEST(UniqueMemberForms, InlineRandcMemberInMethodRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand bit [1:0] a;\n"
             "  randc bit [1:0] b;\n"
             "  function int f();\n"
             "    return randomize() with { unique {a, b}; };\n"
             "  endfunction\n"
             "  function int g();\n"
             "    return this.randomize() with { unique {b, a}; };\n"
             "  endfunction\n"
             "endclass\n"
             "module m; endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a uniqueness constraint member shall not be a randc variable", 5,
      "18.5.4"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "a uniqueness constraint member shall not be a randc variable", 8,
      "18.5.4"));
}

// 18.5.4 with 18.7: an inline group of rand members of the receiver's class is
// accepted wherever randomize() with is called.
TEST(UniqueMemberForms, InlineRandMembersAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand bit [1:0] a;\n"
             "  rand bit [1:0] b;\n"
             "  function int f();\n"
             "    return randomize() with { unique {a, b}; };\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c = new;\n"
             "  initial void'(c.randomize() with { unique {a, b}; });\n"
             "endmodule\n"));
}

}  // namespace
