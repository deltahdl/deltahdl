#include "fixture_elaborator.h"

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
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand byte a;\n"
             "  constraint u { unique {a, 5}; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.5.4 / footnote 13: an arithmetic expression is not a variable reference,
// so a group naming one is rejected.
TEST(UniqueMemberForms, ArithmeticExpressionMemberRejected) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand byte a;\n"
             "  rand byte b;\n"
             "  constraint u { unique {a + b}; }\n"
             "endclass\n"
             "module m; endmodule\n"));
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
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand int a;\n"
             "  string s;\n"
             "  constraint u { unique {a, s}; }\n"
             "endclass\n"
             "module m; endmodule\n"));
}

}  // namespace
