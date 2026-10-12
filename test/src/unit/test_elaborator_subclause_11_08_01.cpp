#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §11.8.1: an operator yields an integral or a real value, and neither type
// has a member or a built-in method, so a method call or a member select
// applied to the result is reported: a binary operator's, a compound
// assignment's, a unary operator's, an increment's and inside's (§11.4.13).
TEST(ExpressionTypeElaboration, MemberOfOperatorResultIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int x;\n"
      "  real r;\n"
      "  bit b;\n"
      "  initial (x + 1).run();\n"
      "  initial (-r).run();\n"
      "  initial (x++).run();\n"
      "  initial b = (x inside {1, 2}).m;\n"
      "  initial (x += 2).run();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'run' is no member or built-in method of the "
                            "integral or real value an operator yields",
                            5, "11.8.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'run' is no member or built-in method of the "
                            "integral or real value an operator yields",
                            6, "11.8.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'run' is no member or built-in method of the "
                            "integral or real value an operator yields",
                            7, "11.8.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'m' is no member or built-in method of the "
                            "integral or real value an operator yields",
                            8, "11.8.1"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'run' is no member or built-in method of the "
                            "integral or real value an operator yields",
                            9, "11.8.1"));
  EXPECT_EQ(f.diag.ErrorCount(), 5u);
}

// §11.3.6: a parenthesized assignment yields the value it assigns, of its
// left-hand side's type, so the methods of a string apply to `(s = t)`.
TEST(ExpressionTypeElaboration, ParenthesizedAssignmentKeepsItsTargetsMethods) {
  EXPECT_TRUE(
      ElabOk("module top;\n"
             "  string s, t;\n"
             "  int n;\n"
             "  initial n = (s = t).len();\n"
             "endmodule\n"));
}

}  // namespace
