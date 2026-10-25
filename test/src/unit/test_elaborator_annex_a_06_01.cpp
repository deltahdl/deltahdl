#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// A.6.1 (printed page 1197): a continuous assignment's target is the net_lvalue
// of a net_assignment or the variable_lvalue of a variable_assignment, and
// A.8.5 (printed page 1212) writes neither in parentheses, whole or as an
// element of a concatenation. The same target written without them stands.
TEST(ContinuousAssignElaboration, ParenthesizedTargetIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire a, b, c, d;\n"
      "  assign (a) = b;\n"
      "  assign {(c), a} = d;\n"
      "  assign {c, a} = {b, d};\n"
      "endmodule\n",
      f);
  for (uint32_t line : {3u, 4u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "continuous assignment target is not a net or "
                              "variable lvalue",
                              line, "10.3"));
  }
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "continuous assignment target is not a net or "
                             "variable lvalue",
                             5, "10.3"));
}

// A.6.1 (printed page 1197): an assignment to a variable takes the second form
// of continuous_assign, with no drive strength and a delay_control alone, and a
// member of a structure variable is a variable_lvalue as the variable is. A
// member access taken of an interface instance's name reaches the instance's
// net, which keeps the net form's strength.
TEST(ContinuousAssignElaboration, MemberOfStructureVariableTakesVariableForm) {
  ElabFixture f;
  Elaborate(
      "interface bus;\n"
      "  wire y;\n"
      "endinterface\n"
      "module m;\n"
      "  typedef struct packed { logic a; logic b; } s_t;\n"
      "  s_t s;\n"
      "  logic x;\n"
      "  bus i();\n"
      "  assign (weak0, weak1) s.a = x;\n"
      "  assign #(1, 2) s.b = x;\n"
      "  assign (weak0, weak1) i.y = x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "drive strength not allowed on continuous assignment to a variable", 9,
      "10.3.4"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "multiple delays not allowed on continuous assignment to a variable", 10,
      "10.3.3"));
  EXPECT_FALSE(ReportedError(
      f.diag.Diagnostics(),
      "drive strength not allowed on continuous assignment to a variable", 11,
      "10.3.4"));
}

// A.6.1 (printed page 1197) with A.8.5 (printed page 1212): a streaming
// concatenation is among the forms of variable_lvalue alone, so a continuous
// assignment to one takes the variable form, and a second delay and a drive
// strength are each reported as written on an assignment to a variable, the
// strength not as one on a net.
TEST(ContinuousAssignElaboration, StreamingTargetTakesVariableForm) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic [3:0] v, x;\n"
      "  assign #(1, 2) {>>{v}} = x;\n"
      "  assign (weak0, weak1) {>>{v}} = x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "multiple delays not allowed on continuous assignment to a variable", 3,
      "10.3.3"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "drive strength not allowed on continuous assignment to a variable", 4,
      "10.3.4"));
  EXPECT_FALSE(ReportedError(
      f.diag.Diagnostics(),
      "drive strength on continuous assignment applies only to scalar nets", 4,
      "10.3.4"));
}

// A.6.1 (printed page 1197): each operand of a net_alias is a net_lvalue, which
// A.8.5 (printed page 1212) writes in no parentheses, whole or as an element of
// a concatenation.
TEST(NetAliasElaboration, ParenthesizedOperandIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire a, b, c;\n"
      "  wire [1:0] d;\n"
      "  alias (a) = b;\n"
      "  alias {(c), a} = d;\n"
      "endmodule\n",
      f);
  for (uint32_t line : {4u, 5u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "alias operand is not a net_lvalue: a net with "
                              "constant selects, or a concatenation or "
                              "pattern of these",
                              line, "10.11"));
  }
}

}  // namespace
