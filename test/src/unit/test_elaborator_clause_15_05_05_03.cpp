#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §15.5.5.3: the equality, inequality, case-equality, and case-inequality
// operators are the only comparison operators permitted on event variables,
// and an event may be used as a Boolean test. These uses elaborate cleanly.
TEST(EventComparisonElaborator, AllowedComparisonOperatorsAccepted) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  event a, b;\n"
      "  logic w, x, y, z, t;\n"
      "  initial begin\n"
      "    w = (a == b);\n"
      "    x = (a != b);\n"
      "    y = (a === b);\n"
      "    z = (a !== b);\n"
      "    if (a) t = 1;\n"
      "  end\n"
      "endmodule\n"));
}

// §15.5.5.3: an event may be compared against the special value null with any
// of the permitted equality operators, including the case-equality forms.
TEST(EventComparisonElaborator, ComparisonAgainstNullAccepted) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  event a;\n"
      "  logic w, x, y, z;\n"
      "  initial begin\n"
      "    w = (a == null);\n"
      "    x = (a != null);\n"
      "    y = (a === null);\n"
      "    z = (a !== null);\n"
      "  end\n"
      "endmodule\n"));
}

// §15.5.5.3: a relational operator is not among the permitted operators for an
// event variable, so applying one is illegal.
TEST(EventComparisonElaborator, RelationalOperatorRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  event a, b;\n"
      "  logic x;\n"
      "  initial x = (a < b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §15.5.5.3: an arithmetic operator on an event operand is likewise illegal,
// even when the other operand is not an event.
TEST(EventComparisonElaborator, ArithmeticOperatorRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  event a;\n"
      "  logic [31:0] x;\n"
      "  initial x = a + 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §15.5.5.3: a bitwise operator on an event operand is not a permitted
// comparison and is rejected.
TEST(EventComparisonElaborator, BitwiseOperatorRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  event a, b;\n"
      "  logic x;\n"
      "  initial x = (a & b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §15.5.5.3: a unary operator applied to an event operand is outside the set of
// permitted operations and is rejected.
TEST(EventComparisonElaborator, UnaryOperatorRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  event a;\n"
      "  logic [31:0] x;\n"
      "  initial x = ~a;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §15.5.5.3: a postfix increment/decrement on an event operand is likewise not
// among the permitted operations and is rejected.
TEST(EventComparisonElaborator, PostfixIncrementOperatorRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  event a;\n"
      "  logic [31:0] x;\n"
      "  initial x = a++;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
