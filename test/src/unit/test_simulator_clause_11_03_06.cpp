#include "helpers_scheduler.h"

using namespace delta;

// §11.3.6 "Assignment within an expression". The clause owns two runtime
// (simulator) requirements:
//   C2  An assignment expression evaluates the right-hand side, casts it to the
//       left-hand data type, updates the left-hand side, and returns the stored
//       value; the data type of the returned value is the data type of the
//       left-hand side.
//   C3  When the left-hand side is a concatenation, the returned value is an
//       unsigned integral value whose bit length is the sum of the operand
//       lengths.
//
// Both rules depend on how their inputs are produced: the target's declared
// width/signedness decides the cast in C2, and the concatenation target of C3
// is built from real §11.4.12 concatenation syntax. These tests therefore drive
// real source through the full pipeline (parse -> elaborate -> lower -> run)
// and observe the resulting variable values, rather than hand-building an AST
// and invoking the evaluator directly. The returned value is made observable by
// feeding it to an outer assignment, an arithmetic operand, or an `if`
// condition, so both the side effect (the target update) and the returned value
// are checked from real behavior.

namespace {

// Runs `src` through the full pipeline and asserts the listed variable values
// once the design settles.
void RunAndCheck(
    const std::string& src,
    std::initializer_list<std::pair<const char*, uint64_t>> checks) {
  SimFixture f;
  auto* design = ElaborateSrc(src, f);
  LowerRunAndCheck(f, design, checks);
}

// ---- C2: evaluate RHS, update the target, return the stored value ----------

// The simplest form: the parenthesized assignment updates its target and the
// value it returns is what the surrounding assignment stores.
TEST(AssignmentWithinExpression, SimpleAssignUpdatesTargetAndReturnsValue) {
  RunAndCheck(
      "module t;\n"
      "  logic [7:0] a, q;\n"
      "  initial begin\n"
      "    a = 8'd0;\n"
      "    q = (a = 8'd42);\n"
      "  end\n"
      "endmodule\n",
      {{"a", 42u}, {"q", 42u}});
}

// A right-associative chain: each inner assignment returns the value that the
// next outer assignment consumes, so every target ends up holding it.
TEST(AssignmentWithinExpression, ChainedAssignPropagatesToEveryTarget) {
  RunAndCheck(
      "module t;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial begin\n"
      "    a = 8'd0; b = 8'd0; c = 8'd0;\n"
      "    a = (b = (c = 8'd5));\n"
      "  end\n"
      "endmodule\n",
      {{"a", 5u}, {"b", 5u}, {"c", 5u}});
}

// A compound assignment operator inside an expression returns the updated value
// (10 + 5), confirming the returned value reflects the post-update contents.
TEST(AssignmentWithinExpression, CompoundAddAssignReturnsUpdatedValue) {
  RunAndCheck(
      "module t;\n"
      "  logic [7:0] x, q;\n"
      "  initial begin\n"
      "    x = 8'd10;\n"
      "    q = (x += 8'd5);\n"
      "  end\n"
      "endmodule\n",
      {{"x", 15u}, {"q", 15u}});
}

// The returned value takes the data type of the left-hand side: assigning a
// wider value to a 4-bit target casts it to 4 bits, and that cast value is what
// the expression yields (0xFF truncated to 0xF).
TEST(AssignmentWithinExpression, ReturnedValueUsesLeftHandWidth) {
  RunAndCheck(
      "module t;\n"
      "  logic [3:0] narrow;\n"
      "  logic [7:0] q;\n"
      "  initial begin\n"
      "    q = (narrow = 8'hFF);\n"
      "  end\n"
      "endmodule\n",
      {{"narrow", 0xFu}, {"q", 0x0Fu}});
}

// The returned value can be consumed by a surrounding operator: (a = 10) yields
// 10, which the `+ 20` adds to reach 30, while `a` retains the assigned 10.
TEST(AssignmentWithinExpression, ReturnedValueFeedsOuterArithmetic) {
  RunAndCheck(
      "module t;\n"
      "  logic [7:0] a, q;\n"
      "  initial begin\n"
      "    a = 8'd0;\n"
      "    q = (a = 8'd10) + 8'd20;\n"
      "  end\n"
      "endmodule\n",
      {{"a", 10u}, {"q", 30u}});
}

// The returned value drives control flow. Assigning 0 both updates `a` and
// yields a false condition, so the else branch runs.
TEST(AssignmentWithinExpression, ReturnedValueAsFalseIfCondition) {
  RunAndCheck(
      "module t;\n"
      "  logic [7:0] a, q;\n"
      "  initial begin\n"
      "    q = 8'd0;\n"
      "    if ((a = 8'd0)) q = 8'd1; else q = 8'd2;\n"
      "  end\n"
      "endmodule\n",
      {{"a", 0u}, {"q", 2u}});
}

// The counterpart: a nonzero assigned value yields a true condition and takes
// the then branch, confirming the branch selection follows the returned value.
TEST(AssignmentWithinExpression, ReturnedValueAsTrueIfCondition) {
  RunAndCheck(
      "module t;\n"
      "  logic [7:0] a, q;\n"
      "  initial begin\n"
      "    q = 8'd0;\n"
      "    if ((a = 8'd7)) q = 8'd1; else q = 8'd2;\n"
      "  end\n"
      "endmodule\n",
      {{"a", 7u}, {"q", 1u}});
}

// ---- C3: a concatenation target returns an unsigned sum-of-widths value -----

// The concatenation splits the assigned value across its operands, and the
// value it returns (fed to a 32-bit target) is the 16-bit concatenation result
// zero-extended, i.e. an unsigned value of width 8 + 8 = 16.
TEST(AssignmentWithinExpression, ConcatTargetSplitsValueAndReturnsIt) {
  RunAndCheck(
      "module t;\n"
      "  logic [7:0] hi, lo;\n"
      "  logic [31:0] q;\n"
      "  initial begin\n"
      "    q = ({hi, lo} = 16'hABCD);\n"
      "  end\n"
      "endmodule\n",
      {{"hi", 0xABu}, {"lo", 0xCDu}, {"q", 0x0000ABCDu}});
}

// The concatenation result is unsigned even when the right-hand side is a
// signed value whose width already matches the concatenation. A signed 0xFFFF
// would sign-extend to 0xFFFFFFFF if the result inherited its signedness;
// because the result is unsigned it zero-extends to 0x0000FFFF.
TEST(AssignmentWithinExpression, ConcatTargetResultIsUnsignedForSignedRhs) {
  RunAndCheck(
      "module t;\n"
      "  logic [7:0] hi, lo;\n"
      "  logic signed [15:0] src;\n"
      "  logic [31:0] q;\n"
      "  initial begin\n"
      "    src = 16'hFFFF;\n"
      "    q = ({hi, lo} = src);\n"
      "  end\n"
      "endmodule\n",
      {{"hi", 0xFFu}, {"lo", 0xFFu}, {"q", 0x0000FFFFu}});
}

// The returned value's width is the sum of the operand lengths, not the width
// of the right-hand side. A 4-bit and an 8-bit operand form a 12-bit result, so
// a 16-bit source is truncated to its low 12 bits (0xFABC -> 0xABC) both in the
// split targets and in the returned value.
TEST(AssignmentWithinExpression, ConcatTargetResultWidthIsSumOfOperandWidths) {
  RunAndCheck(
      "module t;\n"
      "  logic [3:0] hi;\n"
      "  logic [7:0] lo;\n"
      "  logic [31:0] q;\n"
      "  initial begin\n"
      "    q = ({hi, lo} = 16'hFABC);\n"
      "  end\n"
      "endmodule\n",
      {{"hi", 0xAu}, {"lo", 0xBCu}, {"q", 0x00000ABCu}});
}

}  // namespace
