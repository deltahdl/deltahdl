#include <initializer_list>

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

// C2 holds for every left-hand side §10.4 admits, not only a plain identifier.
// A compound assignment written as an expression reached one writer -- the one
// that answers for an associative element -- so every other target was updated
// by nothing at all and only the returned value showed the operation had
// happened. Each case below reads the target as well as the value, since the
// value alone was already right.

// An unpacked array element. `arr[2]` keeps 10 where the write was dropped.
TEST(AssignmentWithinExpression, CompoundAssignToAnArrayElementUpdatesIt) {
  RunAndCheck(
      "module t;\n"
      "  int arr [0:3];\n"
      "  int q;\n"
      "  initial begin\n"
      "    arr[2] = 10;\n"
      "    q = (arr[2] += 5);\n"
      "  end\n"
      "endmodule\n",
      {{"arr[2]", 15u}, {"q", 15u}});
}

// A bit-select of a packed variable, which names a one-bit window rather than
// the variable it is cut from. The other seven bits standing is what says the
// window was written rather than the whole of `d`.
TEST(AssignmentWithinExpression, CompoundAssignToABitSelectWritesOnlyThatBit) {
  RunAndCheck(
      "module t;\n"
      "  logic [7:0] d;\n"
      "  logic q;\n"
      "  initial begin\n"
      "    d = 8'h00;\n"
      "    q = (d[3] += 1'b1);\n"
      "  end\n"
      "endmodule\n",
      {{"d", 0x08u}, {"q", 1u}});
}

// A part-select, loaded beforehand so three answers separate: 0xF0 where the
// write was dropped, 0xF3 where the named bits took it, and 0x03 where the
// value replaced the variable whole.
TEST(AssignmentWithinExpression,
     CompoundAssignToAPartSelectWritesOnlyThoseBits) {
  RunAndCheck(
      "module t;\n"
      "  logic [7:0] d;\n"
      "  logic [3:0] q;\n"
      "  initial begin\n"
      "    d = 8'hF0;\n"
      "    q = (d[3:0] += 4'd3);\n"
      "  end\n"
      "endmodule\n",
      {{"d", 0xF3u}, {"q", 3u}});
}

// A packed struct member, which the expression form named no writer for at all.
// The neighbouring member is read too, since a write that took the whole
// variable would reach it.
TEST(AssignmentWithinExpression, CompoundAssignToAStructMemberUpdatesIt) {
  RunAndCheck(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [3:0] hi;\n"
      "    logic [3:0] lo;\n"
      "  } pair_t;\n"
      "  pair_t s;\n"
      "  int q;\n"
      "  initial begin\n"
      "    s.hi = 4'd2;\n"
      "    s.lo = 4'd5;\n"
      "    q = (s.lo += 4'd3);\n"
      "  end\n"
      "endmodule\n",
      {{"s", 0x28u}, {"q", 8u}});
}

// §11.3.6 gives the returned value "the data type of the left-hand side", and a
// select is a left-hand side of its own type: `d[3:0]` names four bits however
// wide the operation that produced the value was. The write was already right,
// each writer sizing what it stores by what it is storing into; it is the value
// the surrounding expression reads that carried the operation's width.
TEST(AssignmentWithinExpression,
     CompoundAssignToPartSelectYieldsTheSelectWidth) {
  RunAndCheck(
      "module t;\n"
      "  logic [7:0] d;\n"
      "  logic [7:0] q;\n"
      "  initial begin\n"
      "    d = 8'h00;\n"
      "    q = (d[3:0] += 8'hFF);\n"
      "  end\n"
      "endmodule\n",
      {{"d", 0x0Fu}, {"q", 0x0Fu}});
}

// An unpacked array index names a whole element (§7.4.2), so the left-hand type
// is the element's and not the one bit a select of a packed object would name.
// This is the shape 2f14f4b6f withdrew over: measuring the select against the
// base variable truncated the value to one bit and sign-extended it back. The
// added operand is wider than the element, so the operation is sixteen bits and
// 310 truncates to the element's 54.
TEST(AssignmentWithinExpression,
     CompoundAssignToArrayElementYieldsElementWidth) {
  RunAndCheck(
      "module t;\n"
      "  byte arr [0:3];\n"
      "  logic [15:0] q;\n"
      "  initial begin\n"
      "    arr[2] = 8'd10;\n"
      "    q = (arr[2] += 16'd300);\n"
      "  end\n"
      "endmodule\n",
      {{"q", 54u}});
}

// A queue element's width comes from its container rather than from any
// variable the left-hand side names, and the same answer has to reach the
// yielded value.
TEST(AssignmentWithinExpression,
     CompoundAssignToQueueElementYieldsElementWidth) {
  RunAndCheck(
      "module t;\n"
      "  byte qu [$];\n"
      "  logic [15:0] q;\n"
      "  initial begin\n"
      "    qu.push_back(8'd10);\n"
      "    q = (qu[0] += 16'd300);\n"
      "  end\n"
      "endmodule\n",
      {{"q", 54u}});
}

// §11.3.6 over a packed struct member, whose width is the member's. The width
// comes back from the writer here: a member access resolves to a window of the
// variable rather than to a variable of its own, so measuring it from the
// left-hand side finds nothing.
TEST(AssignmentWithinExpression,
     CompoundAssignToStructMemberYieldsMemberWidth) {
  RunAndCheck(
      "module t;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } pair_t;\n"
      "  pair_t s;\n"
      "  logic [15:0] q;\n"
      "  initial begin\n"
      "    s = 16'h000A;\n"
      "    q = (s.lo += 16'd300);\n"
      "  end\n"
      "endmodule\n",
      {{"q", 54u}});
}

}  // namespace
