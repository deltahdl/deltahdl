#include <gtest/gtest.h>

#include <cstdint>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

// These tests drive 18.12.1's std::randomize() with { constraint_block } form
// end to end: each elaborates a real module, calls the scope randomize with an
// inline constraint block from source over variables of the current scope, and
// copies the outcome into module variables the harness reads. The behavior
// observed is that of parse/elaborate/run applying the rule through the
// production scope randomize path (TryEvalScopeRandomizeCall in
// eval_randomize.cpp), not a hand-built solver state. The clause's own rule is
// the random/state split it introduces: the arguments named in the call become
// the random variables, and every other variable a constraint mentions is a
// state variable read at its current value. The draw is deterministic for a
// given source, so each RunAndGet re-run reproduces the same values.

// 18.12.1: the with block is actually applied to the named argument. Before the
// with form was wired the constraint block was dropped and the argument was
// drawn unconstrained; forcing an exact value and observing the argument land
// on it confirms the inline constraint reached the solve.
TEST(ScopeRandomizeWith, InlineConstraintConstrainsNamedArgument) {
  const char* src =
      "module top;\n"
      "  int okv;\n"
      "  int aval;\n"
      "  initial begin\n"
      "    bit [7:0] a;\n"
      "    okv = std::randomize(a) with { a == 200; };\n"
      "    aval = a;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "okv"), 1u);     // constraints satisfied -> 1
  EXPECT_EQ(RunAndGet(src, "aval"), 200u);  // with block pinned the argument
}

// 18.12.1: a variable that is not one of the scope randomize arguments is a
// state variable, so a constraint over the random argument reads its current
// value as a constant. Here the task argument length is named in no list, so
// a > length constrains the randomized a against length's held value; a is a
// byte, length is 100, and every draw lands above 100.
TEST(ScopeRandomizeWith, NonArgumentIsStateVariableReadAsConstant) {
  const char* src =
      "module top;\n"
      "  int okv;\n"
      "  int aval;\n"
      "  task run(int length);\n"
      "    bit [7:0] a;\n"
      "    okv = std::randomize(a) with { a > length; };\n"
      "    aval = a;\n"
      "  endtask\n"
      "  initial run(100);\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "okv"), 1u);     // 101..255 is reachable -> succeeds
  EXPECT_GT(RunAndGet(src, "aval"), 100u);  // drawn above the state value
}

// 18.12.1: the same with block, evaluated under two different current values of
// a state variable, produces draws that respect each one -- mirroring the
// clause's two calls std::randomize(a) with { a > length; } made with distinct
// lengths. The value is read from the state variable at each call rather than
// chosen by the solver, so raising length between calls raises the floor the
// draw must clear.
TEST(ScopeRandomizeWith, StateVariableValueGovernsEachDraw) {
  const char* src =
      "module top;\n"
      "  int a_lo;\n"
      "  int a_hi;\n"
      "  initial begin\n"
      "    bit [7:0] a;\n"
      "    int length;\n"
      "    int s1, s2;\n"
      "    length = 50;\n"
      "    s1 = std::randomize(a) with { a > length; };\n"
      "    a_lo = a;\n"
      "    length = 200;\n"
      "    s2 = std::randomize(a) with { a > length; };\n"
      "    a_hi = a;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_GT(RunAndGet(src, "a_lo"), 50u);   // first call read length == 50
  EXPECT_GT(RunAndGet(src, "a_hi"), 200u);  // second call read length == 200
}

// 18.12.1: with the with form, only the arguments become random variables;
// every other local variable is a state variable and keeps its current value
// across the call. Here b is a live local left out of the argument list, so
// randomizing a leaves b at the value it was assigned, exactly as the clause
// holds all non-argument variables as state.
TEST(ScopeRandomizeWith, NonArgumentLocalKeepsItsValue) {
  const char* src =
      "module top;\n"
      "  int okv;\n"
      "  int aval;\n"
      "  int bval;\n"
      "  initial begin\n"
      "    bit [7:0] a;\n"
      "    bit [7:0] b;\n"
      "    b = 8'd77;\n"
      "    okv = std::randomize(a) with { a == 30; };\n"
      "    aval = a;\n"
      "    bval = b;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "okv"), 1u);
  EXPECT_EQ(RunAndGet(src, "aval"), 30u);  // the sole random variable was drawn
  EXPECT_EQ(RunAndGet(src, "bval"), 77u);  // not an argument, so held as state
}

// 18.12.1: the arguments named in the call are jointly the random variables and
// a constraint may relate them to a state variable, as in the clause's
// std::randomize(a, b) with { a + b < length; }. Both a and b are drawn and
// their sum is checked against length's held value; length is a byte-sum
// ceiling of 10 the draw stays below.
TEST(ScopeRandomizeWith, JointConstraintOverArgumentsAgainstStateValue) {
  const char* src =
      "module top;\n"
      "  int okv;\n"
      "  int sumv;\n"
      "  task run(int length);\n"
      "    bit [3:0] a;\n"
      "    bit [3:0] b;\n"
      "    okv = std::randomize(a, b) with { a + b < length; };\n"
      "    sumv = a + b;\n"
      "  endtask\n"
      "  initial run(10);\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "okv"), 1u);    // a joint solution below 10 exists
  EXPECT_LT(RunAndGet(src, "sumv"), 10u);  // and the drawn sum respects it
}

// 18.12.1: every argument named in the with-form call becomes a random
// variable, whether or not the constraint block mentions it -- as in the
// clause's first call std::randomize(a, b, c) with { a < b; a + b < length; },
// which names c though no constraint touches it. A named argument left
// uninitialized begins all-x; after the call $isunknown reads 0 for it, so it
// was drawn a concrete value as a random variable rather than held all-x as a
// state variable, while the constrained argument still lands on its pinned
// value.
TEST(ScopeRandomizeWith, NamedArgumentWithoutConstraintIsStillRandomized) {
  const char* src =
      "module top;\n"
      "  int okv;\n"
      "  int aval;\n"
      "  int unk_c;\n"
      "  initial begin\n"
      "    logic [7:0] a;\n"
      "    logic [7:0] c;\n"  // both begin all-x
      "    okv = std::randomize(a, c) with { a == 5; };\n"
      "    aval = a;\n"
      "    unk_c = $isunknown(c);\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "okv"), 1u);
  EXPECT_EQ(RunAndGet(src, "aval"), 5u);  // the constrained argument was pinned
  EXPECT_EQ(RunAndGet(src, "unk_c"),
            0u);  // the unconstrained argument was drawn
}

// 18.12.1: because a non-argument variable is a state variable read as a fixed
// constant, its current value can leave the with constraint over the random
// arguments with no solution, and the scope randomize then fails. length holds
// 100, larger than any sum two 4-bit arguments can reach, so a + b > length can
// never hold: the call returns 0 and, per 18.6.3, the arguments keep the values
// they held before the failed call.
TEST(ScopeRandomizeWith, UnsatisfiableAgainstStateValueFails) {
  const char* src =
      "module top;\n"
      "  int okv;\n"
      "  int aval;\n"
      "  int bval;\n"
      "  task run(int length);\n"
      "    bit [3:0] a;\n"
      "    bit [3:0] b;\n"
      "    a = 4'd9;\n"
      "    b = 4'd8;\n"
      "    okv = std::randomize(a, b) with { a + b > length; };\n"
      "    aval = a;\n"
      "    bval = b;\n"
      "  endtask\n"
      "  initial run(100);\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "okv"), 0u);   // no draw satisfies a + b > 100
  EXPECT_EQ(RunAndGet(src, "aval"), 9u);  // failed solve leaves a unchanged
  EXPECT_EQ(RunAndGet(src, "bval"), 8u);  // and b unchanged
}

// 18.12.1: the clause's own example randomizes int-typed scope variables --
// task stimulus( int length ) with local int a, b, c. This drives that operand
// type end to end: two int arguments are jointly randomized under the with
// block and their sum is checked against the int state variable length, so the
// rule holds for a plain int just as for a sized bit vector. Lower bounds keep
// the wide int domain small enough for the generate-and-test solve to land
// quickly.
TEST(ScopeRandomizeWith, IntArgumentsRandomizedAgainstStateValue) {
  const char* src =
      "module top;\n"
      "  int okv;\n"
      "  int sumv;\n"
      "  task run(int length);\n"
      "    int a;\n"
      "    int b;\n"
      "    okv = std::randomize(a, b) with { a < 5; b < 5; a + b < length; };\n"
      "    sumv = a + b;\n"
      "  endtask\n"
      "  initial run(6);\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "okv"), 1u);   // a joint int solution below 6 exists
  EXPECT_LT(RunAndGet(src, "sumv"), 6u);  // and the drawn int sum respects it
}

// 18.12.1: a non-argument operand a with-block reads as a state constant may be
// an elaboration-time constant rather than a variable. A module parameter takes
// a different resolution path than a local variable, so drive it explicitly:
// the random argument a is constrained against the parameter LIMIT, and every
// draw lands above the parameter's value, confirming the constant folded into
// the solve exactly as a held state value would.
TEST(ScopeRandomizeWith, ParameterServesAsStateConstant) {
  const char* src =
      "module top;\n"
      "  parameter int LIMIT = 100;\n"
      "  int okv;\n"
      "  int aval;\n"
      "  initial begin\n"
      "    bit [7:0] a;\n"
      "    okv = std::randomize(a) with { a > LIMIT; };\n"
      "    aval = a;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "okv"), 1u);     // 101..255 is reachable
  EXPECT_GT(RunAndGet(src, "aval"), 100u);  // drawn above the parameter value
}

// 18.12.1: a localparam is the other 11.2.1 constant form and resolves on its
// own path; the with-block reads it as a state constant just the same. The
// random argument a is constrained above the localparam FLOOR, and every draw
// clears it.
TEST(ScopeRandomizeWith, LocalparamServesAsStateConstant) {
  const char* src =
      "module top;\n"
      "  localparam int FLOOR = 200;\n"
      "  int okv;\n"
      "  int aval;\n"
      "  initial begin\n"
      "    bit [7:0] a;\n"
      "    okv = std::randomize(a) with { a > FLOOR; };\n"
      "    aval = a;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "okv"), 1u);     // 201..255 is reachable
  EXPECT_GT(RunAndGet(src, "aval"), 200u);  // drawn above the localparam value
}

// 18.12.1: the with form applies to the variables of whatever current scope
// holds the call. The clause writes it inside a task; here the same call sits
// in a function, randomizing a function-local variable. The inline constraint
// pins the local, and the function returns the scope randomize status, so the
// with block is observed applying to a function scope just as to a task or
// initial block.
TEST(ScopeRandomizeWith, WithFormInsideFunctionScope) {
  const char* src =
      "module top;\n"
      "  int okv;\n"
      "  int aval;\n"
      "  function int rand_it();\n"
      "    bit [7:0] a;\n"
      "    int r;\n"
      "    r = std::randomize(a) with { a == 88; };\n"
      "    aval = a;\n"
      "    return r;\n"
      "  endfunction\n"
      "  initial okv = rand_it();\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "okv"), 1u);  // solve succeeded inside the function
  EXPECT_EQ(RunAndGet(src, "aval"), 88u);  // the with block pinned the local
}

}  // namespace
