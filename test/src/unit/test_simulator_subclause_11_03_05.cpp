#include "helpers_scheduler.h"

using namespace delta;

// §11.3.5 "Operator expression short circuiting". The clause owns three
// normative statements, all runtime (simulator) rules:
//   C1  The operators &&, ||, ->, and ?: shall use short-circuit evaluation:
//       an operand whose value is not needed to determine the result shall not
//       be evaluated.
//   C2  Every other operator shall NOT short circuit; all of its operand
//       expressions are always evaluated.
//   C3  When short circuiting occurs, the side effects (and run-time errors) of
//       the skipped operand shall not occur.
// The clause frames all three around "the side effects caused by calling a
// function". These tests therefore observe the rule the way the LRM does: a
// function with a real, observable side effect appears as the operand that may
// be skipped, and the test checks whether that side effect happened after the
// full pipeline (elaborate -> lower -> run) executes real source.
//
// The side-effect vehicle is `incr`, a function that bumps the module-scope
// counter `cnt` through an inout argument (the copy-back happens only when the
// call is actually evaluated) and returns a truthy value. `cnt` moving from 0
// to 1 means the operand was evaluated; `cnt` staying 0 means it was skipped.

namespace {

// Wraps a procedural body in a module that defines the side-effecting `incr`
// function and the counter it mutates. The body runs in an initial block after
// `cnt` is cleared to a known 0.
inline std::string Mod(const std::string& body) {
  return "module t;\n"
         "  logic [7:0] a, b, q, cnt;\n"
         "  function logic incr(inout logic [7:0] c);\n"
         "    c = c + 8'd1;\n"
         "    return 1'b1;\n"
         "  endfunction\n"
         "  initial begin\n"
         "    cnt = 8'd0;\n" +
         body +
         "  end\n"
         "endmodule\n";
}

// ---- C1: the short-circuiting operators skip the unneeded operand ----------

// && with a false left operand never evaluates the right operand, so the call's
// side effect does not occur.
TEST(ShortCircuit, LogicalAndFalseLhsSkipsRhsCall) {
  EXPECT_EQ(RunAndGet(Mod("    a = 8'd0;\n"
                          "    q = a && incr(cnt);\n"),
                      "cnt"),
            0u);
}

// || with a true left operand never evaluates the right operand.
TEST(ShortCircuit, LogicalOrTrueLhsSkipsRhsCall) {
  EXPECT_EQ(RunAndGet(Mod("    a = 8'd1;\n"
                          "    q = a || incr(cnt);\n"),
                      "cnt"),
            0u);
}

// -> (implication) with a false left operand is already true, so it never
// evaluates the right operand.
TEST(ShortCircuit, ImplicationFalseLhsSkipsRhsCall) {
  EXPECT_EQ(RunAndGet(Mod("    a = 8'd0;\n"
                          "    q = a -> incr(cnt);\n"),
                      "cnt"),
            0u);
}

// ?: evaluates only the selected branch. Both branches call incr(cnt); if the
// unselected one were also evaluated, cnt would reach 2. A true condition
// selects the then-branch.
TEST(ShortCircuit, ConditionalTrueSkipsUnselectedBranchCall) {
  EXPECT_EQ(RunAndGet(Mod("    a = 8'd1;\n"
                          "    q = a ? incr(cnt) : incr(cnt);\n"),
                      "cnt"),
            1u);
}

// A false condition selects the else-branch; the then-branch call is skipped.
TEST(ShortCircuit, ConditionalFalseSkipsUnselectedBranchCall) {
  EXPECT_EQ(RunAndGet(Mod("    a = 8'd0;\n"
                          "    q = a ? incr(cnt) : incr(cnt);\n"),
                      "cnt"),
            1u);
}

// ---- C1 complement: the same operators DO evaluate the operand when its ----
// ---- value is actually required ------------------------------------------

// && with a true left operand must evaluate the right operand.
TEST(ShortCircuit, LogicalAndTrueLhsEvaluatesRhsCall) {
  EXPECT_EQ(RunAndGet(Mod("    a = 8'd1;\n"
                          "    q = a && incr(cnt);\n"),
                      "cnt"),
            1u);
}

// || with a false left operand must evaluate the right operand.
TEST(ShortCircuit, LogicalOrFalseLhsEvaluatesRhsCall) {
  EXPECT_EQ(RunAndGet(Mod("    a = 8'd0;\n"
                          "    q = a || incr(cnt);\n"),
                      "cnt"),
            1u);
}

// -> with a true left operand must evaluate the right operand.
TEST(ShortCircuit, ImplicationTrueLhsEvaluatesRhsCall) {
  EXPECT_EQ(RunAndGet(Mod("    a = 8'd1;\n"
                          "    q = a -> incr(cnt);\n"),
                      "cnt"),
            1u);
}

// ---- C2: every other operator always evaluates both operands (negative) ----

// Bitwise & does not short circuit: a zero left operand still evaluates the
// right operand's call. This is the LRM's `result1` distinction from `&&`.
TEST(ShortCircuit, BitwiseAndZeroLhsStillEvaluatesRhsCall) {
  EXPECT_EQ(RunAndGet(Mod("    a = 8'd0;\n"
                          "    q = a & incr(cnt);\n"),
                      "cnt"),
            1u);
}

// Bitwise | does not short circuit: an all-ones left operand still evaluates
// the right operand's call.
TEST(ShortCircuit, BitwiseOrAllOnesLhsStillEvaluatesRhsCall) {
  EXPECT_EQ(RunAndGet(Mod("    a = 8'hFF;\n"
                          "    q = a | incr(cnt);\n"),
                      "cnt"),
            1u);
}

// Logical equivalence <-> is deliberately excluded from the short-circuiting
// set, so it always evaluates both operands regardless of the left value.
TEST(ShortCircuit, EquivalenceStillEvaluatesRhsCall) {
  EXPECT_EQ(RunAndGet(Mod("    a = 8'd0;\n"
                          "    q = a <-> incr(cnt);\n"),
                      "cnt"),
            1u);
}

// Arithmetic + always evaluates both operands.
TEST(ShortCircuit, AdditionStillEvaluatesRhsCall) {
  EXPECT_EQ(RunAndGet(Mod("    a = 8'd0;\n"
                          "    q = a + incr(cnt);\n"),
                      "cnt"),
            1u);
}

// Logical equality == always evaluates both operands.
TEST(ShortCircuit, EqualityStillEvaluatesRhsCall) {
  EXPECT_EQ(RunAndGet(Mod("    a = 8'd5;\n"
                          "    q = (a == incr(cnt));\n"),
                      "cnt"),
            1u);
}

// ---- C3: LRM worked example — side effect nested inside a subexpression -----

// LRM `result1 = regA & (regB | myFunc(regC))`: neither & nor | short circuits,
// so the nested call fires even though the outer left operand is zero.
TEST(ShortCircuit, LrmBitwiseFormEvaluatesNestedCall) {
  EXPECT_EQ(RunAndGet(Mod("    a = 8'd0;\n"
                          "    b = 8'd0;\n"
                          "    q = a & (b | incr(cnt));\n"),
                      "cnt"),
            1u);
}

// LRM `result2 = regA && (regB || myFunc(regC))`: a zero regA short circuits
// the whole right subexpression, so the nested call — and its side effect —
// never occurs.
TEST(ShortCircuit, LrmLogicalFormSkipsNestedCall) {
  EXPECT_EQ(RunAndGet(Mod("    a = 8'd0;\n"
                          "    b = 8'd0;\n"
                          "    q = a && (b || incr(cnt));\n"),
                      "cnt"),
            0u);
}

// ---- Input form: the short-circuit expression as a statement condition -----
// The rule applies wherever the operator expression is evaluated, not only as
// an assignment right-hand side. Here the same && drives an if condition.

// A false left operand short circuits the if condition, so the call is skipped.
TEST(ShortCircuit, LogicalAndShortCircuitsInIfCondition) {
  EXPECT_EQ(RunAndGet(Mod("    a = 8'd0;\n"
                          "    if (a && incr(cnt)) q = 8'd1;\n"),
                      "cnt"),
            0u);
}

// A true left operand forces the right operand of the if condition to run.
TEST(ShortCircuit, LogicalAndEvaluatesInIfCondition) {
  EXPECT_EQ(RunAndGet(Mod("    a = 8'd1;\n"
                          "    if (a && incr(cnt)) q = 8'd1;\n"),
                      "cnt"),
            1u);
}

// ---- Input form: multi-operator chain grouped by §11.3.2 associativity ------
// `a && b && incr(cnt)` is a real multi-operator expression whose operands are
// grouped left-to-right per §11.3.2 into `(a && b) && incr(cnt)`. The short
// circuit operates on that grouping end-to-end through the full pipeline.

// A false operand at the head of the chain short circuits the whole chain, so
// the trailing call never runs.
TEST(ShortCircuit, AndChainShortCircuitsPerAssociativity) {
  EXPECT_EQ(RunAndGet(Mod("    a = 8'd0;\n"
                          "    b = 8'd1;\n"
                          "    q = a && b && incr(cnt);\n"),
                      "cnt"),
            0u);
}

// When every leading operand of the chain is true, the trailing call is
// required and therefore evaluated.
TEST(ShortCircuit, AndChainEvaluatesWhenLeadingOperandsTrue) {
  EXPECT_EQ(RunAndGet(Mod("    a = 8'd1;\n"
                          "    b = 8'd1;\n"
                          "    q = a && b && incr(cnt);\n"),
                      "cnt"),
            1u);
}

}  // namespace
