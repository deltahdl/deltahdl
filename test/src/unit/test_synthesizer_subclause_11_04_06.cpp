#include <gtest/gtest.h>

#include <cstdint>

#include "helpers_synth_assign.h"

using namespace delta;

namespace {

// The test fails on a synthesizer that answers a netlist whose every bit of `y`
// is constant zero, which is what `assign y = a ==? 4'b10?z;` lowers to today:
// `SynthLower::LowerBinaryBit` in src/synthesizer/synth_lower.cpp answers
// `AigGraph::kConstFalse` for the operator, so the netlist says no value of `a`
// ever matches. Table 11-10 of §11.4.6 defines `a ==? b` as "a equals b, x and
// z values in b act as wildcards", and §11.4.6 rules that "a wildcard bit
// matches any bit value (0, 1, z, or x) in the corresponding bit of the left
// operand being compared against it" while any other bit is compared as for the
// logical equality operator, yielding 1'b1 when the relation is true.
//
// The literal wildcards its two low bits and compares its two high bits, so the
// answer is one exactly when bit 3 of `a` is one and bit 2 of `a` is zero,
// whatever bits 1 and 0 carry. Bit 0 of `y` carries that answer and every bit
// above it is zero.
//
// The module declares `a` alone, so there is no second input to drive and the
// sweep runs over the sixteen values of `a`.
TEST(WildcardEqualitySynthesis,
     WildcardEqualityTreatsTheRightOperandsWildcardsAsDontCare) {
  ExpectAssignSweep(
      ModuleAssigning("input [3:0] a", "a ==? 4'b10?z"), 1,
      [](uint64_t a, uint64_t) -> uint64_t {
        return (((a >> 3) & 1U) == 1U && ((a >> 2) & 1U) == 0U) ? 1U : 0U;
      });
}

// The test fails on a fix that reaches `==?` and leaves `!=?` answering
// `AigGraph::kConstFalse`, which the case above passes. Table 11-10 of §11.4.6
// defines `a !=? b` as "a does not equal b, x and z values in b act as
// wildcards" in the one table that defines `a ==? b`, so the two are owed
// together, and the wildcard positions are read from the same literal. The
// answer is therefore the negation of the case above over every value of `a`,
// which is what a netlist left constant zero disagrees with wherever the
// wildcard equality holds.
TEST(WildcardEqualitySynthesis,
     WildcardInequalityIsTheNegationOfWildcardEquality) {
  ExpectAssignSweep(
      ModuleAssigning("input [3:0] a", "a !=? 4'b10?z"), 1,
      [](uint64_t a, uint64_t) -> uint64_t {
        return (((a >> 3) & 1U) == 1U && ((a >> 2) & 1U) == 0U) ? 0U : 1U;
      });
}

// The test fails when `assign y = a ==? b;` lowers to a netlist rather than to
// a report. §11.4.6 rules that `==?` treats "x and z values in a given bit
// position of their right operand as a wildcard", and a bare identifier carries
// no literal text to read those positions out of, so a graph built anyway would
// silently answer a plain equality for an operator the design wrote wildcards
// for. The netlist is the failure this guards against, because it is accepted
// without a word and nothing tells the reader the wildcards were dropped.
TEST(WildcardEqualitySynthesis,
     WildcardEqualityWithANonLiteralRightOperandIsReported) {
  ExpectAssignReported(
      "input [3:0] a, input [3:0] b", "a ==? b",
      "'a ==? b' with a right operand that is not an integer literal has no "
      "lowering in the synthesizer",
      "11.4.6");
}

// The test fails when `assign y = a !=? b;` lowers to a netlist rather than to
// a report. §11.4.6 gives `!=?` the same reading of its right operand that it
// gives `==?`, so a right operand that is not a literal leaves the same nothing
// to read a wildcard mask out of. This is its own case rather than a second
// expectation inside the one above, because `!=?` arrives as
// `TokenKind::kBangEqQuestion` and a fix reaching only
// `TokenKind::kEqEqQuestion` passes that case and fails this one.
TEST(WildcardEqualitySynthesis,
     WildcardInequalityWithANonLiteralRightOperandIsReported) {
  ExpectAssignReported(
      "input [3:0] a, input [3:0] b", "a !=? b",
      "'a !=? b' with a right operand that is not an integer literal has no "
      "lowering in the synthesizer",
      "11.4.6");
}

// The test fails when `assign y = a ==? 4'd5;` and `assign y = a ==? 5;` answer
// different functions of `a`. A literal written with no base carries decimal
// digits alone, so it holds no x or z for §11.4.6 to make a wildcard of, and
// what is left of the operator is the §11.4.5 comparison of the two operands.
// A lowering that reads the wildcard positions out of the digits that follow
// the base finds no base here, and one that then compares against the value it
// decoded rather than against the literal compares `a` against zero: it answers
// one at `a` of zero and zero at `a` of five, which is the pair of values this
// case reads back.
TEST(WildcardEqualitySynthesis,
     WildcardEqualityWithAnUnbasedLiteralComparesIt) {
  ExpectAssignSweep(
      ModuleAssigning("input [3:0] a", "a ==? 5"), 1,
      [](uint64_t a, uint64_t) -> uint64_t { return a == 5U ? 1U : 0U; });
}

}  // namespace
