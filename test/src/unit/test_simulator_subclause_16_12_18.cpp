#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <utility>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// The design of test/src/e2e/typed_property_formals.sv around one
// assertion: clk rises at 5, 15, ..., 75 so that tick n is at 10n - 5; v is
// 8'h02 at 2 and 4 and 8'h01 at 6, w is high at 2 and 6, go at 1, 3, 5 and
// 7, b at 2, 3, 6, 7 and 8, and c at 2 and 4.
std::string TypedSource(const std::string& items) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  int tick = 1;\n"
         "  logic [7:0] v;\n"
         "  logic w, go, b, c;\n"
         "  int passes = 0;\n"
         "  int fails = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always #10 tick = tick + 1;\n"
         "  assign v = (tick inside {2, 4}) ? 8'h02\n"
         "           : (tick inside {6}) ? 8'h01 : 8'h00;\n"
         "  assign w = tick inside {2, 6};\n"
         "  assign go = tick inside {1, 3, 5, 7};\n"
         "  assign b = tick inside {2, 3, 6, 7, 8};\n"
         "  assign c = tick inside {2, 4};\n"
         "  property p_untyped(x, y);\n"
         "    @(posedge clk) x |-> y;\n"
         "  endproperty\n"
         "  property p_bit(bit x, y);\n"
         "    @(posedge clk) x |-> y;\n"
         "  endproperty\n"
         "  property p_ev(event ev);\n"
         "    @(ev) v == 2 |-> w;\n"
         "  endproperty\n"
         "  property p_prop(property q);\n"
         "    @(posedge clk) go |-> q;\n"
         "  endproperty\n"
         "  property p_not(property q);\n"
         "    @(posedge clk) not q;\n"
         "  endproperty\n"
         "  property p_id(property q);\n"
         "    @(posedge clk) q;\n"
         "  endproperty\n"
         "  property p_not_or(property q);\n"
         "    @(posedge clk) not q or 1'b0;\n"
         "  endproperty\n"
         "  property p_seq(sequence s);\n"
         "    @(posedge clk) s |-> c;\n"
         "  endproperty\n" +
         items +
         "  initial #80 $finish;\n"
         "endmodule\n";
}

// The pass and fail counts at the ticks of the assertion whose whole
// property_spec is `spec`.
std::pair<uint64_t, uint64_t> CountsOfTyped(const std::string& spec) {
  SimFixture f;
  auto* passes = RunAndFindVar(TypedSource("  p: assert property (" + spec +
                                           ") passes++; else fails++;\n"),
                               f, "passes");
  if (passes == nullptr) return {~0ull, ~0ull};
  Variable* fails = f.ctx.FindVariable("fails");
  return {passes->value.ToUint64(), fails->value.ToUint64()};
}

// §16.12.18 by way of §16.8.1: a formal typed with a data type takes its
// actual cast to the type, so p_bit's x reads the low bit of the 8-bit v,
// high at 6 alone, where w holds, while p_untyped's x reads v whole, high
// at 2, 4 and 6, where w fails it at 4.
TEST(TypedPropertyFormals, ADataTypedFormalCastsItsActual) {
  auto untyped = CountsOfTyped("p_untyped(v, w)");
  EXPECT_EQ(untyped.first, 7u);
  EXPECT_EQ(untyped.second, 1u);
  auto typed = CountsOfTyped("p_bit(v, w)");
  EXPECT_EQ(typed.first, 8u);
  EXPECT_EQ(typed.second, 0u);
}

// §16.12.18 by way of §16.8.1: a formal of type event takes an event
// expression, the edge and the signal, which the property's clock is
// evaluated on: v == 2 at 2 and 4, where w fails it at 4.
TEST(TypedPropertyFormals, AnEventFormalTakesTheInstancesEvent) {
  auto counts = CountsOfTyped("p_ev(posedge clk)");
  EXPECT_EQ(counts.first, 7u);
  EXPECT_EQ(counts.second, 1u);
}

// §16.12.18: a boolean may be passed to a formal of type property, being a
// property_expr: go |-> b fails at 1 and 5.
TEST(TypedPropertyFormals, ABooleanMayBePassedToAPropertyFormal) {
  auto counts = CountsOfTyped("@(posedge clk) p_prop(b)");
  EXPECT_EQ(counts.first, 6u);
  EXPECT_EQ(counts.second, 2u);
}

// §16.12.18: a sequence_expr may be passed to a formal of type property:
// go |-> b ##1 c fails at 1 and 5 with b low and at 8 with c low after 7.
TEST(TypedPropertyFormals, ASequenceMayBePassedToAPropertyFormal) {
  auto counts = CountsOfTyped("@(posedge clk) p_prop(b ##1 c)");
  EXPECT_EQ(counts.first, 5u);
  EXPECT_EQ(counts.second, 3u);
}

// §16.12.18: a property_expr that is neither may be passed as well: go |->
// (b or nexttime c) fails at 6 alone, with b low and c low a tick later.
TEST(TypedPropertyFormals, APropertyMayBePassedToAPropertyFormal) {
  auto counts = CountsOfTyped("@(posedge clk) p_prop(b or nexttime c)");
  EXPECT_EQ(counts.first, 7u);
  EXPECT_EQ(counts.second, 1u);
}

// §16.12.18: a reference to a formal of type property stands where a
// property_expr may, the operand of not among them: b |-> c holds at every
// tick but 3, 6, 7 and 8, where b is high and c low, so its negation holds
// at those four alone.
TEST(TypedPropertyFormals, APropertyFormalMayStandUnderNot) {
  auto counts = CountsOfTyped("p_not(b |-> c)");
  EXPECT_EQ(counts.first, 4u);
  EXPECT_EQ(counts.second, 4u);
}

// §16.12.18: the same negation written after the assertion's own clock,
// where the instance is read as a boolean the elaborator promotes to the
// root of a tree.
TEST(TypedPropertyFormals, APropertyFormalUnderNotAfterAClock) {
  auto counts = CountsOfTyped("@(posedge clk) p_not(b |-> c)");
  EXPECT_EQ(counts.first, 4u);
  EXPECT_EQ(counts.second, 4u);
}

// §16.12.18: a body that is the formal alone stands for the actual: b |-> c
// fails at 3, 6, 7 and 8.
TEST(TypedPropertyFormals, APropertyFormalMayBeTheWholeBody) {
  auto counts = CountsOfTyped("p_id(b |-> c)");
  EXPECT_EQ(counts.first, 4u);
  EXPECT_EQ(counts.second, 4u);
}

// §16.12.18: the negation under an or with a false operand, a property of
// operands rather than the clocked boolean form, holds where not q does.
TEST(TypedPropertyFormals, APropertyFormalUnderNotInAPropertyOfOperands) {
  auto counts = CountsOfTyped("p_not_or(b |-> c)");
  EXPECT_EQ(counts.first, 4u);
  EXPECT_EQ(counts.second, 4u);
}

// §16.12.18: a formal of type sequence takes a sequence_expr and may stand
// as the antecedent of an implication: go ##1 b matches at 2, 6 and 8, a
// tick after go, and c fails it at 6 and 8.
TEST(TypedPropertyFormals, ASequenceFormalMayStandAsAnAntecedent) {
  auto counts = CountsOfTyped("p_seq(go ##1 b)");
  EXPECT_EQ(counts.first, 6u);
  EXPECT_EQ(counts.second, 2u);
}

}  // namespace
