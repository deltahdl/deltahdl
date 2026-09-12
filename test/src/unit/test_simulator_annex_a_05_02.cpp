#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// A.5.2 writes the initial value of a UDP's reg output as `output reg
// port_identifier [ = constant_expression ]`, an expression rather than one of
// A.5.3's init_val literals, so what the output holds when simulation begins
// is what the expression evaluates to. Every case here runs a whole design --
// elaborate, lower, run -- and reads the output terminal's net once the run
// settles, because the expression is evaluated when the instance is lowered and
// a parse of the primitive alone does not reach that.
//
// The primitive's table holds its state on every row (§29.3.6's `-` for no
// change), and the instance's inputs are never driven, so the value the net
// settles at is the initial value and nothing else: a primitive that seeded
// the wrong value would show it, and one that seeded none would leave x.

// The design one case runs: a sequential primitive whose reg output carries
// `initial_value` as its A.5.2 initial value, instantiated once with its
// output on `q` and its inputs on nets nothing drives.
std::string HoldingDesign(const char* initial_value) {
  return std::string("primitive udp_hold (output reg q = ") + initial_value +
         ", input a, input b);\n"
         "  table\n"
         "  // a b : q : q+\n"
         "    ? ? : ? : - ;\n"
         "  endtable\n"
         "endprimitive\n"
         "module m;\n"
         "  wire a, b, q;\n"
         "  udp_hold g (q, a, b);\n"
         "endmodule\n";
}

// Elaborates, lowers and runs `src`, then returns what the run left on `name`,
// one character per bit through Logic4Vec::ToString: '0', '1', 'x' or 'z'. A
// source that does not elaborate returns "<no-design>" and a run that declared
// no such signal returns "<no-signal>", so neither is read as a driven value.
std::string SettledValue(const std::string& src, const char* name) {
  SimFixture f;
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  if (design == nullptr) return "<no-design>";
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable(name);
  EXPECT_NE(var, nullptr);
  return var == nullptr ? "<no-signal>" : var->value.ToString();
}

// `~1'b0` is 1 and `1'b1 ^ 1'b1` is 0. Each expression ends in the literal of
// the opposite value, so a reading that took the initial value off the last
// literal written would seed 0 for the first and 1 for the second.
TEST(UdpPortInitialValueSim, InitialValueIsTheExpressionEvaluated) {
  EXPECT_EQ(SettledValue(HoldingDesign("~1'b0"), "q"), "1");
  EXPECT_EQ(SettledValue(HoldingDesign("1'b1 ^ 1'b1"), "q"), "0");
}

// A literal wider than the one bit the reg holds seeds its least significant
// bit, which is what §10.7's truncation of an assignment to a narrower
// variable keeps: `3` seeds 1 and `2'b10` seeds 0.
TEST(UdpPortInitialValueSim, InitialValueIsTheLiteralsLowBit) {
  EXPECT_EQ(SettledValue(HoldingDesign("3"), "q"), "1");
  EXPECT_EQ(SettledValue(HoldingDesign("2'b10"), "q"), "0");
}

}  // namespace
