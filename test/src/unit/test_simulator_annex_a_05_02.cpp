#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

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

TEST(UdpPortInitialValueSim, InitialValueIsTheExpressionEvaluated) {
  EXPECT_EQ(SettledValue(HoldingDesign("~1'b0"), "q"), "1");
  EXPECT_EQ(SettledValue(HoldingDesign("1'b1 ^ 1'b1"), "q"), "0");
}

TEST(UdpPortInitialValueSim, InitialValueIsTheLiteralsLowBit) {
  EXPECT_EQ(SettledValue(HoldingDesign("3"), "q"), "1");
  EXPECT_EQ(SettledValue(HoldingDesign("2'b10"), "q"), "0");
}

}  // namespace
