#pragma once

#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "simulator/variable.h"

inline std::string CounterPropertySource(const std::string& spec,
                                         const std::string& items) {
  return "module t;\n"
         "  logic clk = 0, rst = 0;\n"
         "  int v = 0, passes = 0, fails = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always @(posedge clk) v <= v + 1;\n" +
         items +
         "  property counted;\n"
         "    int x;\n"
         "    @(posedge clk) " +
         spec +
         ";\n"
         "  endproperty\n"
         "  assert property (counted) passes++; else fails++;\n"
         "  initial #100 $finish;\n"
         "endmodule\n";
}

inline void ExpectCounterPropertyCounts(const std::string& spec,
                                        uint64_t passes, uint64_t fails,
                                        const std::string& items = "") {
  SimFixture f;
  auto* counted =
      RunAndFindVar(CounterPropertySource(spec, items), f, "passes");
  ASSERT_NE(counted, nullptr) << spec;
  EXPECT_EQ(counted->value.ToUint64(), passes) << spec;
  EXPECT_EQ(f.ctx.FindVariable("fails")->value.ToUint64(), fails) << spec;
}
