#pragma once

#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

inline std::string MulticlockSource(const std::string& items) {
  return "module t;\n"
         "  logic clk0 = 0;\n"
         "  logic clk1 = 0;\n"
         "  int tick = 1;\n"
         "  logic sig0, sig1;\n"
         "  int passes = 0;\n"
         "  int fails = 0;\n"
         "  int last_pass = 0;\n"
         "  always #5 clk0 = ~clk0;\n"
         "  always #10 tick = tick + 1;\n"
         "  initial begin\n"
         "    #12 clk1 = 1;\n"
         "    #8 clk1 = 0;\n"
         "    #7 clk1 = 1;\n"
         "    #8 clk1 = 0;\n"
         "    #10 clk1 = 1;\n"
         "    #5 clk1 = 0;\n"
         "    #7 clk1 = 1;\n"
         "    #8 clk1 = 0;\n"
         "    #7 clk1 = 1;\n"
         "    #6 clk1 = 0;\n"
         "  end\n"
         "  assign sig0 = tick inside {1, 2, 5, 7};\n"
         "  assign sig1 = tick inside {3, 5};\n" +
         items +
         "  initial #80 $finish;\n"
         "endmodule\n";
}

struct MulticlockCounts {
  uint64_t passes;
  uint64_t fails;
  uint64_t last_pass;
};

inline MulticlockCounts CountsOfAssertionItem(const std::string& item) {
  SimFixture f;
  auto* passes = RunAndFindVar(MulticlockSource(item), f, "passes");
  if (passes == nullptr) return {~0ull, ~0ull, ~0ull};
  Variable* fails = f.ctx.FindVariable("fails");
  Variable* last_pass = f.ctx.FindVariable("last_pass");
  return {passes->value.ToUint64(), fails->value.ToUint64(),
          last_pass->value.ToUint64()};
}

inline std::string CountedAssertion(const std::string& property) {
  return "  p: assert property (" + property +
         ") begin passes++; last_pass = $time; end else fails++;\n";
}

inline MulticlockCounts CountsOfMulticlock(const std::string& spec,
                                           const std::string& prelude = "") {
  return CountsOfAssertionItem(prelude +
                               CountedAssertion("@(posedge clk0) " + spec));
}

inline void ExpectAsWithoutTheRedundantClock(const std::string& spec,
                                             const std::string& plain,
                                             const std::string& prelude = "") {
  MulticlockCounts named = CountsOfMulticlock(spec, prelude);
  MulticlockCounts bare = CountsOfMulticlock(plain);
  EXPECT_NE(bare.passes + bare.fails, 0u) << plain;
  EXPECT_EQ(named.passes, bare.passes) << spec;
  EXPECT_EQ(named.fails, bare.fails) << spec;
  EXPECT_EQ(named.last_pass, bare.last_pass) << spec;
}
