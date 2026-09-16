#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// The design of test/src/e2e/local_property_formals.sv around one
// assertion: clk rises at 5, 15, ..., 75 so that tick n is at 10n - 5; c is
// high at 1 and 4, data is 5 at 1 and 2, 9 at 3 to 5 and 2 from 6, and do1
// is 5 at 3, 2 at 6 and 0 elsewhere.
std::string LocalFormalSource(const std::string& items) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  int tick = 1;\n"
         "  logic c;\n"
         "  int data, do1;\n"
         "  int passes = 0;\n"
         "  int fails = 0;\n"
         "  int fail_time = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always #10 tick = tick + 1;\n"
         "  assign c = tick inside {1, 4};\n"
         "  assign data = (tick <= 2) ? 5 : (tick <= 5) ? 9 : 2;\n"
         "  assign do1 = (tick == 3) ? 5 : (tick == 6) ? 2 : 0;\n"
         "  property p_local(local input int lv);\n"
         "    @(posedge clk) c |-> ##2 (do1 == lv);\n"
         "  endproperty\n"
         "  property p_inferred(local int lv);\n"
         "    @(posedge clk) c |-> ##2 (do1 == lv);\n"
         "  endproperty\n"
         "  property p_live(int v);\n"
         "    @(posedge clk) c |-> ##2 (do1 == v);\n"
         "  endproperty\n" +
         items +
         "  initial #80 $finish;\n"
         "endmodule\n";
}

// The pass and fail counts at the ticks of the assertion whose whole
// property_spec is `spec`, and the time of its last failure.
struct LocalCounts {
  uint64_t passes;
  uint64_t fails;
  uint64_t fail_time;
};

LocalCounts CountsOfLocal(const std::string& spec) {
  SimFixture f;
  auto* passes =
      RunAndFindVar(LocalFormalSource("  p: assert property (" + spec +
                                      ") passes++; else begin fails++; "
                                      "fail_time = $time; end\n"),
                    f, "passes");
  if (passes == nullptr) return {~0ull, ~0ull, ~0ull};
  Variable* fails = f.ctx.FindVariable("fails");
  Variable* fail_time = f.ctx.FindVariable("fail_time");
  return {passes->value.ToUint64(), fails->value.ToUint64(),
          fail_time->value.ToUint64()};
}

// §16.12.19 by way of §16.8.2: a local variable formal argument of direction
// input is initialized from the actual when the attempt begins, so the
// attempt from 1 compares do1 at 3 with data's 5 at 1 and holds, and the
// one from 4 compares do1 at 6 with data's 9 at 4 and fails, at 55.
TEST(LocalPropertyFormals, ALocalInputFormalKeepsTheValueAtTheAttempt) {
  LocalCounts counts = CountsOfLocal("p_local(data)");
  EXPECT_EQ(counts.passes, 7u);
  EXPECT_EQ(counts.fails, 1u);
  EXPECT_EQ(counts.fail_time, 55u);
}

// §16.12.19: a local variable formal argument of a property with no
// direction written has direction input inferred, and reads the same.
TEST(LocalPropertyFormals, ALocalFormalsDirectionIsInferredInput) {
  LocalCounts counts = CountsOfLocal("p_inferred(data)");
  EXPECT_EQ(counts.passes, 7u);
  EXPECT_EQ(counts.fails, 1u);
  EXPECT_EQ(counts.fail_time, 55u);
}

// A formal not designated local stands for the actual as it is read at each
// tick: the attempt from 1 compares do1 at 3 with data's 9 at 3 and fails,
// at 25, and the one from 4 compares do1 at 6 with data's 2 at 6 and holds.
TEST(LocalPropertyFormals, AFormalNotLocalReadsTheActualAtEachTick) {
  LocalCounts counts = CountsOfLocal("p_live(data)");
  EXPECT_EQ(counts.passes, 7u);
  EXPECT_EQ(counts.fails, 1u);
  EXPECT_EQ(counts.fail_time, 25u);
}

}  // namespace
