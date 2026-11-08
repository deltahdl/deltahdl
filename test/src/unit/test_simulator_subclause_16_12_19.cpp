#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

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

struct LocalCounts {
  uint64_t passes;
  uint64_t fails;
  uint64_t fail_time;
};

LocalCounts CountsOfLocal(const std::string& spec,
                          const std::string& items = "") {
  SimFixture f;
  auto* passes =
      RunAndFindVar(LocalFormalSource(items + "  p: assert property (" + spec +
                                      ") passes++; else begin fails++; "
                                      "fail_time = $time; end\n"),
                    f, "passes");
  if (passes == nullptr) return {~0ull, ~0ull, ~0ull};
  Variable* fails = f.ctx.FindVariable("fails");
  Variable* fail_time = f.ctx.FindVariable("fail_time");
  return {passes->value.ToUint64(), fails->value.ToUint64(),
          fail_time->value.ToUint64()};
}

TEST(LocalPropertyFormals, ALocalInputFormalKeepsTheValueAtTheAttempt) {
  LocalCounts counts = CountsOfLocal("p_local(data)");
  EXPECT_EQ(counts.passes, 7u);
  EXPECT_EQ(counts.fails, 1u);
  EXPECT_EQ(counts.fail_time, 55u);
}

TEST(LocalPropertyFormals, ALocalFormalsDirectionIsInferredInput) {
  LocalCounts counts = CountsOfLocal("p_inferred(data)");
  EXPECT_EQ(counts.passes, 7u);
  EXPECT_EQ(counts.fails, 1u);
  EXPECT_EQ(counts.fail_time, 55u);
}

TEST(LocalPropertyFormals, AFormalNotLocalReadsTheActualAtEachTick) {
  LocalCounts counts = CountsOfLocal("p_live(data)");
  EXPECT_EQ(counts.passes, 7u);
  EXPECT_EQ(counts.fails, 1u);
  EXPECT_EQ(counts.fail_time, 25u);
}

TEST(LocalPropertyFormals, ALocalFormalTakesItsDeclaredType) {
  const std::string kItems =
      "  typedef struct packed { logic [3:0] hi, lo; } pair_t;\n"
      "  property p_sel(local input logic [8:1] lv);\n"
      "    @(posedge clk) c |-> ##2 lv[1];\n"
      "  endproperty\n"
      "  property p_member(local input pair_t lp);\n"
      "    @(posedge clk) c |-> ##2 (do1 == lp.lo);\n"
      "  endproperty\n"
      "  property p_write(local input logic [8:1] lv);\n"
      "    @(posedge clk) (c, lv[8] = 1) |-> ##2 (lv == 8'h85);\n"
      "  endproperty\n";
  LocalCounts sel = CountsOfLocal("p_sel(data)", kItems);
  EXPECT_EQ(sel.passes, 8u);
  EXPECT_EQ(sel.fails, 0u);
  LocalCounts member = CountsOfLocal("p_member(data)", kItems);
  EXPECT_EQ(member.passes, 7u);
  EXPECT_EQ(member.fails, 1u);
  EXPECT_EQ(member.fail_time, 55u);
  LocalCounts write = CountsOfLocal("p_write(data)", kItems);
  EXPECT_EQ(write.passes, 7u);
  EXPECT_EQ(write.fails, 1u);
  EXPECT_EQ(write.fail_time, 55u);
}

}  // namespace
