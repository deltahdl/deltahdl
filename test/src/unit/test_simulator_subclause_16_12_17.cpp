#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// The design of test/src/e2e/recursive_property.sv around one assertion:
// clk rises at 5, 15, ..., 75 so that tick n is at 10n - 5; a and hold are
// high at every tick but 6, done at 5, go at 2 and 7, s1 and ph1 at 1 and
// 3, s2 at 2, ph2 never, abt at 3 and acc at 5. The clause's properties
// are declared as it writes them.
std::string RecursiveSource(const std::string& items) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  int tick = 1;\n"
         "  logic a, hold, done, go, s1, s2, ph1, ph2, abt, acc;\n"
         "  int passes = 0;\n"
         "  int fails = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  always #10 tick = tick + 1;\n"
         "  assign a = !(tick inside {6});\n"
         "  assign hold = !(tick inside {6});\n"
         "  assign done = tick inside {5};\n"
         "  assign go = tick inside {2, 7};\n"
         "  assign s1 = tick inside {1, 3};\n"
         "  assign s2 = tick inside {2};\n"
         "  assign ph1 = tick inside {1, 3};\n"
         "  assign ph2 = 0;\n"
         "  assign abt = tick inside {3};\n"
         "  assign acc = tick inside {5};\n"
         "  property prop_always(p);\n"
         "    p and (1'b1 |=> prop_always(p));\n"
         "  endproperty\n"
         "  property prop_weak_until(p, q);\n"
         "    q or (p and (1'b1 |=> prop_weak_until(p, q)));\n"
         "  endproperty\n"
         "  property p1(s, p);\n"
         "    s |-> prop_always(p);\n"
         "  endproperty\n"
         "  property check_phase1;\n"
         "    s1 |-> (ph1 and (1'b1 |=> check_phase2));\n"
         "  endproperty\n"
         "  property check_phase2;\n"
         "    s2 |-> (ph2 and (1'b1 |=> check_phase1));\n"
         "  endproperty\n"
         "  property p3(p, b, abort);\n"
         "    (p and (1'b1 |=> p4(p, b, abort)));\n"
         "  endproperty\n"
         "  property p4(p, b, abort);\n"
         "    accept_on(b) reject_on(abort) p3(p, b, abort);\n"
         "  endproperty\n" +
         items +
         "  initial #80 $finish;\n"
         "endmodule\n";
}

// The pass and fail counts of the assertion over `spec` at the ticks, and
// then with the attempts in flight at the end of the run decided, in the
// final blocks.
struct Counts {
  uint64_t passes;
  uint64_t fails;
  uint64_t passes_at_end;
  uint64_t fails_at_end;
};

Counts CountsOfRecursive(const std::string& spec) {
  SimFixture f;
  auto* passes =
      RunAndFindVar(RecursiveSource("  p: assert property (@(posedge clk) " +
                                    spec + ") passes++; else fails++;\n"),
                    f, "passes");
  if (passes == nullptr) return {~0ull, ~0ull, ~0ull, ~0ull};
  Variable* fails = f.ctx.FindVariable("fails");
  Counts counts{passes->value.ToUint64(), fails->value.ToUint64(), 0, 0};
  f.ctx.RunFinalBlocks();
  counts.passes_at_end = passes->value.ToUint64();
  counts.fails_at_end = fails->value.ToUint64();
  return counts;
}

// §16.12.17: prop_always(a) requires a at the attempt's tick and, a tick
// later, prop_always(a) again, the instance expanded when it begins: the
// attempts from 1 to 6 fail at 6, where a is low, and those from 7 and 8,
// in flight at the end with a high at every tick they reached, hold.
TEST(RecursiveProperty, ASelfInstanceUnrollsOneTickAtATime) {
  Counts counts = CountsOfRecursive("prop_always(a)");
  EXPECT_EQ(counts.passes, 0u);
  EXPECT_EQ(counts.fails, 6u);
  EXPECT_EQ(counts.passes_at_end, 2u);
  EXPECT_EQ(counts.fails_at_end, 6u);
}

// §16.12.17: prop_weak_until(hold, done) requires hold at every tick up to
// but not including the first where done holds, done never required: the
// attempts from 1 to 5 hold at 5, the one from 6 fails with neither, and
// those from 7 and 8 hold at the end.
TEST(RecursiveProperty, AWeakUntilOfTwoFormalsLiftsTheRequirementAtQ) {
  Counts counts = CountsOfRecursive("prop_weak_until(hold, done)");
  EXPECT_EQ(counts.passes, 5u);
  EXPECT_EQ(counts.fails, 1u);
  EXPECT_EQ(counts.passes_at_end, 7u);
  EXPECT_EQ(counts.fails_at_end, 1u);
}

// §16.12.17: p1(go, a) applies prop_always(a) after go, the recursive
// property instantiated from a property that is not itself recursive: the
// attempt from 2 fails at 6, the one from 7 holds at the end, and the six
// with go low hold at their tick.
TEST(RecursiveProperty, ARecursiveInstanceStandsAsAConsequent) {
  Counts counts = CountsOfRecursive("p1(go, a)");
  EXPECT_EQ(counts.passes, 6u);
  EXPECT_EQ(counts.fails, 1u);
  EXPECT_EQ(counts.passes_at_end, 7u);
  EXPECT_EQ(counts.fails_at_end, 1u);
}

// §16.12.17: check_phase1 and check_phase2 are mutually recursive, each
// instantiating the other a tick later: the attempt from 1 fails at 2,
// where s2 holds and ph2 does not, the one from 3 holds at 4, where s2 is
// low, and the six with s1 low hold at their tick.
TEST(RecursiveProperty, MutuallyRecursivePropertiesAlternate) {
  Counts counts = CountsOfRecursive("check_phase1");
  EXPECT_EQ(counts.passes, 7u);
  EXPECT_EQ(counts.fails, 1u);
  EXPECT_EQ(counts.passes_at_end, 7u);
  EXPECT_EQ(counts.fails_at_end, 1u);
}

// §16.12.17: the abort operators may be used inside a recursive property;
// p4 aborts p3 a tick after its a: the attempts from 1 and 2 are rejected
// at 3, those from 3 and 4 accepted at 5, those from 5 and 6 fail at 6
// with a low, and those from 7 and 8 hold at the end.
TEST(RecursiveProperty, AbortsInsideTheRecursionDecideTheAttempt) {
  Counts counts = CountsOfRecursive("p3(a, acc, abt)");
  EXPECT_EQ(counts.passes, 2u);
  EXPECT_EQ(counts.fails, 4u);
  EXPECT_EQ(counts.passes_at_end, 4u);
  EXPECT_EQ(counts.fails_at_end, 4u);
}

}  // namespace
