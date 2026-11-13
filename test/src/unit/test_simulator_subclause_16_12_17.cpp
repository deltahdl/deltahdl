#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "helpers_property_places.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

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

TEST(RecursiveProperty, ASelfInstanceUnrollsOneTickAtATime) {
  Counts counts = CountsOfRecursive("prop_always(a)");
  EXPECT_EQ(counts.passes, 0u);
  EXPECT_EQ(counts.fails, 6u);
  EXPECT_EQ(counts.passes_at_end, 2u);
  EXPECT_EQ(counts.fails_at_end, 6u);
}

TEST(RecursiveProperty, AWeakUntilOfTwoFormalsLiftsTheRequirementAtQ) {
  Counts counts = CountsOfRecursive("prop_weak_until(hold, done)");
  EXPECT_EQ(counts.passes, 5u);
  EXPECT_EQ(counts.fails, 1u);
  EXPECT_EQ(counts.passes_at_end, 7u);
  EXPECT_EQ(counts.fails_at_end, 1u);
}

TEST(RecursiveProperty, ARecursiveInstanceStandsAsAConsequent) {
  Counts counts = CountsOfRecursive("p1(go, a)");
  EXPECT_EQ(counts.passes, 6u);
  EXPECT_EQ(counts.fails, 1u);
  EXPECT_EQ(counts.passes_at_end, 7u);
  EXPECT_EQ(counts.fails_at_end, 1u);
}

TEST(RecursiveProperty, MutuallyRecursivePropertiesAlternate) {
  Counts counts = CountsOfRecursive("check_phase1");
  EXPECT_EQ(counts.passes, 7u);
  EXPECT_EQ(counts.fails, 1u);
  EXPECT_EQ(counts.passes_at_end, 7u);
  EXPECT_EQ(counts.fails_at_end, 1u);
}

TEST(RecursiveProperty, AbortsInsideTheRecursionDecideTheAttempt) {
  Counts counts = CountsOfRecursive("p3(a, acc, abt)");
  EXPECT_EQ(counts.passes, 2u);
  EXPECT_EQ(counts.fails, 4u);
  EXPECT_EQ(counts.passes_at_end, 4u);
  EXPECT_EQ(counts.fails_at_end, 4u);
}

constexpr const char* kPlacedStimulus =
    "  assign a = tick inside {1, 3};\n"
    "  assign b = tick inside {2, 3};\n"
    "  assign c = tick inside {2, 4};\n"
    "  assign d = tick inside {1, 2, 3};\n";

constexpr const char* kPlacedRecursions =
    "  property pa(p); p and (1'b1 |=> pa(p)); endproperty\n"
    "  property pwu(p, q); q or (p and (1'b1 |=> pwu(p, q))); endproperty\n"
    "  property cnt(x, local input int n);\n"
    "    (n == 0) or (x and (1'b1 |=> cnt(x, n - 1)));\n"
    "  endproperty\n"
    "  property ph1(x, y); x and (1'b1 |=> ph2(x, y)); endproperty\n"
    "  property ph2(x, y); y and (1'b1 |=> ph1(x, y)); endproperty\n"
    "  property ab(p, acc); accept_on(acc) p and (1'b1 |=> ab(p, acc));\n"
    "  endproperty\n";

const PlacedProperty kRecursionsInPlace[] = {
    {"c |-> pa(d)", {2, 2}, 2}, {"pwu(d, c)", {4, 0}, 4},
    {"pwu(a, b)", {3, 1}, 3},   {"cnt(d, 2)", {2, 2}, 2},
    {"ph1(d, c)", {2, 2}, 2},   {"ab(d, c)", {4, 0}, 4}};

TEST(RecursiveProperty, ARecursionCountsInEachPlace) {
  for (const char* place : kPropertyPlaces) {
    for (const PlacedProperty& property : kRecursionsInPlace) {
      ExpectPropertyCountsInPlace(place, property, kPlacedStimulus,
                                  kPlacedRecursions);
    }
  }
}

TEST(RecursiveProperty, DISABLED_ARecursionCountsInACompilationUnitProperty) {
  for (const PlacedProperty& property : kRecursionsInPlace) {
    ExpectPropertyCountsInPlace("unit", property, kPlacedStimulus,
                                kPlacedRecursions);
  }
}

}  // namespace
