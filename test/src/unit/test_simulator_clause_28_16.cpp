#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <initializer_list>
#include <type_traits>

#include "fixture_simulator.h"
#include "helpers_mintymax.h"
#include "model_gate_logic.h"
#include "model_strength.h"

using namespace delta;

struct DelaySpec {
  uint64_t d1 = 0;
  uint64_t d2 = 0;
  uint64_t d3 = 0;
  uint8_t count = 0;
};
uint64_t ComputePropagationDelay(const DelaySpec& spec, Val4 from, Val4 to) {
  if (spec.count == 0) return 0;
  if (spec.count == 1) return spec.d1;
  if (from == to) return 0;
  if (spec.count == 2) {
    switch (to) {
      case Val4::kV1:
        return spec.d1;
      case Val4::kV0:
        return spec.d2;
      case Val4::kZ:
      case Val4::kX:
        return std::min(spec.d1, spec.d2);
    }
  }

  switch (to) {
    case Val4::kV1:
      return spec.d1;
    case Val4::kV0:
      return spec.d2;
    case Val4::kZ:
      return spec.d3;
    case Val4::kX:
      return std::min({spec.d1, spec.d2, spec.d3});
  }
  return 0;
}

namespace {

TEST(GateNetDelays, DefaultDelayIsZero) {
  DelaySpec spec;
  spec.count = 0;
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV0, Val4::kV1), 0u);
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV1, Val4::kV0), 0u);
}

TEST(GateNetDelays, SingleDelayUsedForAll) {
  DelaySpec spec{10, 0, 0, 1};
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV0, Val4::kV1), 10u);
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV1, Val4::kV0), 10u);
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV0, Val4::kX), 10u);
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV1, Val4::kZ), 10u);
}

TEST(GateNetDelays, TwoDelayRiseAndFall) {
  DelaySpec spec{10, 20, 0, 2};

  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV0, Val4::kV1), 10u);

  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV1, Val4::kV0), 20u);
}

TEST(GateNetDelays, TwoDelayToZAndXIsMinimum) {
  DelaySpec spec{10, 20, 0, 2};

  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV0, Val4::kZ), 10u);
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV1, Val4::kZ), 10u);
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kX, Val4::kZ), 10u);

  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV0, Val4::kX), 10u);
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV1, Val4::kX), 10u);
}

TEST(GateNetDelays, ThreeDelay0To1IsD1) {
  DelaySpec spec{10, 20, 15, 3};
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV0, Val4::kV1), 10u);
}

TEST(GateNetDelays, ThreeDelay1To0IsD2) {
  DelaySpec spec{10, 20, 15, 3};
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV1, Val4::kV0), 20u);
}

TEST(GateNetDelays, ThreeDelayToZIsD3) {
  DelaySpec spec{10, 20, 15, 3};
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV0, Val4::kZ), 15u);
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV1, Val4::kZ), 15u);
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kX, Val4::kZ), 15u);
}

TEST(GateNetDelays, ThreeDelayToXIsMinOfAll) {
  DelaySpec spec{10, 20, 15, 3};

  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV0, Val4::kX), 10u);
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV1, Val4::kX), 10u);
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kZ, Val4::kX), 10u);
}

TEST(GateNetDelays, ThreeDelayXTo0IsD2) {
  DelaySpec spec{10, 20, 15, 3};
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kX, Val4::kV0), 20u);
}

TEST(GateNetDelays, ThreeDelayXTo1IsD1) {
  DelaySpec spec{10, 20, 15, 3};
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kX, Val4::kV1), 10u);
}

TEST(GateNetDelays, ThreeDelayZTo0IsD2) {
  DelaySpec spec{10, 20, 15, 3};
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kZ, Val4::kV0), 20u);
}

TEST(GateNetDelays, ThreeDelayZTo1IsD1) {
  DelaySpec spec{10, 20, 15, 3};
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kZ, Val4::kV1), 10u);
}

TEST(GateNetDelays, TwoDelaySameStateIsZero) {
  DelaySpec spec{10, 20, 0, 2};
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV0, Val4::kV0), 0u);
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV1, Val4::kV1), 0u);
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kX, Val4::kX), 0u);
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kZ, Val4::kZ), 0u);
}

TEST(GateNetDelays, ThreeDelaySameStateIsZero) {
  DelaySpec spec{10, 20, 15, 3};
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV0, Val4::kV0), 0u);
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV1, Val4::kV1), 0u);
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kX, Val4::kX), 0u);
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kZ, Val4::kZ), 0u);
}

TEST(GateNetDelays, SingleDelayAppliesToSameState) {
  DelaySpec spec{10, 0, 0, 1};
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV0, Val4::kV0), 10u);
  EXPECT_EQ(ComputePropagationDelay(spec, Val4::kV1, Val4::kV1), 10u);
}

TEST(GateNetDelays, TwoDelayRiseFallAndXViaGateModel) {
  EXPECT_EQ(ComputeGateDelay(10, 12, Val4::kV0, Val4::kV1), 10u);
  EXPECT_EQ(ComputeGateDelay(10, 12, Val4::kV1, Val4::kV0), 12u);
  EXPECT_EQ(ComputeGateDelay(10, 12, Val4::kV0, Val4::kX), 10u);
  EXPECT_EQ(ComputeGateDelay(10, 12, Val4::kV1, Val4::kX), 10u);
}

TEST(GateNetDelays, NoDelayZeroPropagationViaGateModel) {
  EXPECT_EQ(ComputeGateDelay(0, 0, Val4::kV0, Val4::kV1), 0u);
}

TEST(GateNetDelays, StrengthDoesNotAffectPropagationDelay) {
  // The production delay helper has no parameter that carries input strength;
  // its result depends solely on the rise/fall slots and the from/to endpoints.
  static_assert(std::is_invocable_r_v<uint64_t, decltype(&ComputeGateDelay),
                                      uint64_t, uint64_t, Val4, Val4>,
                "ComputeGateDelay must take only delay slots and endpoints");

  static constexpr StrengthLevel kAllStrengths[] = {
      StrengthLevel::kSmall,  StrengthLevel::kMedium, StrengthLevel::kWeak,
      StrengthLevel::kLarge,  StrengthLevel::kPull,   StrengthLevel::kStrong,
      StrengthLevel::kSupply,
  };
  static constexpr Val4 kVals[] = {Val4::kV0, Val4::kV1, Val4::kX, Val4::kZ};
  for (Val4 from : kVals) {
    for (Val4 to : kVals) {
      uint64_t reference = ComputeGateDelay(7, 11, from, to);
      for (StrengthLevel s : kAllStrengths) {
        (void)s;
        EXPECT_EQ(ComputeGateDelay(7, 11, from, to), reference);
      }
    }
  }
}

TEST(GateNetDelays, ProductionNoDelaySchedulerStopsAtZero) {
  // Running the lowered simulator on a gate without a delay specification
  // leaves the scheduler at time zero: the production coroutine takes the
  // no-delay branch and never schedules a propagation event.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a;\n"
      "  wire y;\n"
      "  and g(y, a, a);\n"
      "  initial a = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 0u);
}

TEST(GateNetDelays, ProductionRiseTransitionAdvancesByFirstSlot) {
  // A 0->1 transition routes through the rise slot of the production
  // SelectContAssignDelay path; the scheduler's last event lands at the
  // input-change time plus the first delay slot.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a;\n"
      "  wire y;\n"
      "  and #(7, 11) g(y, a, a);\n"
      "  initial begin a = 1'b0; #2 a = 1'b1; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 9u);
}

TEST(GateNetDelays, ProductionFallTransitionAdvancesBySecondSlot) {
  // A 1->0 transition (after the gate has stabilised at 1) routes through the
  // fall slot. The scheduler's last event lands at the input-change time plus
  // the second delay slot.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a;\n"
      "  wire y;\n"
      "  and #(7, 11) g(y, a, a);\n"
      "  initial begin a = 1'b1; #20 a = 1'b0; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 31u);
}

TEST(GateNetDelays, ProductionDelayedGateSettlesToInputConjunction) {
  // With a non-zero delay spec, the production simulator's coroutine still
  // converges the output to the AND of its inputs after the delay elapses.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a, b;\n"
      "  wire y;\n"
      "  and #(3, 5) g(y, a, b);\n"
      "  initial begin a = 1'b1; b = 1'b1; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* net = f.ctx.FindNet("y");
  ASSERT_NE(net, nullptr);
  ASSERT_NE(net->resolved, nullptr);
  ASSERT_GT(net->resolved->value.nwords, 0u);
  const auto& w = net->resolved->value.words[0];
  EXPECT_EQ(w.aval & 1u, 1u);
  EXPECT_EQ(w.bval & 1u, 0u);
}

TEST(GateNetDelays, ProductionTransitionFromXToZeroUsesFallSlot) {
  // After the gate stabilises at x, driving the input to 0 should route the
  // transition through the fall slot rather than the lesser of rise/fall.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a;\n"
      "  wire y;\n"
      "  and #(7, 11) g(y, a, a);\n"
      "  initial begin a = 1'bx; #100 a = 1'b0; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  // First iter applies min(7,11)=7 to settle y at x by t=7. At t=100 the x->0
  // transition then schedules through the fall slot: 100 + 11 = 111.
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 111u);
}

TEST(GateNetDelays, ProductionTransitionFromXToOneUsesRiseSlot) {
  // Symmetric to the previous test: a stabilised-x output transitioning to 1
  // should route through the rise slot.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a;\n"
      "  wire y;\n"
      "  and #(7, 11) g(y, a, a);\n"
      "  initial begin a = 1'bx; #100 a = 1'b1; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  // x->1 routes through the rise slot: 100 + 7 = 107.
  EXPECT_EQ(f.scheduler.CurrentTime().ticks, 107u);
}

}  // namespace
