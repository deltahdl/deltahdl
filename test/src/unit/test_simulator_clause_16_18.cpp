#include <gtest/gtest.h>

#include "common/types.h"
#include "simulator/sva_engine.h"

using namespace delta;

namespace {

// §16.18: a variable used in a concurrent assertion that is a clocking block
// variable is sampled only in the clocking block. The assertion reads the value
// the block captured at its clocking event, not a fresh sample of the
// underlying signal.
TEST(ClockingConcurrentAssertion, ClockingVariableUsesBlockSample) {
  SampledValue live = SampleStaticVariable(0xAAAA, SimTime{10}, 0);
  SampledValue used = ConcurrentAssertionVariableSample(
      /*is_clocking_block_variable=*/true,
      /*clocking_block_sampled_value=*/0x55, live);
  // The clocking-block sample wins over the underlying signal's live sample.
  EXPECT_EQ(used.value, 0x55u);
  EXPECT_NE(used.value, live.value);
  // The value the block captured is a preponed sample taken at its event.
  EXPECT_EQ(used.mode, SampleMode::kPreponed);
}

// §16.18: a reference to a plain variable that is not a clocking block variable
// keeps the ordinary §16.5 concurrent-assertion sample.
TEST(ClockingConcurrentAssertion, PlainVariableKeepsOrdinarySample) {
  SampledValue ordinary = SampleStaticVariable(0x1234, SimTime{7}, 0);
  SampledValue used = ConcurrentAssertionVariableSample(
      /*is_clocking_block_variable=*/false,
      /*clocking_block_sampled_value=*/0x9999, ordinary);
  EXPECT_EQ(used.value, ordinary.value);
  EXPECT_EQ(used.mode, ordinary.mode);
}

// §16.18: because the single clocking-block sample is what every reference to
// the clocking variable reads, naming it different ways — directly, through the
// clocking block, or through a property declared inside the block — all observe
// the same value (the a1/a2/a3/a4 equivalence of the LRM example).
TEST(ClockingConcurrentAssertion, AllNamingsObserveTheSameBlockSample) {
  const uint64_t block_sample = 0x42;
  // Each naming arrives with its own distinct ordinary sample, but all are
  // clocking block variables, so the block sample overrides every one of them.
  SampledValue direct = ConcurrentAssertionVariableSample(
      true, block_sample, SampleStaticVariable(0x11, SimTime{2}, 0));
  SampledValue via_block = ConcurrentAssertionVariableSample(
      true, block_sample, SampleStaticVariable(0x22, SimTime{2}, 0));
  SampledValue via_inner_prop = ConcurrentAssertionVariableSample(
      true, block_sample, SampleStaticVariable(0x33, SimTime{2}, 0));

  EXPECT_EQ(direct.value, block_sample);
  EXPECT_EQ(via_block.value, direct.value);
  EXPECT_EQ(via_inner_prop.value, direct.value);
}

// §16.18 edge case: the clocking block's captured value is used unconditionally
// for a clocking block variable, even when that value is zero — which is also
// the no-entry default of the clocking sample store. A zero block sample must
// still override a nonzero ordinary sample rather than falling through to it.
TEST(ClockingConcurrentAssertion, ZeroValuedBlockSampleStillOverridesOrdinary) {
  SampledValue ordinary = SampleStaticVariable(0xFFFF, SimTime{4}, 0);
  SampledValue used = ConcurrentAssertionVariableSample(
      /*is_clocking_block_variable=*/true,
      /*clocking_block_sampled_value=*/0x0, ordinary);
  EXPECT_EQ(used.value, 0x0u);
  EXPECT_NE(used.value, ordinary.value);
  EXPECT_EQ(used.mode, SampleMode::kPreponed);
}

}  // namespace
