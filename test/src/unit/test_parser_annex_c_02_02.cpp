#include "fixture_parser.h"

using namespace delta;

namespace {

// Annex C.2.2: $sampled with a clocking event argument.
//
// IEEE 1800-2005 required a clocking event argument for the $sampled
// assertion system function. In IEEE 1800-2023 the semantics of $sampled no
// longer depend on a clocking event, so the syntax that once supplied a
// clocking event argument to $sampled has been removed. The parser must
// reject a clocking event argument to $sampled while still accepting the
// plain single-argument form.

// $sampled without a clocking event argument is the form retained in the
// current standard and must parse cleanly.
TEST(SampledClockingEventArgDeprecated, PlainSampledIsAccepted) {
  auto r = Parse("module m; logic a, b; assign b = $sampled(a); endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

// Supplying a clocking event argument to $sampled is the removed syntax and
// is now rejected by the parser.
TEST(SampledClockingEventArgDeprecated, ClockingEventArgIsRejected) {
  auto r = Parse(
      "module m; logic a, b, clk; "
      "assign b = $sampled(a, @(posedge clk)); endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// The clocking event may also be written without parentheses as a bare
// signal reference; that form of the argument to $sampled is rejected too.
TEST(SampledClockingEventArgDeprecated, BareClockingEventArgIsRejected) {
  auto r = Parse(
      "module m; logic a, b, clk; "
      "assign b = $sampled(a, @clk); endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// The deprecation is specific to $sampled; other sampled value functions
// still accept a clocking event argument (16.9.3), so $rose with a clocking
// event must continue to parse.
TEST(SampledClockingEventArgDeprecated, ClockingEventArgStillAllowedForRose) {
  auto r = Parse(
      "module m; logic a, b, clk; "
      "assign b = $rose(a, @(posedge clk)); endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

// The rejection is gated solely on the callee being $sampled, independent of
// how the clocking event is written. A bare (unparenthesized) clocking event
// argument supplied to a non-$sampled sampled value function such as $fell
// must still parse, confirming the gate does not fire on the event syntax
// itself.
TEST(SampledClockingEventArgDeprecated,
     BareClockingEventArgStillAllowedForFell) {
  auto r = Parse(
      "module m; logic a, b, clk; "
      "assign b = $fell(a, @clk); endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
