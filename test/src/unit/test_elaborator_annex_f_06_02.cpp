#include <gtest/gtest.h>

#include <cstddef>
#include <optional>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "elaborator/annex_f_grammar.h"
#include "elaborator/annex_f_past.h"
#include "elaborator/annex_f_tight_satisfaction.h"

using namespace delta;

namespace {

// A single alphabet letter carrying the given atomic propositions.
Letter A(std::set<std::string> atoms) { return LetterAtoms(std::move(atoms)); }

// The unconditional Boolean 1, used for the gating expression e2 and the clock
// c in the default $past(e) form -- §F.6.2's NOTE: $past(e) is equivalent to
// $past(e, 1, 1'b1, 1'b1), so every letter is an active tick.
auto One() { return BoolTrue(); }

using Indices = std::vector<std::size_t>;

// §F.6.2 (NOTE): $past(e) is equivalent to $past(e, 1, 1'b1, 1'b1). With c and
// e2 both the constant 1, every letter is active, so the single tick back from
// w^j is the immediately preceding letter w^{j-1}.
TEST(Past, DefaultFormSamplesThePrecedingLetter) {
  const Word kWord{A({}), A({}), A({})};
  EXPECT_EQ(PastSourceIndices(kWord, /*j=*/2, /*n=*/1, One(), One()),
            Indices{1});
  EXPECT_EQ(PastSourceIndices(kWord, /*j=*/1, /*n=*/1, One(), One()),
            Indices{0});
}

// §F.6.2 ($past): with all ticks active, $past(e, n) reaches back exactly n
// ticks, so the source of w^j is w^{j-n}.
TEST(Past, NTicksBackWithEveryTickActive) {
  const Word kWord{A({}), A({}), A({}), A({})};
  EXPECT_EQ(PastSourceIndices(kWord, /*j=*/3, /*n=*/2, One(), One()),
            Indices{1});
  EXPECT_EQ(PastSourceIndices(kWord, /*j=*/3, /*n=*/3, One(), One()),
            Indices{0});
}

// §F.6.2 ($past): the gating expression e2 selects which letters count as
// active ticks. Only letters where e2 holds are counted, so one tick back from
// j skips the inactive letters between.
TEST(Past, GatingExpressionCountsOnlyActiveTicks) {
  auto en = BoolAtom("en");
  // Active (en) at 0 and 2; letter 1 and 3 are inactive.
  const Word kWord{A({"en"}), A({}), A({"en"}), A({})};
  // One active tick back from j=3 is the active letter at i=2.
  EXPECT_EQ(PastSourceIndices(kWord, /*j=*/3, /*n=*/1, en, One()), Indices{2});
  // Two active ticks back from j=3 is the active letter at i=0.
  EXPECT_EQ(PastSourceIndices(kWord, /*j=*/3, /*n=*/2, en, One()), Indices{0});
}

// §F.6.2 ($past): the destination clock c gates ticks just as e2 does -- the
// active condition is c && e2. A letter where the clock is absent is not a
// tick.
TEST(Past, ClockGatesTicks) {
  auto clk = BoolAtom("clk");
  // clk ticks at 1 and 3; letters 0 and 2 carry no clock edge.
  const Word kWord{A({}), A({"clk"}), A({}), A({"clk"})};
  // j must be in range and a tick must lie strictly before it: one tick back
  // from j=3 is i=1.
  EXPECT_EQ(PastSourceIndices(kWord, /*j=*/3, /*n=*/1, One(), clk), Indices{1});
}

// §F.6.2 ($past): the active condition is the conjunction c && e2, so a letter
// must satisfy both the clock and the gating expression to count as a tick. A
// letter carrying only the clock (no e2) is skipped, so one tick back reaches
// past it to the most recent letter holding both.
TEST(Past, ClockAndGateBothRequiredForATick) {
  auto clk = BoolAtom("clk");
  auto en = BoolAtom("en");
  // Active (clk && en) at 0 and 2; letter 1 has the clock but not en.
  const Word kWord{A({"clk", "en"}), A({"clk"}), A({"clk", "en"})};
  // One tick back from j=2 skips the clk-only letter 1 and lands on i=0.
  EXPECT_EQ(PastSourceIndices(kWord, /*j=*/2, /*n=*/1, en, clk), Indices{0});
}

// §F.6.2 ($past) "Otherwise": when fewer than n active ticks precede j, no
// source index qualifies and the call takes e1's initial value instead.
TEST(Past, FallsBackToInitialValueWhenTooFewTicks) {
  auto en = BoolAtom("en");
  // Only one active tick (at i=0) lies before j=2.
  const Word kWord{A({"en"}), A({}), A({})};
  EXPECT_TRUE(PastSourceIndices(kWord, /*j=*/2, /*n=*/2, en, One()).empty());
  EXPECT_TRUE(PastSamplesInitialValue(kWord, /*j=*/2, /*n=*/2, en, One()));
  // The reachable single-tick case does sample, so it is not the initial value.
  EXPECT_FALSE(PastSamplesInitialValue(kWord, /*j=*/2, /*n=*/1, en, One()));
}

// §F.6.2 ($past) lower boundary: a source index must satisfy 0 <= i < j, so at
// the first letter (j=0) no earlier tick can exist and $past takes e1's initial
// value whatever the word holds.
TEST(Past, TakesInitialValueAtTheFirstLetter) {
  const Word kWord{A({"en"}), A({"en"})};
  auto en = BoolAtom("en");
  EXPECT_TRUE(PastSourceIndices(kWord, /*j=*/0, /*n=*/1, en, One()).empty());
  EXPECT_TRUE(PastSamplesInitialValue(kWord, /*j=*/0, /*n=*/1, en, One()));
}

// §F.6.2 ($past) boundary: the point j must satisfy 0 <= j < |w|. A point at or
// past the end of the word yields no source index and is not the initial-value
// branch (it is outside the rule's domain).
TEST(Past, RejectsOutOfRangePoint) {
  const Word kWord{A({}), A({})};
  EXPECT_TRUE(PastSourceIndices(kWord, /*j=*/2, /*n=*/1, One(), One()).empty());
  EXPECT_FALSE(PastSamplesInitialValue(kWord, /*j=*/2, /*n=*/1, One(), One()));
}

// §F.6.2 ($past): n shall be at least 1; a zero tick count is outside the rule,
// so no index qualifies and it is not the initial-value branch.
TEST(Past, RejectsZeroTickCount) {
  const Word kWord{A({}), A({})};
  EXPECT_TRUE(PastSourceIndices(kWord, /*j=*/1, /*n=*/0, One(), One()).empty());
  EXPECT_FALSE(PastSamplesInitialValue(kWord, /*j=*/1, /*n=*/0, One(), One()));
}

// §F.6.2 ($past_gclk): $past_gclk(e)[w^j] = e[w^{j-1}] for j > 0, so the source
// is the immediately preceding letter.
TEST(PastGclk, SamplesThePrecedingLetter) {
  const Word kWord{A({}), A({}), A({})};
  EXPECT_EQ(PastGclkSourceIndex(kWord, /*j=*/2), std::optional<std::size_t>{1});
  EXPECT_EQ(PastGclkSourceIndex(kWord, /*j=*/1), std::optional<std::size_t>{0});
}

// §F.6.2 ($past_gclk): at w^0 there is no preceding letter, so the value comes
// from e's initial values -- no source index.
TEST(PastGclk, TakesInitialValueAtTheFirstLetter) {
  const Word kWord{A({}), A({})};
  EXPECT_EQ(PastGclkSourceIndex(kWord, /*j=*/0), std::nullopt);
}

// §F.6.2 ($past_gclk) boundary: a point at or past the end of the word is out
// of range and yields no source index.
TEST(PastGclk, RejectsOutOfRangePoint) {
  const Word kWord{A({}), A({})};
  EXPECT_EQ(PastGclkSourceIndex(kWord, /*j=*/2), std::nullopt);
}

}  // namespace
