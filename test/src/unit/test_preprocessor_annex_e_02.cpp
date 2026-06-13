#include <gtest/gtest.h>

#include "fixture_preprocessor.h"

using namespace delta;

// §E.2 `default_decay_time. The directive specifies the charge decay time for
// trireg nets that do not declare one of their own. Its argument shall be an
// integer constant, a real constant, or the keyword `infinite`, and an argument
// shall always be present. The rule is carried by the preprocessor, which parses
// the directive and records the decay-time state queried below.

namespace {

// E2-C1 (syntax, integer_constant; Example 1): an integer argument sets the
// default decay time and clears the infinite (no-decay) state.
TEST(Preprocessor, DefaultDecayTime_IntegerArgument) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "`default_decay_time 100\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DefaultDecayTime(), 100u);
  EXPECT_FALSE(pp.DefaultDecayTimeInfinite());
}

// E2-C1 (syntax, real_constant): a real argument is accepted and recorded as a
// real decay time.
TEST(Preprocessor, DefaultDecayTime_RealArgument) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "`default_decay_time 3.5\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NEAR(pp.DefaultDecayTimeReal(), 3.5, 1e-9);
  EXPECT_FALSE(pp.DefaultDecayTimeInfinite());
}

// E2-C1/E2-C4 (syntax, infinite; Example 2): the keyword `infinite` selects the
// no-charge-decay state.
TEST(Preprocessor, DefaultDecayTime_InfiniteKeyword) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "`default_decay_time infinite\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(pp.DefaultDecayTimeInfinite());
}

// E2-C2 (shall): an argument shall be used with the directive; omitting it is an
// error.
TEST(Preprocessor, DefaultDecayTime_MissingArgumentIsError) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "`default_decay_time\n");
  pp.Preprocess(fid);
  EXPECT_TRUE(f.diag.HasErrors());
}

// E2-C1 (syntax): an argument that is neither an integer/real constant nor the
// `infinite` keyword does not satisfy the directive's grammar and is rejected.
TEST(Preprocessor, DefaultDecayTime_InvalidArgumentIsError) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "`default_decay_time fast\n");
  pp.Preprocess(fid);
  EXPECT_TRUE(f.diag.HasErrors());
}

// E2-C4 (baseline): with no directive present, no charge decay applies, i.e. the
// default state is infinite.
TEST(Preprocessor, DefaultDecayTime_DefaultStateIsInfinite) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "module m; endmodule\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(pp.DefaultDecayTimeInfinite());
}

// E2-C3 (applies to modules that follow): a later directive replaces an earlier
// one for the source text that follows it.
TEST(Preprocessor, DefaultDecayTime_LaterDirectiveReplacesEarlier) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile(
      "<test>", "`default_decay_time 10\n`default_decay_time 200\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DefaultDecayTime(), 200u);
  EXPECT_FALSE(pp.DefaultDecayTimeInfinite());
}

// E2-C1/E2-C4: an integer directive after an `infinite` directive re-enables a
// finite decay time (clears the infinite state).
TEST(Preprocessor, DefaultDecayTime_FiniteAfterInfinite) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile(
      "<test>", "`default_decay_time infinite\n`default_decay_time 42\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(pp.DefaultDecayTimeInfinite());
  EXPECT_EQ(pp.DefaultDecayTime(), 42u);
}

}  // namespace
