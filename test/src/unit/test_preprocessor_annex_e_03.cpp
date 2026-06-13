#include <gtest/gtest.h>

#include "fixture_preprocessor.h"

using namespace delta;

// §E.3 `default_trireg_strength. The directive specifies the charge strength of
// trireg nets. Its syntax takes a single integer_constant argument, and that
// constant shall be between 0 and 250. Both rules are carried by the
// preprocessor, which parses the directive, validates the argument, and records
// the strength state queried below.

namespace {

// E3-C1 (syntax, integer_constant): an integer argument sets the default trireg
// strength and records that a directive is in effect.
TEST(Preprocessor, DefaultTriregStrength_IntegerArgument) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "`default_trireg_strength 100\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(pp.HasDefaultTriregStrength());
  EXPECT_EQ(pp.DefaultTriregStrength(), 100u);
}

// E3-C1 (syntax): the directive requires an argument; omitting it is an error.
TEST(Preprocessor, DefaultTriregStrength_MissingArgumentIsError) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "`default_trireg_strength\n");
  pp.Preprocess(fid);
  EXPECT_TRUE(f.diag.HasErrors());
}

// E3-C1 (syntax, integer_constant): a non-integer argument does not satisfy the
// directive's grammar and is rejected.
TEST(Preprocessor, DefaultTriregStrength_NonIntegerArgumentIsError) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "`default_trireg_strength strong\n");
  pp.Preprocess(fid);
  EXPECT_TRUE(f.diag.HasErrors());
}

// E3-C2 (shall, lower bound): 0 is within the legal 0..250 range and is
// accepted.
TEST(Preprocessor, DefaultTriregStrength_LowerBoundZeroAccepted) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "`default_trireg_strength 0\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(pp.HasDefaultTriregStrength());
  EXPECT_EQ(pp.DefaultTriregStrength(), 0u);
}

// E3-C2 (shall, upper bound): 250 is the largest legal value and is accepted.
TEST(Preprocessor, DefaultTriregStrength_UpperBound250Accepted) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "`default_trireg_strength 250\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(pp.HasDefaultTriregStrength());
  EXPECT_EQ(pp.DefaultTriregStrength(), 250u);
}

// E3-C2 (shall): a value above 250 is outside the legal range and is rejected.
TEST(Preprocessor, DefaultTriregStrength_AboveRangeIsError) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "`default_trireg_strength 251\n");
  pp.Preprocess(fid);
  EXPECT_TRUE(f.diag.HasErrors());
}

// E3 (baseline): with no directive present, no default trireg strength is in
// effect.
TEST(Preprocessor, DefaultTriregStrength_DefaultStateNoDirective) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "module m; endmodule\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(pp.HasDefaultTriregStrength());
}

// E3-C1 (applies to the source that follows): a later directive replaces an
// earlier one for the text that follows it.
TEST(Preprocessor, DefaultTriregStrength_LaterDirectiveReplacesEarlier) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile(
      "<test>", "`default_trireg_strength 50\n`default_trireg_strength 200\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(pp.HasDefaultTriregStrength());
  EXPECT_EQ(pp.DefaultTriregStrength(), 200u);
}

}  // namespace
