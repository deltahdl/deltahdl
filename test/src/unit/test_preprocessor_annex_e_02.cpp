#include <gtest/gtest.h>

#include <optional>
#include <string>

#include "fixture_preprocessor.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

namespace {

std::optional<double> DecayTimeSetBy(PreprocFixture& f,
                                     const std::string& arg) {
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "`default_decay_time " + arg + "\n");
  pp.Preprocess(fid);
  if (f.diag.HasErrors() || pp.DefaultDecayTimeInfinite()) return std::nullopt;
  return pp.DefaultDecayTimeReal();
}

::testing::AssertionResult ReportedInvalid(const PreprocFixture& f,
                                           const std::string& arg) {
  return ReportedError(f.diag.Diagnostics(),
                       "invalid `default_decay_time argument: '" + arg + "'", 1,
                       "E.2");
}

TEST(Preprocessor, DefaultDecayTime_IntegerArgument) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "`default_decay_time 100\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DefaultDecayTime(), 100u);
  EXPECT_FALSE(pp.DefaultDecayTimeInfinite());
}

TEST(Preprocessor, DefaultDecayTime_RealArgument) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "`default_decay_time 3.5\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NEAR(pp.DefaultDecayTimeReal(), 3.5, 1e-9);
  EXPECT_FALSE(pp.DefaultDecayTimeInfinite());
  EXPECT_EQ(pp.DefaultDecayTime(), 4u);
}

TEST(Preprocessor, DefaultDecayTime_InfiniteKeyword) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "`default_decay_time infinite\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(pp.DefaultDecayTimeInfinite());
}

TEST(Preprocessor, DefaultDecayTime_MissingArgumentIsError) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "`default_decay_time\n");
  pp.Preprocess(fid);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`default_decay_time requires an argument", 1,
                            "E.2"));
}

TEST(Preprocessor, DefaultDecayTime_InvalidArgumentIsError) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "`default_decay_time fast\n");
  pp.Preprocess(fid);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "invalid `default_decay_time argument: 'fast'", 1,
                            "E.2"));
}

TEST(Preprocessor, DefaultDecayTime_TwoDecimalPointsIsError) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "`default_decay_time 1.2.3\n");
  pp.Preprocess(fid);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "invalid `default_decay_time argument: '1.2.3'", 1,
                            "E.2"));
}

TEST(Preprocessor, DefaultDecayTime_DefaultStateIsInfinite) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "module m; endmodule\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(pp.DefaultDecayTimeInfinite());
}

TEST(Preprocessor, DefaultDecayTime_LaterDirectiveReplacesEarlier) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>",
                           "`default_decay_time 10\n`default_decay_time 200\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DefaultDecayTime(), 200u);
  EXPECT_FALSE(pp.DefaultDecayTimeInfinite());
}

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

TEST(Preprocessor, DefaultDecayTime_InsideAModuleIsAccepted) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>",
                           "module m;\n"
                           "`default_decay_time 5\n"
                           "  trireg t;\n"
                           "endmodule\n");
  pp.Preprocess(fid);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_FALSE(pp.DefaultDecayTimeInfinite());
  EXPECT_EQ(pp.DefaultDecayTime(), 5u);
}

TEST(Preprocessor, DefaultDecayTime_UnderscoredOrBasedIntegerArgument) {
  PreprocFixture underscored;
  EXPECT_EQ(DecayTimeSetBy(underscored, "1_000"), 1000.0);
  PreprocFixture based;
  EXPECT_EQ(DecayTimeSetBy(based, "'d100"), 100.0);
  PreprocFixture sized;
  EXPECT_EQ(DecayTimeSetBy(sized, "16'h1_F4"), 500.0);
}

TEST(Preprocessor, DefaultDecayTime_NegativeSignedArgumentIsError) {
  PreprocFixture f;
  EXPECT_EQ(DecayTimeSetBy(f, "4'shf"), std::nullopt);
  EXPECT_TRUE(ReportedInvalid(f, "4'shf"));
}

TEST(Preprocessor, DefaultDecayTime_ScientificOrUnderscoredRealArgument) {
  PreprocFixture lower;
  EXPECT_EQ(DecayTimeSetBy(lower, "2.5e1"), 25.0);
  PreprocFixture upper;
  EXPECT_EQ(DecayTimeSetBy(upper, "25E0"), 25.0);
  PreprocFixture negative_exponent;
  EXPECT_EQ(DecayTimeSetBy(negative_exponent, "2.5e-1"), 0.25);
  PreprocFixture underscored;
  EXPECT_EQ(DecayTimeSetBy(underscored, "1_2.5"), 12.5);
}

TEST(Preprocessor, DefaultDecayTime_MalformedRealArgumentIsError) {
  for (const char* arg : {"9.", ".5", "4.E3", "2.5e", "2.5x"}) {
    PreprocFixture f;
    EXPECT_EQ(DecayTimeSetBy(f, arg), std::nullopt) << arg;
    EXPECT_TRUE(ReportedInvalid(f, arg)) << arg;
  }
}

}  // namespace
