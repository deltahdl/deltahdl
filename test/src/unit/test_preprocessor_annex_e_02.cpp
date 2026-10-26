#include <gtest/gtest.h>

#include <optional>
#include <string>

#include "fixture_preprocessor.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

// §E.2 `default_decay_time. The directive specifies the charge decay time for
// trireg nets that do not declare one of their own. Its argument shall be an
// integer constant, a real constant, or the keyword `infinite`, and an argument
// shall always be present. The rule is carried by the preprocessor, which
// parses the directive and records the decay-time state queried below.

namespace {

// The decay time a source holding only `default_decay_time with the argument
// `arg` sets, as the value the argument gives, or nothing where the source
// reported an error or left the charge never decaying. The report stays in `f`
// for a case to read.
std::optional<double> DecayTimeSetBy(PreprocFixture& f,
                                     const std::string& arg) {
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "`default_decay_time " + arg + "\n");
  pp.Preprocess(fid);
  if (f.diag.HasErrors() || pp.DefaultDecayTimeInfinite()) return std::nullopt;
  return pp.DefaultDecayTimeReal();
}

// Whether `f` reported `arg` as no decay time.
::testing::AssertionResult ReportedInvalid(const PreprocFixture& f,
                                           const std::string& arg) {
  return ReportedError(f.diag.Diagnostics(),
                       "invalid `default_decay_time argument: '" + arg + "'", 1,
                       "E.2");
}

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
  // §3.14.1 rounds a delay value rather than truncating it -- with the
  // precision equal to the time unit, delay values round to whole numbers -- so
  // the count the directive yields is 4. Nothing asserted this count before,
  // and truncation gave 3.
  EXPECT_EQ(pp.DefaultDecayTime(), 4u);
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

// E2-C2 (shall): an argument shall be used with the directive; omitting it is
// an error.
TEST(Preprocessor, DefaultDecayTime_MissingArgumentIsError) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "`default_decay_time\n");
  pp.Preprocess(fid);
  // Annex E is informative, and the report names the subclause whose syntax
  // the directive breaks all the same, as a report under Annex D names its
  // subclause, so a reader can follow it to the rule.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`default_decay_time requires an argument", 1,
                            "E.2"));
}

// E2-C1 (syntax): an argument that is neither an integer/real constant nor the
// `infinite` keyword does not satisfy the directive's grammar and is rejected.
TEST(Preprocessor, DefaultDecayTime_InvalidArgumentIsError) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "`default_decay_time fast\n");
  pp.Preprocess(fid);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "invalid `default_decay_time argument: 'fast'", 1,
                            "E.2"));
}

// E2-C1 (syntax): a real_constant holds one decimal point, so an argument with
// two is not one, though every other character in it is a digit.
TEST(Preprocessor, DefaultDecayTime_TwoDecimalPointsIsError) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "`default_decay_time 1.2.3\n");
  pp.Preprocess(fid);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "invalid `default_decay_time argument: '1.2.3'", 1,
                            "E.2"));
}

// E2-C4 (baseline): with no directive present, no charge decay applies, i.e.
// the default state is infinite.
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
  auto fid = f.mgr.AddFile("<test>",
                           "`default_decay_time 10\n`default_decay_time 200\n");
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

// E.2 sets no limit on where the directive is written, and §22.2 leaves any
// such limit to a directive's own description, so one written inside a module
// is read like any other: no report, and the decay time it gives is recorded.
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

// §5.7.1 makes an integer constant of a decimal number broken by underscores
// and of a based number with or without a size, and each sets the decay time
// its value gives.
TEST(Preprocessor, DefaultDecayTime_UnderscoredOrBasedIntegerArgument) {
  PreprocFixture underscored;
  EXPECT_EQ(DecayTimeSetBy(underscored, "1_000"), 1000.0);
  PreprocFixture based;
  EXPECT_EQ(DecayTimeSetBy(based, "'d100"), 100.0);
  PreprocFixture sized;
  EXPECT_EQ(DecayTimeSetBy(sized, "16'h1_F4"), 500.0);
}

// A signed constant whose top bit is set is negative, 4'shf being -1, and
// §28.16.2 gives a charge decay time no negative value, so the argument sets
// no decay time.
TEST(Preprocessor, DefaultDecayTime_NegativeSignedArgumentIsError) {
  PreprocFixture f;
  EXPECT_EQ(DecayTimeSetBy(f, "4'shf"), std::nullopt);
  EXPECT_TRUE(ReportedInvalid(f, "4'shf"));
}

// §5.7.2 writes a real constant in scientific notation as well, its exponent
// marked by e or E and signed or not, and ignores the underscores in it.
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

// §5.7.2 requires a digit on each side of a decimal point, listing .12, 9. and
// 4.E3 among the invalid forms, and an exponent has digits. None of these is a
// real constant, nor is a number followed by other text.
TEST(Preprocessor, DefaultDecayTime_MalformedRealArgumentIsError) {
  for (const char* arg : {"9.", ".5", "4.E3", "2.5e", "2.5x"}) {
    PreprocFixture f;
    EXPECT_EQ(DecayTimeSetBy(f, arg), std::nullopt) << arg;
    EXPECT_TRUE(ReportedInvalid(f, arg)) << arg;
  }
}

}  // namespace
