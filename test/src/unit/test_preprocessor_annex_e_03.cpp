#include <gtest/gtest.h>

#include <cstdint>
#include <optional>
#include <string>

#include "fixture_preprocessor.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

// §E.3 `default_trireg_strength. The directive specifies the charge strength of
// trireg nets. Its syntax takes a single integer_constant argument, and that
// constant shall be between 0 and 250. Both rules are carried by the
// preprocessor, which parses the directive, validates the argument, and records
// the strength state queried below.

namespace {

// The strength a source holding only `default_trireg_strength with the argument
// `arg` sets, or nothing where the source reported an error or set none. The
// report stays in `f` for a case to read.
std::optional<uint32_t> StrengthSetBy(PreprocFixture& f,
                                      const std::string& arg) {
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "`default_trireg_strength " + arg + "\n");
  pp.Preprocess(fid);
  if (f.diag.HasErrors() || !pp.HasDefaultTriregStrength()) {
    return std::nullopt;
  }
  return pp.DefaultTriregStrength();
}

// Whether `f` reported `arg` as no integer constant at all.
::testing::AssertionResult ReportedInvalid(const PreprocFixture& f,
                                           const std::string& arg) {
  return ReportedError(
      f.diag.Diagnostics(),
      "invalid `default_trireg_strength argument: '" + arg + "'", 1, "E.3");
}

// Whether `f` reported a value outside E.3's range.
::testing::AssertionResult ReportedOutOfRange(const PreprocFixture& f) {
  return ReportedError(
      f.diag.Diagnostics(),
      "`default_trireg_strength value must be between 0 and 250", 1, "E.3");
}

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
  // Annex E is informative, and the report names the subclause whose syntax
  // the directive breaks all the same, as a report under Annex D names its
  // subclause, so a reader can follow it to the rule.
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`default_trireg_strength requires an argument", 1,
                            "E.3"));
}

// E3-C1 (syntax, integer_constant): a non-integer argument does not satisfy the
// directive's grammar and is rejected.
TEST(Preprocessor, DefaultTriregStrength_NonIntegerArgumentIsError) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "`default_trireg_strength strong\n");
  pp.Preprocess(fid);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "invalid `default_trireg_strength argument: 'strong'", 1, "E.3"));
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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "`default_trireg_strength value must be between 0 and 250", 1, "E.3"));
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

// E.3 sets no limit on where the directive is written, and §22.2 leaves any
// such limit to a directive's own description, so one written inside a module
// is read like any other: no report, and the strength it gives is recorded.
TEST(Preprocessor, DefaultTriregStrength_InsideAModuleIsAccepted) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>",
                           "module m;\n"
                           "`default_trireg_strength 30\n"
                           "  trireg t;\n"
                           "endmodule\n");
  pp.Preprocess(fid);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  EXPECT_TRUE(pp.HasDefaultTriregStrength());
  EXPECT_EQ(pp.DefaultTriregStrength(), 30u);
}

// §5.7.1 lets an underscore stand anywhere in a number but first, and ignores
// it, so 2_00 is the integer constant 200.
TEST(Preprocessor, DefaultTriregStrength_UnderscoredDecimalArgument) {
  PreprocFixture f;
  EXPECT_EQ(StrengthSetBy(f, "2_00"), 200u);
}

// §5.7.1's based numbers are integer constants with or without a size, in any
// of the four bases, the base letter and hexadecimal digits in either case, and
// with white space beside the base format.
TEST(Preprocessor, DefaultTriregStrength_BasedArgument) {
  PreprocFixture decimal;
  EXPECT_EQ(StrengthSetBy(decimal, "'d200"), 200u);
  PreprocFixture binary;
  EXPECT_EQ(StrengthSetBy(binary, "'B1100_1000"), 200u);
  PreprocFixture octal;
  EXPECT_EQ(StrengthSetBy(octal, "'o310"), 200u);
  PreprocFixture sized;
  EXPECT_EQ(StrengthSetBy(sized, "8'hfA"), 250u);
  PreprocFixture spaced;
  EXPECT_EQ(StrengthSetBy(spaced, "8 'h FA"), 250u);
}

// A sized constant holds its size in bits, so digits wider than the size lose
// their leftmost bits: 4'd200 is 8. A size of 64 or more keeps every digit.
TEST(Preprocessor, DefaultTriregStrength_SizeTruncatesTheDigits) {
  PreprocFixture narrow;
  EXPECT_EQ(StrengthSetBy(narrow, "4'd200"), 8u);
  PreprocFixture wide;
  EXPECT_EQ(StrengthSetBy(wide, "72'd200"), 200u);
}

// §5.7.1's s or S marks a signed constant, which is the value its bits give
// while its top bit is clear.
TEST(Preprocessor, DefaultTriregStrength_SignedArgument) {
  PreprocFixture lower;
  EXPECT_EQ(StrengthSetBy(lower, "8'sd100"), 100u);
  PreprocFixture upper;
  EXPECT_EQ(StrengthSetBy(upper, "'Sh64"), 100u);
}

// A signed constant whose top bit is set is negative, 4'shf being -1, and a
// based value can exceed 250 as a decimal one can. E.3's range holds for both.
TEST(Preprocessor, DefaultTriregStrength_BasedValueOutsideTheRangeIsError) {
  PreprocFixture negative;
  EXPECT_EQ(StrengthSetBy(negative, "4'shf"), std::nullopt);
  EXPECT_TRUE(ReportedOutOfRange(negative));
  PreprocFixture large;
  EXPECT_EQ(StrengthSetBy(large, "'h1FF"), std::nullopt);
  EXPECT_TRUE(ReportedOutOfRange(large));
}

// An x, z or ? digit leaves the constant no number to be a strength, and a
// digit outside the base, a base format with no digits, an unknown base
// letter, a missing base letter and a size that is no positive number each
// leave the argument no integer constant.
TEST(Preprocessor, DefaultTriregStrength_MalformedBasedArgumentIsError) {
  for (const char* arg :
       {"8'hx", "'b1?", "'o9", "'o19", "'d", "'q5", "8'", "a'd5", "0'd5"}) {
    PreprocFixture f;
    EXPECT_EQ(StrengthSetBy(f, arg), std::nullopt) << arg;
    EXPECT_TRUE(ReportedInvalid(f, arg)) << arg;
  }
}

}  // namespace
