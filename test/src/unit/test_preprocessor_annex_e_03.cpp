#include <gtest/gtest.h>

#include <cstdint>
#include <optional>
#include <string>

#include "fixture_preprocessor.h"
#include "helpers_reported_error.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

namespace {

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

::testing::AssertionResult ReportedInvalid(const PreprocFixture& f,
                                           const std::string& arg) {
  return ReportedError(
      f.diag.Diagnostics(),
      "invalid `default_trireg_strength argument: '" + arg + "'", 1, "E.3");
}

::testing::AssertionResult ReportedOutOfRange(const PreprocFixture& f) {
  return ReportedError(
      f.diag.Diagnostics(),
      "`default_trireg_strength value must be between 0 and 250", 1, "E.3");
}

TEST(Preprocessor, DefaultTriregStrength_IntegerArgument) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "`default_trireg_strength 100\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(pp.HasDefaultTriregStrength());
  EXPECT_EQ(pp.DefaultTriregStrength(), 100u);
}

TEST(Preprocessor, DefaultTriregStrength_MissingArgumentIsError) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "`default_trireg_strength\n");
  pp.Preprocess(fid);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "`default_trireg_strength requires an argument", 1,
                            "E.3"));
}

TEST(Preprocessor, DefaultTriregStrength_NonIntegerArgumentIsError) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "`default_trireg_strength strong\n");
  pp.Preprocess(fid);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "invalid `default_trireg_strength argument: 'strong'", 1, "E.3"));
}

TEST(Preprocessor, DefaultTriregStrength_LowerBoundZeroAccepted) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "`default_trireg_strength 0\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(pp.HasDefaultTriregStrength());
  EXPECT_EQ(pp.DefaultTriregStrength(), 0u);
}

TEST(Preprocessor, DefaultTriregStrength_UpperBound250Accepted) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "`default_trireg_strength 250\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(pp.HasDefaultTriregStrength());
  EXPECT_EQ(pp.DefaultTriregStrength(), 250u);
}

TEST(Preprocessor, DefaultTriregStrength_AboveRangeIsError) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "`default_trireg_strength 251\n");
  pp.Preprocess(fid);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "`default_trireg_strength value must be between 0 and 250", 1, "E.3"));
}

TEST(Preprocessor, DefaultTriregStrength_DefaultStateNoDirective) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  auto fid = f.mgr.AddFile("<test>", "module m; endmodule\n");
  pp.Preprocess(fid);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(pp.HasDefaultTriregStrength());
}

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

TEST(Preprocessor, DefaultTriregStrength_UnderscoredDecimalArgument) {
  PreprocFixture f;
  EXPECT_EQ(StrengthSetBy(f, "2_00"), 200u);
}

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

TEST(Preprocessor, DefaultTriregStrength_SizeTruncatesTheDigits) {
  PreprocFixture narrow;
  EXPECT_EQ(StrengthSetBy(narrow, "4'd200"), 8u);
  PreprocFixture wide;
  EXPECT_EQ(StrengthSetBy(wide, "72'd200"), 200u);
}

TEST(Preprocessor, DefaultTriregStrength_SignedArgument) {
  PreprocFixture lower;
  EXPECT_EQ(StrengthSetBy(lower, "8'sd100"), 100u);
  PreprocFixture upper;
  EXPECT_EQ(StrengthSetBy(upper, "'Sh64"), 100u);
}

TEST(Preprocessor, DefaultTriregStrength_BasedValueOutsideTheRangeIsError) {
  PreprocFixture negative;
  EXPECT_EQ(StrengthSetBy(negative, "4'shf"), std::nullopt);
  EXPECT_TRUE(ReportedOutOfRange(negative));
  PreprocFixture large;
  EXPECT_EQ(StrengthSetBy(large, "'h1FF"), std::nullopt);
  EXPECT_TRUE(ReportedOutOfRange(large));
}

TEST(Preprocessor, DefaultTriregStrength_MalformedBasedArgumentIsError) {
  for (const char* arg :
       {"8'hx", "'b1?", "'o9", "'o19", "'d", "'q5", "8'", "a'd5", "0'd5"}) {
    PreprocFixture f;
    EXPECT_EQ(StrengthSetBy(f, arg), std::nullopt) << arg;
    EXPECT_TRUE(ReportedInvalid(f, arg)) << arg;
  }
}

}  // namespace
