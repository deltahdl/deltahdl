#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_parser.h"
#include "fixture_preprocessor.h"
#include "fixture_preprocessor_timescale.h"

using namespace delta;

static std::string PreprocessWithPP(const std::string& src, PreprocFixture& f,
                                    Preprocessor& pp) {
  auto fid = f.mgr.AddFile("<test>", src);
  return pp.Preprocess(fid);
}

namespace {

TEST(Preprocessor, Timescale_ParseBasic) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`timescale 1ns / 1ps\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.CurrentTimescale().unit, TimeUnit::kNs);
  EXPECT_EQ(pp.CurrentTimescale().magnitude, 1);
  EXPECT_EQ(pp.CurrentTimescale().precision, TimeUnit::kPs);
  EXPECT_EQ(pp.CurrentTimescale().prec_magnitude, 1);
}

TEST(Preprocessor, Timescale_ParseMagnitude) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`timescale 100us / 10ns\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.CurrentTimescale().unit, TimeUnit::kUs);
  EXPECT_EQ(pp.CurrentTimescale().magnitude, 100);
  EXPECT_EQ(pp.CurrentTimescale().precision, TimeUnit::kNs);
  EXPECT_EQ(pp.CurrentTimescale().prec_magnitude, 10);
}

TEST(Preprocessor, Timescale_InvalidUnit) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`timescale 1xx / 1ns\n", f, pp);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, DelayToTicks_Magnitude) {
  TimeScale ts;
  ts.unit = TimeUnit::kUs;
  ts.magnitude = 100;

  EXPECT_EQ(DelayToTicks(5, ts, TimeUnit::kNs), 500000);
}

TEST(DesignBuildingBlockParsing, NoTimescaleDefault) {
  auto r = Preprocess("// no directives\n");
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(r.has_timescale);

  EXPECT_EQ(r.timescale.unit, TimeUnit::kNs);
  EXPECT_EQ(r.timescale.precision, TimeUnit::kNs);
}

TEST(DesignBuildingBlockParsing, DelayConversionWithTimescale) {
  auto r = Preprocess("`timescale 10ns / 1ns\n");
  EXPECT_FALSE(r.has_errors);

  EXPECT_EQ(DelayToTicks(3, r.timescale, r.global_precision), 30u);

  EXPECT_EQ(RealDelayToTicks(1.5, r.timescale, r.global_precision), 15u);
}

TEST(CompilerDirectiveParsing, TimescaleModuleNamePreserved) {
  auto r = ParseWithPreprocessor(
      "`timescale 1ns/1ps\n"
      "module foo;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "foo");
}

TEST(Preprocessor, Timescale_PrecisionLessPreciseThanUnit) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`timescale 1ns / 1us\n", f, pp);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Timescale_PrecisionEqualToUnit) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`timescale 1ns / 1ns\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Timescale_InvalidMagnitude5) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`timescale 5ns / 1ns\n", f, pp);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Timescale_InvalidMagnitude0) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`timescale 0ns / 1ns\n", f, pp);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Timescale_InvalidMagnitude1000) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`timescale 1000ns / 1ns\n", f, pp);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Timescale_UnitS) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`timescale 1s / 1s\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.CurrentTimescale().unit, TimeUnit::kS);
}

TEST(Preprocessor, Timescale_UnitMs) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`timescale 1ms / 1ms\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.CurrentTimescale().unit, TimeUnit::kMs);
}

TEST(Preprocessor, Timescale_UnitPs) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`timescale 1ps / 1ps\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.CurrentTimescale().unit, TimeUnit::kPs);
}

TEST(Preprocessor, Timescale_UnitFs) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`timescale 1fs / 1fs\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.CurrentTimescale().unit, TimeUnit::kFs);
}

TEST(Preprocessor, Timescale_SpaceBetweenMagnitudeAndUnit) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`timescale 1 ns / 1 ps\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.CurrentTimescale().unit, TimeUnit::kNs);
  EXPECT_EQ(pp.CurrentTimescale().precision, TimeUnit::kPs);
}

TEST(Preprocessor, Timescale_LaterOverridesEarlier) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`timescale 1ns / 1ps\n`timescale 10us / 1us\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.CurrentTimescale().unit, TimeUnit::kUs);
  EXPECT_EQ(pp.CurrentTimescale().magnitude, 10);
}

TEST(Preprocessor, Timescale_IllegalInsideDesignElement) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("module foo;\n`timescale 1ns / 1ps\nendmodule\n", f, pp);
  EXPECT_TRUE(f.diag.HasErrors());
}

// The "illegal within a design element" rule is not module-specific: the
// directive is equally forbidden inside every design-element kind. Exercise a
// distinct enclosing position (an interface) to confirm the same rejection.
TEST(Preprocessor, Timescale_IllegalInsideInterface) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("interface ifc;\n`timescale 1ns / 1ps\nendinterface\n", f,
                   pp);
  EXPECT_TRUE(f.diag.HasErrors());
}

// A package is another design-element position the same prohibition covers.
TEST(Preprocessor, Timescale_IllegalInsidePackage) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("package pkg;\n`timescale 1ns / 1ps\nendpackage\n", f, pp);
  EXPECT_TRUE(f.diag.HasErrors());
}

// The accepting side of the same rule: once a design element closes, the
// directive is back at compilation-unit scope and is legal again.
TEST(Preprocessor, Timescale_LegalAfterDesignElementCloses) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("module foo;\nendmodule\n`timescale 1ns / 1ps\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(pp.HasTimescale());
  EXPECT_EQ(pp.CurrentTimescale().unit, TimeUnit::kNs);
  EXPECT_EQ(pp.CurrentTimescale().precision, TimeUnit::kPs);
}

// A program is another design-element position the prohibition covers.
TEST(Preprocessor, Timescale_IllegalInsideProgram) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("program prg;\n`timescale 1ns / 1ps\nendprogram\n", f, pp);
  EXPECT_TRUE(f.diag.HasErrors());
}

// A checker is likewise a design element, so the directive is illegal inside
// it.
TEST(Preprocessor, Timescale_IllegalInsideChecker) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("checker chk;\n`timescale 1ns / 1ps\nendchecker\n", f, pp);
  EXPECT_TRUE(f.diag.HasErrors());
}

// A primitive is a design element as well; the same rejection applies.
TEST(Preprocessor, Timescale_IllegalInsidePrimitive) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("primitive prim;\n`timescale 1ns / 1ps\nendprimitive\n", f,
                   pp);
  EXPECT_TRUE(f.diag.HasErrors());
}

// A configuration is the final design-element kind this prohibition spans.
TEST(Preprocessor, Timescale_IllegalInsideConfig) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("config cfg;\n`timescale 1ns / 1ps\nendconfig\n", f, pp);
  EXPECT_TRUE(f.diag.HasErrors());
}

// The magnitude-set {1,10,100} constraint governs the precision argument in its
// own right: a value outside the set is rejected in that position too.
TEST(Preprocessor, Timescale_InvalidPrecisionMagnitude) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`timescale 1ns / 5ps\n", f, pp);
  EXPECT_TRUE(f.diag.HasErrors());
}

// The largest legal magnitude, 100, is accepted in the precision argument.
TEST(Preprocessor, Timescale_PrecisionMagnitude100) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`timescale 1us / 100ns\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.CurrentTimescale().prec_magnitude, 100);
  EXPECT_EQ(pp.CurrentTimescale().precision, TimeUnit::kNs);
}

TEST(Preprocessor, Timescale_MissingSlash) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`timescale 1ns\n", f, pp);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Timescale_MissingPrecisionAfterSlash) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`timescale 1ns /\n", f, pp);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Timescale_GlobalPrecisionTracksFines) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`timescale 1ns / 1ps\n"
      "`timescale 1us / 1ns\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.GlobalPrecision(), TimeUnit::kPs);
}

TEST(Preprocessor, Timescale_InvalidPrecisionUnit) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`timescale 1ns / 1xx\n", f, pp);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Timescale_PrecisionSameUnitLargerMagnitudeError) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`timescale 1ns / 10ns\n", f, pp);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Timescale_PrecisionSameUnitSmallerMagnitudeOk) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`timescale 10ns / 1ns\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Preprocessor, Timescale_GlobalPrecisionWithMagnitude) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`timescale 1ns / 1ps\n"
      "`timescale 1ns / 10ps\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.GlobalPrecision(), TimeUnit::kPs);
}

TEST(Preprocessor, Timescale_ResetallThenTimescale) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`timescale 1ns / 1ps\n"
      "`resetall\n"
      "`timescale 1us / 1ns\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(pp.HasTimescale());
  EXPECT_EQ(pp.CurrentTimescale().unit, TimeUnit::kUs);
  EXPECT_EQ(pp.CurrentTimescale().precision, TimeUnit::kNs);
}

TEST(Preprocessor, Timescale_ResetallClearsTimescale) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP(
      "`timescale 1ns / 1ps\n"
      "`resetall\n",
      f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_FALSE(pp.HasTimescale());
}

}  // namespace
