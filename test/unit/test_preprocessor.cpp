#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

struct PreprocFixture {
  SourceManager mgr;
  DiagEngine diag{mgr};
};

static std::string Preprocess(const std::string& src, PreprocFixture& f,
                              PreprocConfig config = {}) {
  auto fid = f.mgr.AddFile("<test>", src);
  Preprocessor pp(f.mgr, f.diag, std::move(config));
  return pp.Preprocess(fid);
}

static std::string PreprocessWithPP(const std::string& src, PreprocFixture& f,
                                    Preprocessor& pp) {
  auto fid = f.mgr.AddFile("<test>", src);
  return pp.Preprocess(fid);
}

TEST(Preprocessor, ElsifTakesSecondBranch) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"B", "1"}};
  auto result = Preprocess(
      "`ifdef A\n"
      "line_a\n"
      "`elsif B\n"
      "line_b\n"
      "`endif\n",
      f, std::move(cfg));
  EXPECT_NE(result.find("line_b"), std::string::npos);
  EXPECT_EQ(result.find("line_a"), std::string::npos);
}

TEST(Preprocessor, ElsifSkippedWhenFirstTaken) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"A", "1"}, {"B", "1"}};
  auto result = Preprocess(
      "`ifdef A\n"
      "line_a\n"
      "`elsif B\n"
      "line_b\n"
      "`endif\n",
      f, std::move(cfg));
  EXPECT_NE(result.find("line_a"), std::string::npos);
  EXPECT_EQ(result.find("line_b"), std::string::npos);
}

TEST(Preprocessor, ElsifElseFallthrough) {
  PreprocFixture f;
  auto result = Preprocess(
      "`ifdef A\n"
      "line_a\n"
      "`elsif B\n"
      "line_b\n"
      "`else\n"
      "line_else\n"
      "`endif\n",
      f);
  EXPECT_EQ(result.find("line_a"), std::string::npos);
  EXPECT_EQ(result.find("line_b"), std::string::npos);
  EXPECT_NE(result.find("line_else"), std::string::npos);
}

TEST(Preprocessor, MultipleElsif) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"C", "1"}};
  auto result = Preprocess(
      "`ifdef A\n"
      "line_a\n"
      "`elsif B\n"
      "line_b\n"
      "`elsif C\n"
      "line_c\n"
      "`else\n"
      "line_else\n"
      "`endif\n",
      f, std::move(cfg));
  EXPECT_EQ(result.find("line_a"), std::string::npos);
  EXPECT_EQ(result.find("line_b"), std::string::npos);
  EXPECT_NE(result.find("line_c"), std::string::npos);
  EXPECT_EQ(result.find("line_else"), std::string::npos);
}

TEST(Preprocessor, NestedIfdefInsideElsif) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"B", "1"}, {"INNER", "1"}};
  auto result = Preprocess(
      "`ifdef A\n"
      "line_a\n"
      "`elsif B\n"
      "`ifdef INNER\n"
      "line_inner\n"
      "`endif\n"
      "`endif\n",
      f, std::move(cfg));
  EXPECT_NE(result.find("line_inner"), std::string::npos);
  EXPECT_EQ(result.find("line_a"), std::string::npos);
}

TEST(Preprocessor, BasicFunctionLikeMacro) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define ADD(a, b) a + b\n"
      "`ADD(3, 4)\n",
      f);
  EXPECT_NE(result.find("3 + 4"), std::string::npos);
}

TEST(Preprocessor, MultiParamMacro) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define MUX(sel, a, b) (sel ? a : b)\n"
      "`MUX(s, x, y)\n",
      f);
  EXPECT_NE(result.find("(s ? x : y)"), std::string::npos);
}

TEST(Preprocessor, NestedParensInArgs) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define CALL(f, x) f(x)\n"
      "`CALL(foo, (a+b))\n",
      f);
  EXPECT_NE(result.find("foo((a+b))"), std::string::npos);
}

TEST(Preprocessor, ObjectLikeNotConfusedWithFunctionLike) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define FOO (1+2)\n"
      "`FOO\n",
      f);
  EXPECT_NE(result.find("(1+2)"), std::string::npos);
}

TEST(Preprocessor, FileExpansion) {
  PreprocFixture f;
  auto result = Preprocess("`__FILE__\n", f);
  EXPECT_NE(result.find("\"<test>\""), std::string::npos);
}

TEST(Preprocessor, LineExpansion) {
  PreprocFixture f;
  auto result = Preprocess(
      "line1\n"
      "`__LINE__\n",
      f);
  EXPECT_NE(result.find('2'), std::string::npos);
}

TEST(Preprocessor, IfdefElseRegression) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"A", "1"}};
  auto result = Preprocess(
      "`ifdef A\n"
      "line_a\n"
      "`else\n"
      "line_else\n"
      "`endif\n",
      f, std::move(cfg));
  EXPECT_NE(result.find("line_a"), std::string::npos);
  EXPECT_EQ(result.find("line_else"), std::string::npos);
}

// --- Timescale tests ---

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

TEST(Preprocessor, Timescale_GlobalPrecision) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`timescale 1ns / 1ns\n", f, pp);
  EXPECT_EQ(pp.GlobalPrecision(), TimeUnit::kNs);
  PreprocessWithPP("`timescale 1us / 1ps\n", f, pp);
  // Global precision is the finest (most negative exponent).
  EXPECT_EQ(pp.GlobalPrecision(), TimeUnit::kPs);
}

TEST(Preprocessor, Timescale_InvalidUnit) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`timescale 1xx / 1ns\n", f, pp);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, DelayToTicks_Basic) {
  TimeScale ts;
  ts.unit = TimeUnit::kNs;
  ts.magnitude = 1;
  // 10 delay units at 1ns with 1ps precision = 10,000 ticks.
  EXPECT_EQ(DelayToTicks(10, ts, TimeUnit::kPs), 10000);
}

TEST(Preprocessor, DelayToTicks_Magnitude) {
  TimeScale ts;
  ts.unit = TimeUnit::kUs;
  ts.magnitude = 100;
  // 5 delay units at 100us with 1ns precision = 5 * 100 * 1000 = 500,000 ticks.
  EXPECT_EQ(DelayToTicks(5, ts, TimeUnit::kNs), 500000);
}

// --- default_nettype tests ---

TEST(Preprocessor, DefaultNettype_Wire) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`default_nettype wire\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DefaultNetType(), NetType::kWire);
}

TEST(Preprocessor, DefaultNettype_None) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`default_nettype none\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  // "none" maps to kWire as sentinel.
  EXPECT_EQ(pp.DefaultNetType(), NetType::kWire);
}

TEST(Preprocessor, DefaultNettype_Tri) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`default_nettype tri\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.DefaultNetType(), NetType::kTri);
}

// --- celldefine tests ---

TEST(Preprocessor, Celldefine_Toggle) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  EXPECT_FALSE(pp.InCelldefine());
  PreprocessWithPP("`celldefine\n", f, pp);
  EXPECT_TRUE(pp.InCelldefine());
  PreprocessWithPP("`endcelldefine\n", f, pp);
  EXPECT_FALSE(pp.InCelldefine());
}

// --- unconnected_drive tests ---

TEST(Preprocessor, UnconnectedDrive_Pull0) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`unconnected_drive pull0\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(pp.UnconnectedDrive(), NetType::kTri0);
}

TEST(Preprocessor, NounconnectedDrive_Reset) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`unconnected_drive pull1\n", f, pp);
  EXPECT_EQ(pp.UnconnectedDrive(), NetType::kTri1);
  PreprocessWithPP("`nounconnected_drive\n", f, pp);
  EXPECT_EQ(pp.UnconnectedDrive(), NetType::kWire);
}

// --- pragma tests ---

TEST(Preprocessor, Pragma_Consumed) {
  PreprocFixture f;
  auto result = Preprocess("`pragma protect begin\ncode\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  // Pragma line should be consumed (not appear in output).
  EXPECT_EQ(result.find("pragma"), std::string::npos);
  EXPECT_NE(result.find("code"), std::string::npos);
}

// --- line directive tests ---

TEST(Preprocessor, Line_OverridesLineNumber) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`line 42 \"foo.sv\" 0\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(pp.HasLineOverride());
  EXPECT_EQ(pp.LineOffset(), 42);
}

// --- begin_keywords / end_keywords tests ---

TEST(Preprocessor, BeginKeywords_EmitsWarning) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`begin_keywords \"1800-2023\"\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(f.diag.WarningCount() > 0);
}

TEST(Preprocessor, EndKeywords_EmitsWarning) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  PreprocessWithPP("`end_keywords\n", f, pp);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_TRUE(f.diag.WarningCount() > 0);
}
