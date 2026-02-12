#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "lexer/keywords.h"
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
  // §22.8: "none" forbids implicit net declarations.
  EXPECT_EQ(pp.DefaultNetType(), NetType::kNone);
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

// --- begin_keywords / end_keywords tests (IEEE 1800-2023 §22.14) ---

TEST(Preprocessor, BeginKeywords_EmitsMarker) {
  PreprocFixture f;
  auto result = Preprocess("`begin_keywords \"1364-2001\"\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  // Marker: \x01 + version byte (1 = kVer13642001) + \n
  std::string expected = {kKeywordMarker, '\x01', '\n'};
  EXPECT_NE(result.find(expected), std::string::npos);
}

TEST(Preprocessor, EndKeywords_EmitsRestoreMarker) {
  PreprocFixture f;
  auto result = Preprocess(
      "`begin_keywords \"1364-2001\"\n"
      "`end_keywords\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  // After end_keywords with empty stack, restores to kVer18002023 (8).
  std::string restore = {kKeywordMarker, '\x08', '\n'};
  EXPECT_NE(result.find(restore), std::string::npos);
}

TEST(Preprocessor, BeginKeywords_InvalidVersion) {
  PreprocFixture f;
  Preprocess("`begin_keywords \"bogus\"\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, EndKeywords_WithoutBegin) {
  PreprocFixture f;
  Preprocess("`end_keywords\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, BeginKeywords_NestedRestoresVersion) {
  PreprocFixture f;
  auto result = Preprocess(
      "`begin_keywords \"1364-2001\"\n"
      "`begin_keywords \"1800-2005\"\n"
      "`end_keywords\n"
      "`end_keywords\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  // First begin: version 1 (1364-2001)
  std::string m1 = {kKeywordMarker, '\x01', '\n'};
  // Second begin: version 4 (1800-2005)
  std::string m2 = {kKeywordMarker, '\x04', '\n'};
  // Second end: restore to 8 (1800-2023)
  std::string m4 = {kKeywordMarker, '\x08', '\n'};
  EXPECT_NE(result.find(m1), std::string::npos);
  EXPECT_NE(result.find(m2), std::string::npos);
  // First end restores to version 1, same as m1 — already verified.
  EXPECT_NE(result.find(m4), std::string::npos);
}

// --- Macro default parameter tests (IEEE 1800-2023 §22.5.1) ---

TEST(Preprocessor, MacroDefaultParam) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define M(a=1, b=2) a+b\n"
      "`M(,)\n",
      f);
  EXPECT_NE(result.find("1+2"), std::string::npos);
}

TEST(Preprocessor, MacroDefaultParamPartial) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define M(a=1, b) a+b\n"
      "`M(,3)\n",
      f);
  EXPECT_NE(result.find("1+3"), std::string::npos);
}

TEST(Preprocessor, MacroDefaultParamOverride) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define M(a=1) a\n"
      "`M(5)\n",
      f);
  EXPECT_NE(result.find("5"), std::string::npos);
}

TEST(Preprocessor, MacroDefaultParamString) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define M(a=\"hello\") a\n"
      "`M()\n",
      f);
  EXPECT_NE(result.find("\"hello\""), std::string::npos);
}

// --- Multi-line macro tests (IEEE 1800-2023 §22.5.1) ---

TEST(Preprocessor, MultiLineMacro) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define BLOCK(x) begin \\\n"
      "  x; \\\n"
      "end\n"
      "`BLOCK(foo)\n",
      f);
  EXPECT_NE(result.find("begin"), std::string::npos);
  EXPECT_NE(result.find("foo;"), std::string::npos);
  EXPECT_NE(result.find("end"), std::string::npos);
}

TEST(Preprocessor, MultiLineMacroContinuation) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define LONG a + \\\n"
      "b + \\\n"
      "c\n"
      "`LONG\n",
      f);
  EXPECT_NE(result.find("a + b + c"), std::string::npos);
}

// --- Ifdef expression tests (IEEE 1800-2023 §22.6) ---

TEST(Preprocessor, IfdefExprAnd) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"A", "1"}, {"B", "1"}};
  auto result = Preprocess(
      "`ifdef (A && B)\n"
      "both_defined\n"
      "`endif\n",
      f, std::move(cfg));
  EXPECT_NE(result.find("both_defined"), std::string::npos);
}

TEST(Preprocessor, IfdefExprAndFalse) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"A", "1"}};
  auto result = Preprocess(
      "`ifdef (A && B)\n"
      "both_defined\n"
      "`endif\n",
      f, std::move(cfg));
  EXPECT_EQ(result.find("both_defined"), std::string::npos);
}

TEST(Preprocessor, IfdefExprOr) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"A", "1"}};
  auto result = Preprocess(
      "`ifdef (A || B)\n"
      "either_defined\n"
      "`endif\n",
      f, std::move(cfg));
  EXPECT_NE(result.find("either_defined"), std::string::npos);
}

TEST(Preprocessor, IfdefExprNot) {
  PreprocFixture f;
  auto result = Preprocess(
      "`ifdef (!A)\n"
      "not_defined\n"
      "`endif\n",
      f);
  EXPECT_NE(result.find("not_defined"), std::string::npos);
}

TEST(Preprocessor, IfdefExprComplex) {
  PreprocFixture f;
  PreprocConfig cfg;
  cfg.defines = {{"A", "1"}};
  auto result = Preprocess(
      "`ifdef (A && (B || !C))\n"
      "complex_true\n"
      "`endif\n",
      f, std::move(cfg));
  EXPECT_NE(result.find("complex_true"), std::string::npos);
}

// --- __LINE__ with `line directive ---

TEST(Preprocessor, LineDirectiveAffectsLineMacro) {
  PreprocFixture f;
  auto result = Preprocess(
      "`line 100 \"test.sv\" 0\n"
      "`__LINE__\n",
      f);
  EXPECT_NE(result.find("101"), std::string::npos);
}

// --- Inline macro expansion ---

TEST(Preprocessor, InlineMacro_ExpandsDefined) {
  PreprocFixture f;
  auto result = Preprocess("`define FOO 42\nint x = `FOO;\n", f);
  EXPECT_NE(result.find("int x = 42;"), std::string::npos);
}

TEST(Preprocessor, InlineMacro_ExpandsFileInline) {
  PreprocFixture f;
  auto result = Preprocess("$display(`__FILE__);\n", f);
  EXPECT_NE(result.find("$display(\"<test>\");"), std::string::npos);
}

TEST(Preprocessor, InlineMacro_ExpandsLineInline) {
  PreprocFixture f;
  auto result = Preprocess("$display(`__LINE__);\n", f);
  EXPECT_NE(result.find("$display(1);"), std::string::npos);
}

TEST(Preprocessor, InlineMacro_SkipsStringLiterals) {
  PreprocFixture f;
  auto result = Preprocess("`define FOO 42\n\"hello `FOO\";\n", f);
  EXPECT_NE(result.find("\"hello `FOO\""), std::string::npos);
}

TEST(Preprocessor, InlineMacro_MultipleMacrosOnOneLine) {
  PreprocFixture f;
  auto result = Preprocess("`define A 1\n`define B 2\nint x = `A + `B;\n", f);
  EXPECT_NE(result.find("int x = 1 + 2;"), std::string::npos);
}

TEST(Preprocessor, InlineMacro_FunctionLikeMacro) {
  PreprocFixture f;
  auto result =
      Preprocess("`define ADD(a, b) (a + b)\nint x = `ADD(3, 4);\n", f);
  EXPECT_NE(result.find("int x = (3 + 4);"), std::string::npos);
}

TEST(Preprocessor, InlineMacro_CommandLineDefines) {
  PreprocFixture f;
  PreprocConfig config;
  config.defines = {{"VAR_1", "2"}, {"VAR_2", "5"}};
  auto result = Preprocess("int a = `VAR_1 + `VAR_2;\n", f, config);
  EXPECT_NE(result.find("int a = 2 + 5;"), std::string::npos);
}

// --- Absolute include paths ---

TEST(Preprocessor, Include_AbsolutePath) {
  PreprocFixture f;
  auto result = Preprocess("`include \"/dev/null\"\nmodule m; endmodule\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("module m;"), std::string::npos);
}

// --- §22.5.3 `undefineall ---

TEST(Preprocessor, UndefineAll) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define FOO 42\n"
      "`undefineall\n"
      "`ifdef FOO\n"
      "visible\n"
      "`endif\n",
      f);
  EXPECT_EQ(result.find("visible"), std::string::npos);
}

// §22.12: `line directive validation
TEST(Preprocessor, Line_IllegalLevel) {
  PreprocFixture f;
  Preprocess("`line 1 \"somefile\" 3\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Line_NonStringFilename) {
  PreprocFixture f;
  Preprocess("`line 1 somefile 2\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Line_NegativeLineNumber) {
  PreprocFixture f;
  Preprocess("`line -12 \"somefile\" 3\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Line_MissingLevel) {
  PreprocFixture f;
  Preprocess("`line 1 \"somefile\"\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Preprocessor, Line_MissingFilename) {
  PreprocFixture f;
  Preprocess("`line 1\n", f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §22 Table 22-2: SV_COV_* predefined coverage macros
TEST(Preprocessor, SvCovPredefinedMacros) {
  PreprocFixture f;
  auto result = Preprocess(
      "`ifdef SV_COV_START\n"
      "cov_start_defined\n"
      "`endif\n"
      "val=`SV_COV_START\n",
      f);
  EXPECT_NE(result.find("cov_start_defined"), std::string::npos);
  EXPECT_NE(result.find("val=0"), std::string::npos);
}

TEST(Preprocessor, SvCovToggleValue) {
  PreprocFixture f;
  auto result = Preprocess("x=`SV_COV_TOGGLE\n", f);
  EXPECT_NE(result.find("x=23"), std::string::npos);
}

TEST(Preprocessor, SvCovErrorValue) {
  PreprocFixture f;
  auto result = Preprocess("x=`SV_COV_ERROR\n", f);
  EXPECT_NE(result.find("x=-1"), std::string::npos);
}

// §22.3: `resetall shall not affect text macros
TEST(Preprocessor, ResetAll_PreservesTextMacros) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define FOO bar\n"
      "`resetall\n"
      "int x = `FOO;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("bar"), std::string::npos);
}

// §22.8: `default_nettype trireg
TEST(Preprocessor, DefaultNettypeTrireg) {
  PreprocFixture f;
  Preprocess("`default_nettype trireg\n", f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §22.4: include filename with trailing comment
TEST(Preprocessor, IncludeFilenameStripsComment) {
  PreprocFixture f;
  // The include filename should stop at closing ", not consume comments
  Preprocess("`include \"nonexistent.sv\" // this is a comment\n", f);
  // Should error about "nonexistent.sv", not a garbled filename with comment
  EXPECT_TRUE(f.diag.HasErrors());
}

// §22.5.1: macro expansion preserves trailing text on the line
TEST(Preprocessor, MacroExpansionTrailingText) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define TAG(x) x\n"
      "`TAG(hello) world;\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("hello world"), std::string::npos);
}

// §22.5.1: function-like macro with trailing tokens
TEST(Preprocessor, FunctionMacroTrailingTokens) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define GATE(d) nand #d\n"
      "`GATE(2) g1 (q, a, b);\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("nand #2 g1"), std::string::npos);
}

// §22.5.1: macro string delimiter `"
TEST(Preprocessor, MacroStringDelimiter) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define msg(x,y) `\"x: `\\`\"y`\\`\"`\"\n"
      "$display(`msg(left side,right side));\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  // Should expand to: $display("left side: \"right side\"");
  EXPECT_NE(result.find("\"left side: \\\"right side\\\"\""),
            std::string::npos);
}

// §22.5.1: `" for constructing filenames
TEST(Preprocessor, MacroStringFilename) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define home(filename) `\"/home/mydir/filename`\"\n"
      "`home(myfile)\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("\"/home/mydir/myfile\""), std::string::npos);
}
