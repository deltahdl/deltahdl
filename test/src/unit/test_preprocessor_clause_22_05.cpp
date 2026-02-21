#include <gtest/gtest.h>

#include "common/diagnostic.h"
#include "common/source_mgr.h"
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
  EXPECT_NE(result.find('5'), std::string::npos);
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

// --- Inline macro expansion ---

TEST(Preprocessor, InlineMacro_ExpandsDefined) {
  PreprocFixture f;
  auto result = Preprocess("`define FOO 42\nint x = `FOO;\n", f);
  EXPECT_NE(result.find("int x = 42;"), std::string::npos);
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

// --- Tests from test_lexical.cpp (LRM §22.5.1) ---

TEST(Preprocessor, Define_WithDefaultArgs) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define ASSERT(cond, msg=\"error\") if (!(cond)) $error(msg)\n"
      "`ASSERT(x)\n",
      f);
  EXPECT_NE(result.find("if (!(x)) $error(\"error\")"), std::string::npos);
}

TEST(Preprocessor, Define_Stringification) {
  // `` (double backtick) concatenation in macros
  PreprocFixture f;
  auto result = Preprocess(
      "`define CONCAT(a, b) a``b\n"
      "`CONCAT(foo, bar)\n",
      f);
  EXPECT_NE(result.find("foobar"), std::string::npos);
}

TEST(Preprocessor, Define_EmptyArgUsesDefault) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define M(a, b=99) a + b\n"
      "`M(1,)\n",
      f);
  EXPECT_NE(result.find("1 + 99"), std::string::npos);
}
