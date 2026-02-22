#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"
#include "simulation/lowerer.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"
#include "simulation/variable.h"

using namespace delta;

// §5.3 White space

struct SimCh503Fixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign* ElaborateSrc(const std::string& src, SimCh503Fixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

static uint64_t RunAndGet(const std::string& src, const char* var_name) {
  SimCh503Fixture f;
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  if (!design) return 0;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable(var_name);
  EXPECT_NE(var, nullptr);
  if (!var) return 0;
  return var->value.ToUint64();
}

// ---------------------------------------------------------------------------
// 1. Whitespace variations do not affect simulation results
// ---------------------------------------------------------------------------
TEST(SimCh503, WhitespaceSameResultWithSpaces) {
  // Normal spacing — compute a + b.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] a, b, result;\n"
      "  initial begin\n"
      "    a = 8'd10;\n"
      "    b = 8'd20;\n"
      "    result = a + b;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 30u);
}

TEST(SimCh503, WhitespaceSameResultWithTabs) {
  // Tab-delimited tokens — identical computation must yield same result.
  auto result = RunAndGet(
      "module\tt\t;\n"
      "\tlogic\t[7:0]\ta\t,\tb\t,\tresult\t;\n"
      "\tinitial\tbegin\n"
      "\t\ta\t=\t8'd10\t;\n"
      "\t\tb\t=\t8'd20\t;\n"
      "\t\tresult\t=\ta\t+\tb\t;\n"
      "\tend\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 30u);
}

TEST(SimCh503, WhitespaceSameResultWithNewlines) {
  // Every token on its own line.
  auto result = RunAndGet(
      "module\n"
      "t\n"
      ";\n"
      "logic\n"
      "[7:0]\n"
      "result\n"
      ";\n"
      "initial\n"
      "result\n"
      "=\n"
      "8'd42\n"
      ";\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 42u);
}

TEST(SimCh503, WhitespaceSameResultMinimal) {
  // Minimal whitespace — only where needed to separate keywords/identifiers.
  auto result = RunAndGet(
      "module t;logic [7:0] result;initial result=8'd55;endmodule", "result");
  EXPECT_EQ(result, 55u);
}

TEST(SimCh503, WhitespaceSameResultExcessive) {
  // Excessive whitespace everywhere.
  auto result = RunAndGet(
      "  \t\n  module   \t  t  \n  ;  \n"
      "  logic   [  7  :  0  ]   result  ;  \n"
      "  initial   result   =   8'd77   ;  \n"
      "  endmodule  \n\n  ",
      "result");
  EXPECT_EQ(result, 77u);
}

// ---------------------------------------------------------------------------
// 2. Formfeed in source does not affect simulation
// ---------------------------------------------------------------------------
TEST(SimCh503, WhitespaceFormfeedInSource) {
  // Formfeed characters between tokens — must parse and simulate identically.
  auto result = RunAndGet(
      "module t;\f"
      "logic [7:0] result;\f"
      "initial result = 8'd99;\f"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 99u);
}

// ---------------------------------------------------------------------------
// 3. Mixed whitespace in expressions does not affect evaluation
// ---------------------------------------------------------------------------
TEST(SimCh503, WhitespaceMixedInExpression) {
  // Various whitespace around operators in an expression.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] a, b, c, result;\n"
      "  initial begin\n"
      "    a = 8'd3;\n"
      "    b = 8'd4;\n"
      "    c = 8'd5;\n"
      "    result =  a \t + \n b  \f +  c ;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 12u);
}

// ---------------------------------------------------------------------------
// 4. Whitespace around assignment operator
// ---------------------------------------------------------------------------
TEST(SimCh503, WhitespaceAroundAssignment) {
  // No whitespace around '=' — still valid.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result=8'd33;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 33u);
}

// ---------------------------------------------------------------------------
// 5. String literal preserves blanks and tabs (§5.3 + §5.9)
// ---------------------------------------------------------------------------
TEST(SimCh503, WhitespaceStringLiteralPreserved) {
  // §5.3: blanks and tabs are significant in string literals.
  // Assign a string with spaces to a wide variable and verify encoding.
  SimCh503Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [63:0] s;\n"
      "  initial s = \"a b\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("s");
  ASSERT_NE(var, nullptr);
  // "a b" is 3 bytes: 'a'=0x61, ' '=0x20, 'b'=0x62
  // Stored MSB first: 0x61_20_62 = 6365282
  uint64_t val = var->value.ToUint64();
  EXPECT_EQ(val & 0xFF, 0x62u);          // 'b'
  EXPECT_EQ((val >> 8) & 0xFF, 0x20u);   // ' '
  EXPECT_EQ((val >> 16) & 0xFF, 0x61u);  // 'a'
}

TEST(SimCh503, WhitespaceStringLiteralTabPreserved) {
  // §5.3: tabs are significant in string literals.
  // Use a literal tab character inside the SV string literal.
  SimCh503Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [63:0] s;\n"
      "  initial s = \"a\tb\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("s");
  ASSERT_NE(var, nullptr);
  // "a<TAB>b" is 3 bytes: 'a'=0x61, '\t'=0x09, 'b'=0x62
  uint64_t val = var->value.ToUint64();
  EXPECT_EQ(val & 0xFF, 0x62u);          // 'b'
  EXPECT_EQ((val >> 8) & 0xFF, 0x09u);   // '\t'
  EXPECT_EQ((val >> 16) & 0xFF, 0x61u);  // 'a'
}

// ---------------------------------------------------------------------------
// 6. Whitespace as token separator — keyword separation
// ---------------------------------------------------------------------------
TEST(SimCh503, WhitespaceSeparatesKeywords) {
  // Without space, "moduleendmodule" would not parse. Whitespace separates.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial begin result = 8'd1; end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 1u);
}

// ---------------------------------------------------------------------------
// 7. always_comb with various whitespace patterns
// ---------------------------------------------------------------------------
TEST(SimCh503, WhitespaceAlwaysCombWithFormfeed) {
  // Formfeed inside always_comb body.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] a, result;\n"
      "  initial a = 8'd7;\n"
      "  always_comb begin\f"
      "    result = a + 8'd3;\f"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 10u);
}

// ---------------------------------------------------------------------------
// 8. Whitespace in concatenation expression
// ---------------------------------------------------------------------------
TEST(SimCh503, WhitespaceInConcatenation) {
  // Various whitespace around concatenation braces.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    a = 4'hA;\n"
      "    b = 4'h5;\n"
      "    result = { \t a \n , \f b \t };\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 0xA5u);
}

// ---------------------------------------------------------------------------
// 9. Whitespace around conditional operator
// ---------------------------------------------------------------------------
TEST(SimCh503, WhitespaceAroundTernary) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial result = 1'b1 \t ? \n 8'd100 \f : \t 8'd200;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 100u);
}

// ---------------------------------------------------------------------------
// 10. Multiple statements with only whitespace between
// ---------------------------------------------------------------------------
TEST(SimCh503, WhitespaceMultipleStatements) {
  SimCh503Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  initial begin\n"
      "    a = 8'd10; \t \n b = 8'd20; \f\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* a = f.ctx.FindVariable("a");
  auto* b = f.ctx.FindVariable("b");
  ASSERT_NE(a, nullptr);
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(a->value.ToUint64(), 10u);
  EXPECT_EQ(b->value.ToUint64(), 20u);
}
