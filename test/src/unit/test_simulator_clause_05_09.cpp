#include <gtest/gtest.h>

#include <cstring>
#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "simulation/lowerer.h"
#include "simulation/scheduler.h"
#include "simulation/sim_context.h"
#include "simulation/variable.h"

using namespace delta;

struct SimCh509Fixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign *ElaborateSrc(const std::string &src, SimCh509Fixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

static uint64_t RunAndGet(const std::string &src, const char *var_name) {
  SimCh509Fixture f;
  auto *design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  if (!design)
    return 0;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable(var_name);
  EXPECT_NE(var, nullptr);
  if (!var)
    return 0;
  return var->value.ToUint64();
}

// ===========================================================================
// §5.9 String literals
// ===========================================================================

// ---------------------------------------------------------------------------
// 1. Single-character string to byte — §5.9 example
// ---------------------------------------------------------------------------
TEST(SimCh509, StrLitSingleChar) {
  // §5.9 example: byte c1 = "A"
  auto v =
      RunAndGet("module t;\n  byte c;\n  initial c = \"A\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x41u);
}

// ---------------------------------------------------------------------------
// 2. Multi-character string — 8-bit-per-character packing
// ---------------------------------------------------------------------------
TEST(SimCh509, StrLitMultiChar) {
  // §5.9: String packs as a sequence of 8-bit ASCII values.
  auto v = RunAndGet(
      "module t;\n  bit [23:0] s;\n  initial s = \"ABC\";\nendmodule\n", "s");
  EXPECT_EQ(v, 0x414243u);
}

// ---------------------------------------------------------------------------
// 3. Larger destination — right-justified, zero-padded
// ---------------------------------------------------------------------------
TEST(SimCh509, StrLitZeroPad) {
  // §5.9: Larger destination — right-justified, zero-padded on the left.
  auto v = RunAndGet(
      "module t;\n  bit [15:0] s;\n  initial s = \"A\";\nendmodule\n", "s");
  EXPECT_EQ(v, 0x0041u);
}

// ---------------------------------------------------------------------------
// 4. Smaller destination — right-justified, leftmost truncated
// ---------------------------------------------------------------------------
TEST(SimCh509, StrLitTruncateLeft) {
  // §5.9: Smaller destination — right-justified, leftmost chars truncated.
  auto v = RunAndGet(
      "module t;\n  byte s;\n  initial s = \"ABCD\";\nendmodule\n", "s");
  EXPECT_EQ(v, 0x44u);
}

// ---------------------------------------------------------------------------
// 5. Triple-quoted string — basic
// ---------------------------------------------------------------------------
TEST(SimCh509, StrLitTripleBasic) {
  // §5.9: Triple-quoted string literal.
  auto v = RunAndGet("module t;\n  bit [15:0] s;\n"
                     "  initial s = \"\"\"AB\"\"\";\nendmodule\n",
                     "s");
  EXPECT_EQ(v, 0x4142u);
}

// ---------------------------------------------------------------------------
// 6. Triple-quoted string — embedded newline (no escape needed)
// ---------------------------------------------------------------------------
TEST(SimCh509, StrLitTripleNewline) {
  // §5.9: Triple-quoted string allows direct newline characters.
  auto v = RunAndGet("module t;\n  bit [23:0] s;\n"
                     "  initial s = \"\"\"A\nB\"\"\";\nendmodule\n",
                     "s");
  EXPECT_EQ(v, 0x410A42u);
}

// ---------------------------------------------------------------------------
// 7. Triple-quoted string — embedded double-quote (no escape needed)
// ---------------------------------------------------------------------------
TEST(SimCh509, StrLitTripleQuote) {
  // §5.9: Triple-quoted string allows embedded double-quote without escape.
  auto v = RunAndGet("module t;\n  bit [23:0] s;\n"
                     "  initial s = \"\"\"A\"B\"\"\";\nendmodule\n",
                     "s");
  EXPECT_EQ(v, 0x412242u);
}

// ---------------------------------------------------------------------------
// 8. Line continuation — backslash-newline stripped in quoted string
// ---------------------------------------------------------------------------
TEST(SimCh509, StrLitLineContinuation) {
  // §5.9: Line continuation — backslash-newline stripped from string.
  auto v = RunAndGet("module t;\n  bit [31:0] s;\n"
                     "  initial s = \"AB\\\nCD\";\nendmodule\n",
                     "s");
  EXPECT_EQ(v, 0x41424344u);
}

// ---------------------------------------------------------------------------
// 9. Double-backslash before newline — \\ escape + line continuation
// ---------------------------------------------------------------------------
TEST(SimCh509, StrLitDoubleBackslashNewline) {
  // §5.9.1: \\\<newline> -> \\ is backslash escape, \<newline> is
  // line continuation.  "A" + '\' + "B" = 0x415C42.
  auto v = RunAndGet("module t;\n  bit [23:0] s;\n"
                     "  initial s = \"A\\\\\\\nB\";\nendmodule\n",
                     "s");
  EXPECT_EQ(v, 0x415C42u);
}

// ---------------------------------------------------------------------------
// 10. Triple-quoted line continuation — same behavior as quoted
// ---------------------------------------------------------------------------
TEST(SimCh509, StrLitTripleContinuation) {
  // §5.9: Triple-quoted line continuation behaves like single-quoted.
  auto v = RunAndGet("module t;\n  bit [31:0] s;\n"
                     "  initial s = \"\"\"AB\\\nCD\"\"\";\nendmodule\n",
                     "s");
  EXPECT_EQ(v, 0x41424344u);
}
