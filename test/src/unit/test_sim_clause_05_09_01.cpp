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

struct SimCh50901Fixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign* ElaborateSrc(const std::string& src, SimCh50901Fixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

static uint64_t RunAndGet(const std::string& src, const char* var_name) {
  SimCh50901Fixture f;
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

// ===========================================================================
// §5.9.1 Special characters in strings
// ===========================================================================

// ---------------------------------------------------------------------------
// 1. \n — Newline character (0x0A)
// ---------------------------------------------------------------------------
TEST(SimCh50901, StrEscNewline) {
  // §5.9.1 Table 5-1: \n → newline character
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\n\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x0Au);
}

// ---------------------------------------------------------------------------
// 2. \t — Tab character (0x09)
// ---------------------------------------------------------------------------
TEST(SimCh50901, StrEscTab) {
  // §5.9.1 Table 5-1: \t → tab character
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\t\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x09u);
}

// ---------------------------------------------------------------------------
// 3. \\ — Backslash character (0x5C)
// ---------------------------------------------------------------------------
TEST(SimCh50901, StrEscBackslash) {
  // §5.9.1 Table 5-1: \\ → \ character
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\\\\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x5Cu);
}

// ---------------------------------------------------------------------------
// 4. \" — Double-quote character (0x22)
// ---------------------------------------------------------------------------
TEST(SimCh50901, StrEscDoubleQuote) {
  // §5.9.1 Table 5-1: \" → " character
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\\"\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x22u);
}

// ---------------------------------------------------------------------------
// 5. \v — Vertical tab (0x0B)
// ---------------------------------------------------------------------------
TEST(SimCh50901, StrEscVerticalTab) {
  // §5.9.1 Table 5-1: \v → vertical tab
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\v\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x0Bu);
}

// ---------------------------------------------------------------------------
// 6. \f — Form feed (0x0C)
// ---------------------------------------------------------------------------
TEST(SimCh50901, StrEscFormFeed) {
  // §5.9.1 Table 5-1: \f → form feed
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\f\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x0Cu);
}

// ---------------------------------------------------------------------------
// 7. \a — Bell (0x07)
// ---------------------------------------------------------------------------
TEST(SimCh50901, StrEscBell) {
  // §5.9.1 Table 5-1: \a → bell
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\a\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x07u);
}

// ---------------------------------------------------------------------------
// 8. \ddd — Octal escape, three digits
// ---------------------------------------------------------------------------
TEST(SimCh50901, StrEscOctalThreeDigit) {
  // §5.9.1 Table 5-1: \ddd → character specified in 1-3 octal digits.
  // \101 = 65 decimal = 'A'
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\101\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x41u);
}

// ---------------------------------------------------------------------------
// 9. \ddd — Octal escape, one digit
// ---------------------------------------------------------------------------
TEST(SimCh50901, StrEscOctalOneDigit) {
  // §5.9.1: 1-digit octal.  \7 = 7 = BEL.
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\7\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x07u);
}

// ---------------------------------------------------------------------------
// 10. \xdd — Hex escape, two digits
// ---------------------------------------------------------------------------
TEST(SimCh50901, StrEscHexTwoDigit) {
  // §5.9.1 Table 5-1: \xdd → character specified in 1-2 hex digits.
  // \x41 = 65 = 'A'
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\x41\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x41u);
}

// ---------------------------------------------------------------------------
// 11. \xd — Hex escape, one digit
// ---------------------------------------------------------------------------
TEST(SimCh50901, StrEscHexOneDigit) {
  // §5.9.1: 1-digit hex.  \xA = 10 = newline.
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\xA\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x0Au);
}

// ---------------------------------------------------------------------------
// 12. Unrecognized escape — treated as literal character
// ---------------------------------------------------------------------------
TEST(SimCh50901, StrEscUnrecognized) {
  // §5.9.1: Unrecognized escape treated as literal character. \b -> 'b' (0x62).
  auto v = RunAndGet(
      "module t;\n  byte c;\n  initial c = \"\\b\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x62u);
}

// ---------------------------------------------------------------------------
// 13. Multiple escape sequences in one string
// ---------------------------------------------------------------------------
TEST(SimCh50901, StrEscMultiple) {
  // §5.9.1: Multiple escapes in a single string: "A\nB" → 3 bytes: 0x41
  // 0x0A 0x42 → packed 24-bit value 0x410A42.
  auto v = RunAndGet(
      "module t;\n  bit [23:0] s;\n  initial s = \"A\\nB\";\nendmodule\n", "s");
  EXPECT_EQ(v, 0x410A42u);
}
