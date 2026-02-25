// Annex A.8.8: Strings

#include <gtest/gtest.h>

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

namespace {

struct SimA88Fixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign *ElaborateSrc(const std::string &src, SimA88Fixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

static uint64_t RunAndGet(const std::string &src, const char *var_name) {
  SimA88Fixture f;
  auto *design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  if (!design) return 0;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto *var = f.ctx.FindVariable(var_name);
  EXPECT_NE(var, nullptr);
  if (!var) return 0;
  return var->value.ToUint64();
}

// § quoted_string — ASCII bytes pack big-endian per §5.9
TEST(SimA88, QuotedStringPacksBigEndian) {
  // quoted_string "AB" → 2 bytes 0x41 0x42, packed into 16-bit: 0x4142
  auto v = RunAndGet(
      "module t;\n"
      "  bit [15:0] s;\n"
      "  initial s = \"AB\";\n"
      "endmodule\n",
      "s");
  EXPECT_EQ(v, 0x4142u);
}

// § triple_quoted_string — ASCII chars pack same as quoted_string
TEST(SimA88, TripleQuotedStringPacksBigEndian) {
  // triple_quoted_string """AB""" → 0x4142
  auto v = RunAndGet(
      "module t;\n"
      "  bit [15:0] s;\n"
      "  initial s = \"\"\"AB\"\"\";\n"
      "endmodule\n",
      "s");
  EXPECT_EQ(v, 0x4142u);
}

// § string_escape_seq — \any_ASCII_character: \n → 0x0A (newline)
TEST(SimA88, EscapeSeqAnyAsciiNewline) {
  auto v = RunAndGet(
      "module t;\n"
      "  byte c;\n"
      "  initial c = \"\\n\";\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x0Au);
}

// § string_escape_seq — \any_ASCII_character: \t → 0x09 (tab)
TEST(SimA88, EscapeSeqAnyAsciiTab) {
  auto v = RunAndGet(
      "module t;\n"
      "  byte c;\n"
      "  initial c = \"\\t\";\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x09u);
}

// § string_escape_seq — \any_ASCII_character: \\ → 0x5C (backslash)
TEST(SimA88, EscapeSeqAnyAsciiBackslash) {
  auto v = RunAndGet(
      "module t;\n"
      "  byte c;\n"
      "  initial c = \"\\\\\";\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x5Cu);
}

// § string_escape_seq — \any_ASCII_character: \" → 0x22 (double-quote)
TEST(SimA88, EscapeSeqAnyAsciiDoubleQuote) {
  auto v = RunAndGet(
      "module t;\n"
      "  byte c;\n"
      "  initial c = \"\\\"\";\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x22u);
}

// § string_escape_seq — \one_to_three_digit_octal_number: one digit \7 → 0x07
TEST(SimA88, EscapeSeqOctalOneDigit) {
  auto v = RunAndGet(
      "module t;\n"
      "  byte c;\n"
      "  initial c = \"\\7\";\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x07u);
}

// § string_escape_seq — \one_to_three_digit_octal_number: two digits \77 → 0x3F
TEST(SimA88, EscapeSeqOctalTwoDigits) {
  auto v = RunAndGet(
      "module t;\n"
      "  byte c;\n"
      "  initial c = \"\\77\";\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x3Fu);
}

// § string_escape_seq — \one_to_three_digit_octal_number: three digits \101 → 0x41 ('A')
TEST(SimA88, EscapeSeqOctalThreeDigits) {
  auto v = RunAndGet(
      "module t;\n"
      "  byte c;\n"
      "  initial c = \"\\101\";\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x41u);
}

// § string_escape_seq — \x one_to_two_digit_hex_number: one hex digit \xA → 0x0A
TEST(SimA88, EscapeSeqHexOneDigit) {
  auto v = RunAndGet(
      "module t;\n"
      "  byte c;\n"
      "  initial c = \"\\xA\";\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x0Au);
}

// § string_escape_seq — \x one_to_two_digit_hex_number: two hex digits \x41 → 0x41 ('A')
TEST(SimA88, EscapeSeqHexTwoDigits) {
  auto v = RunAndGet(
      "module t;\n"
      "  byte c;\n"
      "  initial c = \"\\x41\";\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x41u);
}

// § triple_quoted_string_item — newline is a literal character (0x0A in result)
TEST(SimA88, TripleQuotedStringItemNewlineIsLiteral) {
  // """A\nB""" where \n is a literal newline character in source (not escape)
  auto v = RunAndGet(
      "module t;\n"
      "  bit [23:0] s;\n"
      "  initial s = \"\"\"A\nB\"\"\";\n"
      "endmodule\n",
      "s");
  EXPECT_EQ(v, 0x410A42u);
}

// § triple_quoted_string_item — double-quote is a literal character (0x22 in result)
TEST(SimA88, TripleQuotedStringItemDoubleQuoteIsLiteral) {
  // """A"B""" where " is a literal double-quote character
  auto v = RunAndGet(
      "module t;\n"
      "  bit [23:0] s;\n"
      "  initial s = \"\"\"A\"B\"\"\";\n"
      "endmodule\n",
      "s");
  EXPECT_EQ(v, 0x412242u);
}

// § string_escape_seq in triple_quoted_string — same semantics as in quoted_string
TEST(SimA88, TripleQuotedStringEscapeSeq) {
  // """\n""" → newline (0x0A)
  auto v = RunAndGet(
      "module t;\n"
      "  byte c;\n"
      "  initial c = \"\"\"\\n\"\"\";\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x0Au);
}

// § string_escape_seq — octal in triple_quoted_string
TEST(SimA88, TripleQuotedStringEscapeSeqOctal) {
  auto v = RunAndGet(
      "module t;\n"
      "  byte c;\n"
      "  initial c = \"\"\"\\101\"\"\";\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x41u);
}

// § string_escape_seq — hex in triple_quoted_string
TEST(SimA88, TripleQuotedStringEscapeSeqHex) {
  auto v = RunAndGet(
      "module t;\n"
      "  byte c;\n"
      "  initial c = \"\"\"\\x41\"\"\";\n"
      "endmodule\n",
      "c");
  EXPECT_EQ(v, 0x41u);
}

// § quoted_string — width is 8 bits per character (§5.9)
TEST(SimA88, QuotedStringWidthPerCharacter) {
  // "ABC" → 3 chars → 24-bit value 0x414243
  auto v = RunAndGet(
      "module t;\n"
      "  bit [23:0] s;\n"
      "  initial s = \"ABC\";\n"
      "endmodule\n",
      "s");
  EXPECT_EQ(v, 0x414243u);
}

}  // namespace
