#include <cstdint>
#include <cstring>
#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

static std::string ElemChar(SimFixture& f, const std::string& name) {
  auto* v = f.ctx.FindVariable(name);
  if (!v) return "";
  auto val = static_cast<char>(v->value.ToUint64() & 0xFF);
  return std::string(1, val);
}

TEST(LexicalConventionSim, SingleCharValue) {
  auto v =
      RunAndGet("module t;\n  byte c;\n  initial c = \"A\";\nendmodule\n", "c");
  EXPECT_EQ(v, 0x41u);
}

TEST(LexicalConventionSim, MultiCharValue) {
  auto v = RunAndGet(
      "module t;\n  bit [23:0] s;\n  initial s = \"ABC\";\nendmodule\n", "s");
  EXPECT_EQ(v, 0x414243u);
}

TEST(LexicalConventionSim, ZeroPadLeft) {
  auto v = RunAndGet(
      "module t;\n  bit [15:0] s;\n  initial s = \"A\";\nendmodule\n", "s");
  EXPECT_EQ(v, 0x0041u);
}

TEST(LexicalConventionSim, TruncateLeft) {
  auto v = RunAndGet(
      "module t;\n  byte s;\n  initial s = \"ABCD\";\nendmodule\n", "s");
  EXPECT_EQ(v, 0x44u);
}

TEST(LexicalConventionSim, TripleQuotedBasic) {
  auto v = RunAndGet(
      "module t;\n  bit [15:0] s;\n"
      "  initial s = \"\"\"AB\"\"\";\nendmodule\n",
      "s");
  EXPECT_EQ(v, 0x4142u);
}

TEST(LexicalConventionSim, TripleQuotedNewline) {
  auto v = RunAndGet(
      "module t;\n  bit [23:0] s;\n"
      "  initial s = \"\"\"A\nB\"\"\";\nendmodule\n",
      "s");
  EXPECT_EQ(v, 0x410A42u);
}

TEST(LexicalConventionSim, TripleQuotedEmbeddedQuote) {
  auto v = RunAndGet(
      "module t;\n  bit [23:0] s;\n"
      "  initial s = \"\"\"A\"B\"\"\";\nendmodule\n",
      "s");
  EXPECT_EQ(v, 0x412242u);
}

TEST(LexicalConventionSim, LineContinuation) {
  auto v = RunAndGet(
      "module t;\n  bit [31:0] s;\n"
      "  initial s = \"AB\\\nCD\";\nendmodule\n",
      "s");
  EXPECT_EQ(v, 0x41424344u);
}

TEST(LexicalConventionSim, DoubleBackslashNewline) {
  auto v = RunAndGet(
      "module t;\n  bit [23:0] s;\n"
      "  initial s = \"A\\\\\\\nB\";\nendmodule\n",
      "s");
  EXPECT_EQ(v, 0x415C42u);
}

TEST(LexicalConventionSim, TripleQuotedLineContinuation) {
  auto v = RunAndGet(
      "module t;\n  bit [31:0] s;\n"
      "  initial s = \"\"\"AB\\\nCD\"\"\";\nendmodule\n",
      "s");
  EXPECT_EQ(v, 0x41424344u);
}

TEST(LexicalConventionSim, LongStringNoLimit) {
  auto v = RunAndGet(
      "module t;\n  bit [63:0] s;\n"
      "  initial s = \"ABCDEFGH\";\nendmodule\n",
      "s");
  EXPECT_EQ(v, 0x4142434445464748u);
}

TEST(LexicalConventionSim, UnpackedByteArrayLeftJustifiedFirst) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte c3 [0:12] = \"hello world\\n\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(ElemChar(f, "c3[0]"), "h");
}

TEST(LexicalConventionSim, UnpackedByteArrayLeftJustifiedLast) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte c3 [0:12] = \"hello world\\n\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_EQ(ElemChar(f, "c3[11]"), "\n");
}

TEST(LexicalConventionSim, UnpackedByteArrayLeftJustifiedPadding) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte c3 [0:12] = \"hello world\\n\";\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* v = f.ctx.FindVariable("c3[12]");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 0u);
}

// §5.9: an escaped character sequence in a string literal is a single 8-bit
// ASCII value. "\n" occupies exactly one byte (0x0A), so it fits an 8-bit
// target unchanged (the bit [7:0] d = "\n" example).
TEST(LexicalConventionSim, EscapedNewlineIsSingleByte) {
  auto v = RunAndGet(
      "module t;\n  bit [7:0] d;\n  initial d = \"\\n\";\nendmodule\n", "d");
  EXPECT_EQ(v, 0x0Au);
}

// §5.9: a string literal can be cast to a packed array type, following the same
// rules as assigning it. A width-16 cast of the two-character literal packs the
// bytes exactly.
TEST(LexicalConventionSim, CastStringLiteralToPackedArrayExactWidth) {
  auto v = RunAndGet(
      "module t;\n  bit [15:0] x;\n  initial x = 16'(\"AB\");\nendmodule\n",
      "x");
  EXPECT_EQ(v, 0x4142u);
}

// §5.9: casting a string literal to a narrower packed array right justifies and
// truncates on the left, exactly as the assignment rules require.
TEST(LexicalConventionSim, CastStringLiteralToPackedArrayTruncatesLeft) {
  auto v = RunAndGet(
      "module t;\n  bit [7:0] x;\n  initial x = 8'(\"AB\");\nendmodule\n", "x");
  EXPECT_EQ(v, 0x42u);
}

// §5.9: casting a string literal to a wider packed array right justifies and
// zero-fills on the left.
TEST(LexicalConventionSim, CastStringLiteralToPackedArrayZeroFillsLeft) {
  auto v = RunAndGet(
      "module t;\n  bit [23:0] x;\n  initial x = 24'(\"AB\");\nendmodule\n",
      "x");
  EXPECT_EQ(v, 0x004142u);
}

}  // namespace
