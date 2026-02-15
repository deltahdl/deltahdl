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

struct SimCh5bFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static RtlirDesign* ElaborateSrc(const std::string& src, SimCh5bFixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

static uint64_t RunAndGet(const std::string& src, const char* var_name) {
  SimCh5bFixture f;
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
// §5.6 Identifiers, keywords, and system names — simulation-level tests
//
// LRM §5.6: "An identifier is used to give an object a unique name so that
// it can be referenced. An identifier is either a simple identifier or an
// escaped identifier (see 5.6.1). A simple identifier shall be any sequence
// of letters, digits, dollar signs ($), and underscore characters (_). A
// keyword (see 5.6.2) may not be used as a user-defined identifier. The
// first character of a simple identifier shall not be a digit or $; it can
// be a letter or an underscore. Identifiers shall be case sensitive."
// ===========================================================================

// ---------------------------------------------------------------------------
// 1. Simple identifier with dollar sign ($) in name
// ---------------------------------------------------------------------------
TEST(SimCh5b, IdentifierWithDollarSign) {
  // §5.6: "A simple identifier shall be any sequence of letters, digits,
  // dollar signs ($), and underscore characters (_)."
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] n$657;\n"
      "  initial n$657 = 8'd42;\n"
      "endmodule\n",
      "n$657");
  EXPECT_EQ(result, 42u);
}

// ---------------------------------------------------------------------------
// 2. Identifier starting with underscore
// ---------------------------------------------------------------------------
TEST(SimCh5b, IdentifierStartingWithUnderscore) {
  // §5.6: "The first character of a simple identifier shall not be a digit
  // or $; it can be a letter or an underscore."
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] _bus3;\n"
      "  initial _bus3 = 8'd55;\n"
      "endmodule\n",
      "_bus3");
  EXPECT_EQ(result, 55u);
}

// ---------------------------------------------------------------------------
// 3. Identifiers are case sensitive
// ---------------------------------------------------------------------------
TEST(SimCh5b, IdentifiersCaseSensitive) {
  // §5.6: "Identifiers shall be case sensitive."
  SimCh5bFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] data, Data, DATA;\n"
      "  initial begin\n"
      "    data = 8'd10;\n"
      "    Data = 8'd20;\n"
      "    DATA = 8'd30;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* v1 = f.ctx.FindVariable("data");
  auto* v2 = f.ctx.FindVariable("Data");
  auto* v3 = f.ctx.FindVariable("DATA");
  ASSERT_NE(v1, nullptr);
  ASSERT_NE(v2, nullptr);
  ASSERT_NE(v3, nullptr);
  EXPECT_EQ(v1->value.ToUint64(), 10u);
  EXPECT_EQ(v2->value.ToUint64(), 20u);
  EXPECT_EQ(v3->value.ToUint64(), 30u);
}

// ---------------------------------------------------------------------------
// 4. Long identifier (1024 characters — the minimum required maximum)
// ---------------------------------------------------------------------------
TEST(SimCh5b, LongIdentifier1024Chars) {
  // §5.6: "Implementations may set a limit on the maximum length of
  // identifiers, but the limit shall be at least 1024 characters."
  std::string long_id(1024, 'a');
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] " +
          long_id +
          ";\n"
          "  initial " +
          long_id +
          " = 8'd77;\n"
          "endmodule\n",
      long_id.c_str());
  EXPECT_EQ(result, 77u);
}

// ---------------------------------------------------------------------------
// 5. Identifier with digits (not as first character)
// ---------------------------------------------------------------------------
TEST(SimCh5b, IdentifierWithDigits) {
  // §5.6: Simple identifiers can contain digits (not as first character).
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] abc123;\n"
      "  initial abc123 = 8'd88;\n"
      "endmodule\n",
      "abc123");
  EXPECT_EQ(result, 88u);
}

// ---------------------------------------------------------------------------
// 6. Identifier references an object by name
// ---------------------------------------------------------------------------
TEST(SimCh5b, IdentifierReferencesObject) {
  // §5.6: "An identifier is used to give an object a unique name so that
  // it can be referenced."
  SimCh5bFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] source, sink;\n"
      "  initial begin\n"
      "    source = 8'd66;\n"
      "    sink = source;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("sink");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 66u);
}

// ---------------------------------------------------------------------------
// 7. Multiple identifiers with mixed character classes
// ---------------------------------------------------------------------------
TEST(SimCh5b, IdentifierMixedCharClasses) {
  // §5.6: Identifiers use letters, digits, $, _ in combination.
  SimCh5bFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] _start, mid$dle, end_99, result;\n"
      "  initial begin\n"
      "    _start = 8'd1;\n"
      "    mid$dle = 8'd2;\n"
      "    end_99 = 8'd3;\n"
      "    result = _start + mid$dle + end_99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 6u);
}

// ===========================================================================
// §5.7.1 Integer literal constants — simulation-level tests
//
// LRM §5.7.1: Integer literal constants can be specified in decimal,
// hexadecimal, octal, or binary format. Two forms: simple decimal (digits
// 0-9, optional unary +/-) and based literal (optional size + base format
// + value). Simple decimals are signed; based are unsigned unless 's'.
// ===========================================================================

// ---------------------------------------------------------------------------
// 8. Simple decimal number
// ---------------------------------------------------------------------------
TEST(SimCh5b, SimpleDecimalNumber) {
  // §5.7.1: "The first form is a simple decimal number, which shall be
  // specified as a sequence of digits 0 through 9"
  auto result = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial x = 659;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 659u);
}

// ---------------------------------------------------------------------------
// 9. Sized binary literal constant
// ---------------------------------------------------------------------------
TEST(SimCh5b, SizedBinaryLiteral) {
  // §5.7.1: "4'b1001" — a 4-bit binary number
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 4'b1001;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 9u);
}

// ---------------------------------------------------------------------------
// 10. Sized octal literal constant
// ---------------------------------------------------------------------------
TEST(SimCh5b, SizedOctalLiteral) {
  // §5.7.1: based literal with octal base
  auto result = RunAndGet(
      "module t;\n"
      "  logic [15:0] x;\n"
      "  initial x = 12'o7460;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 07460u);
}

// ---------------------------------------------------------------------------
// 11. Sized hexadecimal literal constant
// ---------------------------------------------------------------------------
TEST(SimCh5b, SizedHexLiteral) {
  // §5.7.1: based literal with hex base
  auto result = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial x = 20'h837FF;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 0x837FFu);
}

// ---------------------------------------------------------------------------
// 12. Sized decimal literal constant
// ---------------------------------------------------------------------------
TEST(SimCh5b, SizedDecimalLiteral) {
  // §5.7.1: "5 'D 3" — a 5-bit decimal number
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 5'd3;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 3u);
}

// ---------------------------------------------------------------------------
// 13. Unsized hex literal (at least 32 bits)
// ---------------------------------------------------------------------------
TEST(SimCh5b, UnsizedHexLiteral) {
  // §5.7.1: "'h 837FF" — unsized hex number
  auto result = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial x = 'h837FF;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 0x837FFu);
}

// ---------------------------------------------------------------------------
// 14. Unsized octal literal
// ---------------------------------------------------------------------------
TEST(SimCh5b, UnsizedOctalLiteral) {
  // §5.7.1: "'o7460" — unsized octal number
  auto result = RunAndGet(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial x = 'o7460;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 07460u);
}

// ---------------------------------------------------------------------------
// 15. Unary minus before size (two's complement)
// ---------------------------------------------------------------------------
TEST(SimCh5b, UnaryMinusBeforeSize) {
  // §5.7.1: "-8 'd 6" — two's complement of 6, held in 8 bits
  // equivalent to -(8'd 6) = 250 in unsigned 8-bit
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = -8'd6;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 250u);
}

// ---------------------------------------------------------------------------
// 16. Negative numbers in two's complement
// ---------------------------------------------------------------------------
TEST(SimCh5b, NegativeTwosComplement) {
  // §5.7.1: "Negative numbers shall be represented in two's-complement
  // form."
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = -1;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 255u);
}

// ---------------------------------------------------------------------------
// 17. Hex digits case insensitive
// ---------------------------------------------------------------------------
TEST(SimCh5b, HexDigitsCaseInsensitive) {
  // §5.7.1: "The hexadecimal digits a to f shall be case insensitive."
  SimCh5bFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] a, b;\n"
      "  initial begin\n"
      "    a = 16'hABcd;\n"
      "    b = 16'habCD;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(va->value.ToUint64(), vb->value.ToUint64());
  EXPECT_EQ(va->value.ToUint64(), 0xABCDu);
}

// ---------------------------------------------------------------------------
// 18. Underscore in numbers
// ---------------------------------------------------------------------------
TEST(SimCh5b, UnderscoreInNumber) {
  // §5.7.1: "The underscore character (_) shall be legal anywhere in a
  // number except as the first character."
  SimCh5bFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] a, b, c;\n"
      "  initial begin\n"
      "    a = 27_195_000;\n"
      "    b = 16'b0011_0101_0001_1111;\n"
      "    c = 32'h12ab_f001;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  auto* vc = f.ctx.FindVariable("c");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  ASSERT_NE(vc, nullptr);
  EXPECT_EQ(va->value.ToUint64(), 27195000u);
  EXPECT_EQ(vb->value.ToUint64(), 0x351Fu);
  EXPECT_EQ(vc->value.ToUint64(), 0x12ABF001u);
}

// ---------------------------------------------------------------------------
// 19. Left padding with zeros (value smaller than size)
// ---------------------------------------------------------------------------
TEST(SimCh5b, LeftPadWithZeros) {
  // §5.7.1: "If the size of the unsigned number is smaller than the size
  // specified for the literal constant, the unsigned number shall be
  // padded to the left with zeros."
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'hF;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 0x0Fu);
}

// ---------------------------------------------------------------------------
// 20. Truncation from left (value larger than size)
// ---------------------------------------------------------------------------
TEST(SimCh5b, TruncationFromLeft) {
  // §5.7.1: "If the size of the unsigned number is larger than the size
  // specified for the literal constant, the unsigned number shall be
  // truncated from the left."
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 4'b11001;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 0x09u);
}

// ---------------------------------------------------------------------------
// 21. X value in hex literal
// ---------------------------------------------------------------------------
TEST(SimCh5b, XValueInHexLiteral) {
  // §5.7.1: "An x represents the unknown value... An x shall set 4 bits
  // to unknown in the hexadecimal base"
  SimCh5bFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [11:0] x;\n"
      "  initial x = 12'hx;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_NE(var->value.words[0].bval, 0u);
}

// ---------------------------------------------------------------------------
// 22. Z value in hex literal
// ---------------------------------------------------------------------------
TEST(SimCh5b, ZValueInHexLiteral) {
  // §5.7.1: "A z represents the high-impedance value... a z shall set
  // 4 bits... to the high-impedance value."
  SimCh5bFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] x;\n"
      "  initial x = 16'hz;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  // z encoding: aval=0, bval=1 per bit; left-padded to full width.
  uint16_t mask = 0xFFFF;
  EXPECT_EQ(var->value.words[0].aval & mask, 0u);
  EXPECT_EQ(var->value.words[0].bval & mask, mask);
}

// ---------------------------------------------------------------------------
// 23. X in binary literal (1 bit)
// ---------------------------------------------------------------------------
TEST(SimCh5b, XInBinaryLiteral) {
  // §5.7.1: x sets "1 bit in the binary base"
  SimCh5bFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [2:0] x;\n"
      "  initial x = 3'b01x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  // x encoding: aval=1, bval=1 per bit.
  EXPECT_EQ(var->value.words[0].aval & 0x7, 0b011u);
  EXPECT_EQ(var->value.words[0].bval & 0x7, 0b001u);
}

// ---------------------------------------------------------------------------
// 24. Question mark as z alternative
// ---------------------------------------------------------------------------
TEST(SimCh5b, QuestionMarkAsZ) {
  // §5.7.1: "the question mark (?) character is a SystemVerilog
  // alternative for the z character"
  SimCh5bFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  initial begin\n"
      "    a = 4'b1?0?;\n"
      "    b = 4'b1z0z;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(va->value.words[0].aval & 0xF, vb->value.words[0].aval & 0xF);
  EXPECT_EQ(va->value.words[0].bval & 0xF, vb->value.words[0].bval & 0xF);
}

// ---------------------------------------------------------------------------
// 25. Unbased unsized literal '0 and '1
// ---------------------------------------------------------------------------
TEST(SimCh5b, UnbasedUnsizedLiteral01) {
  // §5.7.1: "'0, '1... All bits of the unsized value shall be set to
  // the value of the specified bit."
  SimCh5bFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] a, b;\n"
      "  initial begin\n"
      "    a = '0;\n"
      "    b = '1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(va->value.ToUint64(), 0u);
  EXPECT_EQ(vb->value.ToUint64(), 0xFFFFu);
}

// ---------------------------------------------------------------------------
// 26. Unbased unsized literal 'x and 'z
// ---------------------------------------------------------------------------
TEST(SimCh5b, UnbasedUnsizedLiteralXZ) {
  // §5.7.1: "'X, 'x, 'Z, 'z" set all bits to x or z
  SimCh5bFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [15:0] a, b;\n"
      "  initial begin\n"
      "    a = 'x;\n"
      "    b = 'z;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  // x: aval=1, bval=1; z: aval=0, bval=1. All bits filled.
  uint16_t mask = 0xFFFF;
  EXPECT_EQ(va->value.words[0].aval & mask, mask);
  EXPECT_EQ(va->value.words[0].bval & mask, mask);
  EXPECT_EQ(vb->value.words[0].aval & mask, 0u);
  EXPECT_EQ(vb->value.words[0].bval & mask, mask);
}

// ---------------------------------------------------------------------------
// 27. Left padding with x when leftmost bit is x
// ---------------------------------------------------------------------------
TEST(SimCh5b, LeftPadWithX) {
  // §5.7.1: "If the leftmost bit in the unsigned number is an x...
  // then an x... shall be used to pad to the left"
  SimCh5bFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [11:0] x;\n"
      "  initial x = 'hx;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  // x encoding: aval=1, bval=1 per bit; left-padded to full width.
  uint16_t mask = 0xFFF;
  EXPECT_EQ(var->value.words[0].aval & mask, mask);
  EXPECT_EQ(var->value.words[0].bval & mask, mask);
}

// ---------------------------------------------------------------------------
// 28. Left padding with z when leftmost bit is z
// ---------------------------------------------------------------------------
TEST(SimCh5b, LeftPadWithZ) {
  // §5.7.1: "...or a z, then... a z shall be used to pad to the left"
  SimCh5bFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [11:0] x;\n"
      "  initial x = 'hz;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  // z encoding: aval=0, bval=1 per bit; left-padded to full width.
  uint16_t mask = 0xFFF;
  EXPECT_EQ(var->value.words[0].aval & mask, 0u);
  EXPECT_EQ(var->value.words[0].bval & mask, mask);
}

// ---------------------------------------------------------------------------
// 29. Signed based literal with 's' designator
// ---------------------------------------------------------------------------
TEST(SimCh5b, SignedBasedLiteral) {
  // §5.7.1: "4 'shf" — 4'b1111, interpreted as signed = -1.
  // "This is equivalent to -4'h 1"
  auto result = RunAndGet(
      "module t;\n"
      "  integer x;\n"
      "  initial x = 4'shf;\n"
      "endmodule\n",
      "x");
  uint32_t mask = 0xFFFFFFFF;
  EXPECT_EQ(result & mask, mask);
}

// ---------------------------------------------------------------------------
// 30. Signed designator does not affect bit pattern
// ---------------------------------------------------------------------------
TEST(SimCh5b, SignedDesignatorBitPattern) {
  // §5.7.1: "The s designator does not affect the bit pattern specified,
  // only its interpretation."
  SimCh5bFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  initial begin\n"
      "    a = 4'hf;\n"
      "    b = 4'shf;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(va->value.words[0].aval & 0xF, 0xFu);
  EXPECT_EQ(vb->value.words[0].aval & 0xF, 0xFu);
  EXPECT_EQ(va->value.words[0].aval, vb->value.words[0].aval);
}

// ---------------------------------------------------------------------------
// 31. X and z case insensitive in values
// ---------------------------------------------------------------------------
TEST(SimCh5b, XZCaseInsensitive) {
  // §5.7.1: "The use of x and z in defining the value of a number is
  // case insensitive."
  SimCh5bFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [3:0] a, b;\n"
      "  initial begin\n"
      "    a = 4'bx01x;\n"
      "    b = 4'bX01X;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  EXPECT_EQ(va->value.words[0].aval & 0xF, vb->value.words[0].aval & 0xF);
  EXPECT_EQ(va->value.words[0].bval & 0xF, vb->value.words[0].bval & 0xF);
}

// ---------------------------------------------------------------------------
// 32. X in octal literal (sets 3 bits)
// ---------------------------------------------------------------------------
TEST(SimCh5b, XInOctalLiteral) {
  // §5.7.1: x sets "3 bits in the octal base"
  SimCh5bFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [5:0] x;\n"
      "  initial x = 6'o7x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval & 0x38, 0x38u);
  EXPECT_EQ(var->value.words[0].bval & 0x07, 0x07u);
}

// ---------------------------------------------------------------------------
// 33. Base format case insensitive
// ---------------------------------------------------------------------------
TEST(SimCh5b, BaseFormatCaseInsensitive) {
  // §5.7.1: "a case insensitive letter specifying the base"
  SimCh5bFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, c, d;\n"
      "  initial begin\n"
      "    a = 8'hFF;\n"
      "    b = 8'HFF;\n"
      "    c = 8'b11111111;\n"
      "    d = 8'B11111111;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* va = f.ctx.FindVariable("a");
  auto* vb = f.ctx.FindVariable("b");
  auto* vc = f.ctx.FindVariable("c");
  auto* vd = f.ctx.FindVariable("d");
  ASSERT_NE(va, nullptr);
  ASSERT_NE(vb, nullptr);
  ASSERT_NE(vc, nullptr);
  ASSERT_NE(vd, nullptr);
  EXPECT_EQ(va->value.ToUint64(), 0xFFu);
  EXPECT_EQ(vb->value.ToUint64(), 0xFFu);
  EXPECT_EQ(vc->value.ToUint64(), 0xFFu);
  EXPECT_EQ(vd->value.ToUint64(), 0xFFu);
}

// ---------------------------------------------------------------------------
// 34. White space between size and base format
// ---------------------------------------------------------------------------
TEST(SimCh5b, WhiteSpaceSizeAndBase) {
  // §5.7.1: "5 'D 3" — white space allowed between tokens
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 5 'd 3;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 3u);
}

// ---------------------------------------------------------------------------
// 35. Left padding: known value (0x3x → yields 03x)
// ---------------------------------------------------------------------------
TEST(SimCh5b, LeftPadKnownHex) {
  // §5.7.1 Example 4: "b = 'h 3x; // yields 03x"
  SimCh5bFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [11:0] x;\n"
      "  initial x = 'h3x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  // x: aval=1, bval=1. Lower nibble = x, middle = 3, upper = 0-pad.
  EXPECT_EQ(var->value.words[0].aval & 0xFFF, 0x03Fu);
  EXPECT_EQ(var->value.words[0].bval & 0x00F, 0x00Fu);
  EXPECT_EQ(var->value.words[0].bval & 0xF00, 0x000u);
}

// ---------------------------------------------------------------------------
// 36. Decimal single-digit x
// ---------------------------------------------------------------------------
TEST(SimCh5b, DecimalSingleDigitX) {
  // §5.7.1: "In a decimal literal constant, the unsigned number token
  // shall not contain any x, z, or ? digits, unless there is exactly
  // one digit in the token"
  SimCh5bFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'dx;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  uint8_t mask = 0xFF;
  EXPECT_EQ(var->value.words[0].bval & mask, mask);
}

// ---------------------------------------------------------------------------
// 37. Size constant must be nonzero
// ---------------------------------------------------------------------------
TEST(SimCh5b, SizeConstantNonzero) {
  // §5.7.1: "It shall be specified as a nonzero unsigned decimal number."
  // Using size=1 (the smallest legal size) verifies nonzero is accepted.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 1'b1;\n"
      "endmodule\n",
      "x");
  EXPECT_EQ(result, 1u);
}
