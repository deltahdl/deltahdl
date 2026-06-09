#include <cstdio>
#include <fstream>

#include "builders_systask.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

// §21.3.4.3: a successful conversion stores the converted field and counts as
// one matched item.
TEST(ReadFormattedTest, SscanfDecimal) {
  SimFixture f;
  auto* dest = f.ctx.CreateVariable("scanned", 32);
  dest->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* expr = MkSysCall(
      f.arena, "$sscanf",
      {MkStr(f.arena, "42"), MkStr(f.arena, "%d"), MkId(f.arena, "scanned")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
  EXPECT_EQ(dest->value.ToUint64(), 42u);
}

// §21.3.4.3: when the destination is narrower than the converted value, the
// least significant bits are transferred.
TEST(ReadFormattedTest, SscanfTransfersLeastSignificantBits) {
  SimFixture f;
  auto* dest = f.ctx.CreateVariable("narrow", 8);
  dest->value = MakeLogic4VecVal(f.arena, 8, 0);

  auto* expr = MkSysCall(
      f.arena, "$sscanf",
      {MkStr(f.arena, "511"), MkStr(f.arena, "%d"), MkId(f.arena, "narrow")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 1u);
  EXPECT_EQ(dest->value.ToUint64(), 511u & 0xFFu);  // 255, low 8 bits of 511
}

// §21.3.4.3: once the control string is exhausted, any remaining arguments are
// left untouched.
TEST(ReadFormattedTest, SscanfIgnoresExcessArguments) {
  SimFixture f;
  auto* a = f.ctx.CreateVariable("a", 32);
  a->value = MakeLogic4VecVal(f.arena, 32, 0);
  auto* b = f.ctx.CreateVariable("b", 32);
  b->value = MakeLogic4VecVal(f.arena, 32, 7);  // sentinel; must stay

  auto* expr =
      MkSysCall(f.arena, "$sscanf",
                {MkStr(f.arena, "3"), MkStr(f.arena, "%d"), MkId(f.arena, "a"),
                 MkId(f.arena, "b")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 1u);
  EXPECT_EQ(a->value.ToUint64(), 3u);
  EXPECT_EQ(b->value.ToUint64(), 7u);  // excess argument untouched
}

// §21.3.4.3: $fscanf reads formatted fields from the file descriptor and
// returns the number of successfully matched and assigned items.
TEST(ReadFormattedTest, FscanfReadsFormattedFromDescriptor) {
  SimFixture f;
  std::string tmp = "/tmp/deltahdl_test_fscanf_ok.txt";
  {
    std::ofstream ofs(tmp);
    ofs << "42 ff";
  }
  auto fd = EvalExpr(MkSysCall(f.arena, "$fopen",
                               {MkStr(f.arena, tmp), MkStr(f.arena, "r")}),
                     f.ctx, f.arena)
                .ToUint64();

  auto* d = f.ctx.CreateVariable("d", 32);
  d->value = MakeLogic4VecVal(f.arena, 32, 0);
  auto* h = f.ctx.CreateVariable("h", 32);
  h->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* expr = MkSysCall(
      f.arena, "$fscanf",
      {MkInt(f.arena, fd), MkStr(f.arena, "%d %h"), MkId(f.arena, "d"),
       MkId(f.arena, "h")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 2u);
  EXPECT_EQ(d->value.ToUint64(), 42u);
  EXPECT_EQ(h->value.ToUint64(), 0xFFu);

  EvalExpr(MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd)}), f.ctx, f.arena);
  std::remove(tmp.c_str());
}

// §21.3.4.3: an unknown bit (x or z) in the str argument of $sscanf forces an
// EOF (-1) return.
TEST(ReadFormattedTest, SscanfReturnsEofForUnknownBitsInStr) {
  SimFixture f;
  auto* src = f.ctx.CreateVariable("src", 8);
  src->value = MakeLogic4VecVal(f.arena, 8, 0);
  src->value.words[0].bval = 0xFF;  // all bits unknown

  auto* dest = f.ctx.CreateVariable("d", 32);
  dest->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* expr = MkSysCall(
      f.arena, "$sscanf",
      {MkId(f.arena, "src"), MkStr(f.arena, "%d"), MkId(f.arena, "d")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 0xFFFFFFFFu);
}

// §21.3.4.3: an unknown bit in the format string is likewise reported as EOF
// (-1).
TEST(ReadFormattedTest, SscanfReturnsEofForUnknownBitsInFormat) {
  SimFixture f;
  auto* fmt = f.ctx.CreateVariable("fmt", 16);
  fmt->value = MakeLogic4VecVal(f.arena, 16, 0);
  fmt->value.words[0].bval = 0x1;  // one unknown bit

  auto* dest = f.ctx.CreateVariable("d", 32);
  dest->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* expr = MkSysCall(
      f.arena, "$sscanf",
      {MkStr(f.arena, "42"), MkId(f.arena, "fmt"), MkId(f.arena, "d")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 0xFFFFFFFFu);
}

// §21.3.4.3: when the input ends before any field can be converted, EOF (-1) is
// returned.
TEST(ReadFormattedTest, SscanfReturnsEofWhenInputExhausted) {
  SimFixture f;
  auto* dest = f.ctx.CreateVariable("d", 32);
  dest->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* expr = MkSysCall(
      f.arena, "$sscanf",
      {MkStr(f.arena, ""), MkStr(f.arena, "%d"), MkId(f.arena, "d")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 0xFFFFFFFFu);
}

// §21.3.4.3: a return of zero (not EOF) distinguishes a matching failure
// against present input from an exhausted input.
TEST(ReadFormattedTest, SscanfReturnsZeroOnMatchingFailure) {
  SimFixture f;
  auto* dest = f.ctx.CreateVariable("d", 32);
  dest->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* expr = MkSysCall(
      f.arena, "$sscanf",
      {MkStr(f.arena, "abc"), MkStr(f.arena, "%d"), MkId(f.arena, "d")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 0u);
}

// §21.3.4.3: the unknown-bit rule applies equally to $fscanf's format string.
TEST(ReadFormattedTest, FscanfReturnsEofForUnknownBitsInFormat) {
  SimFixture f;
  std::string tmp = "/tmp/deltahdl_test_fscanf_xz.txt";
  {
    std::ofstream ofs(tmp);
    ofs << "42";
  }
  auto fd = EvalExpr(MkSysCall(f.arena, "$fopen",
                               {MkStr(f.arena, tmp), MkStr(f.arena, "r")}),
                     f.ctx, f.arena)
                .ToUint64();

  auto* fmt = f.ctx.CreateVariable("fmt", 16);
  fmt->value = MakeLogic4VecVal(f.arena, 16, 0);
  fmt->value.words[0].bval = 0x1;  // unknown bit in the format
  auto* dest = f.ctx.CreateVariable("d", 32);
  dest->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* expr = MkSysCall(
      f.arena, "$fscanf",
      {MkInt(f.arena, fd), MkId(f.arena, "fmt"), MkId(f.arena, "d")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 0xFFFFFFFFu);

  EvalExpr(MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd)}), f.ctx, f.arena);
  std::remove(tmp.c_str());
}

// §21.3.4.3: $fscanf returns EOF (-1) when the file is already at end-of-file
// so no field can be converted.
TEST(ReadFormattedTest, FscanfReturnsEofAtEndOfFile) {
  SimFixture f;
  std::string tmp = "/tmp/deltahdl_test_fscanf_empty.txt";
  { std::ofstream ofs(tmp); }  // empty file
  auto fd = EvalExpr(MkSysCall(f.arena, "$fopen",
                               {MkStr(f.arena, tmp), MkStr(f.arena, "r")}),
                     f.ctx, f.arena)
                .ToUint64();

  auto* dest = f.ctx.CreateVariable("d", 32);
  dest->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* expr = MkSysCall(
      f.arena, "$fscanf",
      {MkInt(f.arena, fd), MkStr(f.arena, "%d"), MkId(f.arena, "d")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 0xFFFFFFFFu);

  EvalExpr(MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd)}), f.ctx, f.arena);
  std::remove(tmp.c_str());
}

// §21.3.4.3: the %h specifier reads a hexadecimal field into an integral
// variable.
TEST(ReadFormattedTest, SscanfHexadecimal) {
  SimFixture f;
  auto* dest = f.ctx.CreateVariable("hv", 32);
  dest->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* expr = MkSysCall(
      f.arena, "$sscanf",
      {MkStr(f.arena, "ff"), MkStr(f.arena, "%h"), MkId(f.arena, "hv")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 1u);
  EXPECT_EQ(dest->value.ToUint64(), 0xFFu);
}

// §21.3.4.3: the %b specifier reads a binary field into an integral variable.
TEST(ReadFormattedTest, SscanfBinary) {
  SimFixture f;
  auto* dest = f.ctx.CreateVariable("bv", 32);
  dest->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* expr = MkSysCall(
      f.arena, "$sscanf",
      {MkStr(f.arena, "1010"), MkStr(f.arena, "%b"), MkId(f.arena, "bv")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 1u);
  EXPECT_EQ(dest->value.ToUint64(), 10u);
}

// §21.3.4.3: the %o specifier reads an octal field from a file descriptor into
// an integral variable.
TEST(ReadFormattedTest, FscanfOctal) {
  SimFixture f;
  std::string tmp = "/tmp/deltahdl_test_fscanf_oct.txt";
  {
    std::ofstream ofs(tmp);
    ofs << "17";  // octal 17 == 15
  }
  auto fd = EvalExpr(MkSysCall(f.arena, "$fopen",
                               {MkStr(f.arena, tmp), MkStr(f.arena, "r")}),
                     f.ctx, f.arena)
                .ToUint64();

  auto* dest = f.ctx.CreateVariable("ov", 32);
  dest->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* expr = MkSysCall(
      f.arena, "$fscanf",
      {MkInt(f.arena, fd), MkStr(f.arena, "%o"), MkId(f.arena, "ov")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 1u);
  EXPECT_EQ(dest->value.ToUint64(), 15u);

  EvalExpr(MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd)}), f.ctx, f.arena);
  std::remove(tmp.c_str());
}

// §21.3.4.3: white space preceding an input field is skipped before the field
// is converted.
TEST(ReadFormattedTest, SscanfSkipsLeadingWhitespace) {
  SimFixture f;
  auto* dest = f.ctx.CreateVariable("ws", 32);
  dest->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* expr = MkSysCall(
      f.arena, "$sscanf",
      {MkStr(f.arena, "   42"), MkStr(f.arena, "%d"), MkId(f.arena, "ws")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 1u);
  EXPECT_EQ(dest->value.ToUint64(), 42u);
}

// §21.3.4.3: each converted field is counted, so a control string with several
// conversions returns the number of fields assigned.
TEST(ReadFormattedTest, SscanfMatchesMultipleFields) {
  SimFixture f;
  auto* a = f.ctx.CreateVariable("m1", 32);
  a->value = MakeLogic4VecVal(f.arena, 32, 0);
  auto* b = f.ctx.CreateVariable("m2", 32);
  b->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* expr =
      MkSysCall(f.arena, "$sscanf",
                {MkStr(f.arena, "12 34"), MkStr(f.arena, "%d %d"),
                 MkId(f.arena, "m1"), MkId(f.arena, "m2")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 2u);
  EXPECT_EQ(a->value.ToUint64(), 12u);
  EXPECT_EQ(b->value.ToUint64(), 34u);
}

// §21.3.4.3: an ordinary character in the control string must match the next
// input character before the following conversion is attempted.
TEST(ReadFormattedTest, SscanfMatchesOrdinaryCharacters) {
  SimFixture f;
  auto* dest = f.ctx.CreateVariable("ov", 32);
  dest->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* expr = MkSysCall(
      f.arena, "$sscanf",
      {MkStr(f.arena, "a=5"), MkStr(f.arena, "a=%d"), MkId(f.arena, "ov")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 1u);
  EXPECT_EQ(dest->value.ToUint64(), 5u);
}

// §21.3.4.3: a mismatch between an ordinary control character and the input
// ends the scan with no assignment.
TEST(ReadFormattedTest, SscanfStopsOnLiteralMismatch) {
  SimFixture f;
  auto* dest = f.ctx.CreateVariable("ov", 32);
  dest->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* expr = MkSysCall(
      f.arena, "$sscanf",
      {MkStr(f.arena, "y5"), MkStr(f.arena, "x%d"), MkId(f.arena, "ov")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 0u);
  EXPECT_EQ(dest->value.ToUint64(), 0u);  // nothing assigned
}

// §21.3.4.3, Table 21-7: a %% conversion expects a literal % in the input and
// assigns nothing. Here it consumes the leading %, letting the following %d
// convert the digit -- without the %% match the %d would fail on the % instead.
TEST(ReadFormattedTest, SscanfMatchesLiteralPercent) {
  SimFixture f;
  auto* dest = f.ctx.CreateVariable("pv", 32);
  dest->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* expr = MkSysCall(
      f.arena, "$sscanf",
      {MkStr(f.arena, "%5"), MkStr(f.arena, "%%%d"), MkId(f.arena, "pv")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 1u);  // only %d assigns
  EXPECT_EQ(dest->value.ToUint64(), 5u);
}

// §21.3.4.3: the assignment-suppression character converts a field without
// consuming a destination argument.
TEST(ReadFormattedTest, SscanfSuppressesAssignment) {
  SimFixture f;
  auto* dest = f.ctx.CreateVariable("kept", 32);
  dest->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* expr =
      MkSysCall(f.arena, "$sscanf",
                {MkStr(f.arena, "3 4"), MkStr(f.arena, "%*d %d"),
                 MkId(f.arena, "kept")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 1u);  // only one assigned
  EXPECT_EQ(dest->value.ToUint64(), 4u);  // the second field, not the first
}

// §21.3.4.3: a maximum field width limits how many characters a conversion
// consumes.
TEST(ReadFormattedTest, SscanfHonorsFieldWidth) {
  SimFixture f;
  auto* dest = f.ctx.CreateVariable("wv", 32);
  dest->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* expr = MkSysCall(
      f.arena, "$sscanf",
      {MkStr(f.arena, "12345"), MkStr(f.arena, "%2d"), MkId(f.arena, "wv")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 1u);
  EXPECT_EQ(dest->value.ToUint64(), 12u);  // only first two digits
}

// §21.3.4.3: %c reads the next character and returns its 8-bit value.
TEST(ReadFormattedTest, SscanfReadsCharacter) {
  SimFixture f;
  auto* dest = f.ctx.CreateVariable("cv", 8);
  dest->value = MakeLogic4VecVal(f.arena, 8, 0);

  auto* expr = MkSysCall(
      f.arena, "$sscanf",
      {MkStr(f.arena, "Q"), MkStr(f.arena, "%c"), MkId(f.arena, "cv")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 1u);
  EXPECT_EQ(dest->value.ToUint64(), static_cast<uint64_t>('Q'));
}

// §21.3.4.3: the character conversion is the lone exception to leading
// white-space skipping -- %c takes the next input character verbatim, so a
// leading space is read as the character itself.
TEST(ReadFormattedTest, SscanfCharacterDoesNotSkipLeadingWhitespace) {
  SimFixture f;
  auto* dest = f.ctx.CreateVariable("cv", 8);
  dest->value = MakeLogic4VecVal(f.arena, 8, 0);

  auto* expr = MkSysCall(
      f.arena, "$sscanf",
      {MkStr(f.arena, " A"), MkStr(f.arena, "%c"), MkId(f.arena, "cv")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 1u);
  EXPECT_EQ(dest->value.ToUint64(), static_cast<uint64_t>(' '));  // the space
}

// §21.3.4.3: %s reads a run of nonwhitespace characters into the destination,
// leftmost character in the most significant byte.
TEST(ReadFormattedTest, SscanfReadsString) {
  SimFixture f;
  auto* dest = f.ctx.CreateVariable("sv", 16);
  dest->value = MakeLogic4VecVal(f.arena, 16, 0);

  auto* expr = MkSysCall(
      f.arena, "$sscanf",
      {MkStr(f.arena, "hi"), MkStr(f.arena, "%s"), MkId(f.arena, "sv")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 1u);
  EXPECT_EQ(dest->value.ToUint64(), 0x6869u);  // 'h'<<8 | 'i'
}

// §21.3.4.3: the floating-point conversion reads a real value into a real
// destination.
TEST(ReadFormattedTest, SscanfReadsRealNumber) {
  SimFixture f;
  auto* dest = f.ctx.CreateVariable("rv", 64);
  dest->value = MakeLogic4VecVal(f.arena, 64, 0);

  auto* expr = MkSysCall(
      f.arena, "$sscanf",
      {MkStr(f.arena, "2.5"), MkStr(f.arena, "%f"), MkId(f.arena, "rv")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 1u);
  EXPECT_DOUBLE_EQ(ResultToDouble(dest->value), 2.5);
}

// §21.3.4.3: integer conversion codes are case-insensitive (%D behaves like
// %d).
TEST(ReadFormattedTest, SscanfUppercaseSpecifier) {
  SimFixture f;
  auto* dest = f.ctx.CreateVariable("uv", 32);
  dest->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* expr = MkSysCall(
      f.arena, "$sscanf",
      {MkStr(f.arena, "42"), MkStr(f.arena, "%D"), MkId(f.arena, "uv")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 1u);
  EXPECT_EQ(dest->value.ToUint64(), 42u);
}

// §21.3.4.3: the new control-string handling applies to the $fscanf engine as
// well -- read a string field from a file descriptor.
TEST(ReadFormattedTest, FscanfReadsString) {
  SimFixture f;
  std::string tmp = "/tmp/deltahdl_test_fscanf_str.txt";
  {
    std::ofstream ofs(tmp);
    ofs << "world";
  }
  auto fd = EvalExpr(MkSysCall(f.arena, "$fopen",
                               {MkStr(f.arena, tmp), MkStr(f.arena, "r")}),
                     f.ctx, f.arena)
                .ToUint64();

  auto* dest = f.ctx.CreateVariable("sv", 64);
  dest->value = MakeLogic4VecVal(f.arena, 64, 0);

  auto* expr = MkSysCall(
      f.arena, "$fscanf",
      {MkInt(f.arena, fd), MkStr(f.arena, "%s"), MkId(f.arena, "sv")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 1u);
  EXPECT_EQ(dest->value.ToUint64(), 0x776f726c64u);  // "world"

  EvalExpr(MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd)}), f.ctx, f.arena);
  std::remove(tmp.c_str());
}

// §21.3.4.3: the str source of $sscanf need not be a literal -- it may be an
// integral expression whose packed bytes spell the text to scan. Here a 16-bit
// variable holds the characters "42", read most significant byte first.
TEST(ReadFormattedTest, SscanfReadsFromIntegralVariable) {
  SimFixture f;
  auto* src = f.ctx.CreateVariable("src", 16);
  src->value = MakeLogic4VecVal(f.arena, 16, ('4' << 8) | '2');  // "42"

  auto* dest = f.ctx.CreateVariable("d", 32);
  dest->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* expr = MkSysCall(
      f.arena, "$sscanf",
      {MkId(f.arena, "src"), MkStr(f.arena, "%d"), MkId(f.arena, "d")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 1u);
  EXPECT_EQ(dest->value.ToUint64(), 42u);
}

// §21.3.4.3: an input field reaches only as far as the next character that does
// not belong to it. A numeric field stops at the first non-numeric character,
// which a following %s then picks up.
TEST(ReadFormattedTest, SscanfNumericFieldStopsAtNonNumericCharacter) {
  SimFixture f;
  auto* num = f.ctx.CreateVariable("num", 32);
  num->value = MakeLogic4VecVal(f.arena, 32, 0);
  auto* rest = f.ctx.CreateVariable("rest", 16);
  rest->value = MakeLogic4VecVal(f.arena, 16, 0);

  auto* expr =
      MkSysCall(f.arena, "$sscanf",
                {MkStr(f.arena, "12ab"), MkStr(f.arena, "%d%s"),
                 MkId(f.arena, "num"), MkId(f.arena, "rest")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 2u);
  EXPECT_EQ(num->value.ToUint64(), 12u);          // digits only
  EXPECT_EQ(rest->value.ToUint64(), 0x6162u);     // "ab" follows
}

// §21.3.4.3: a %s field is a run of nonwhite-space characters, so it ends at the
// first space; the next %s resumes after that space.
TEST(ReadFormattedTest, SscanfStringFieldStopsAtWhitespace) {
  SimFixture f;
  auto* w1 = f.ctx.CreateVariable("w1", 16);
  w1->value = MakeLogic4VecVal(f.arena, 16, 0);
  auto* w2 = f.ctx.CreateVariable("w2", 16);
  w2->value = MakeLogic4VecVal(f.arena, 16, 0);

  auto* expr =
      MkSysCall(f.arena, "$sscanf",
                {MkStr(f.arena, "ab cd"), MkStr(f.arena, "%s %s"),
                 MkId(f.arena, "w1"), MkId(f.arena, "w2")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 2u);
  EXPECT_EQ(w1->value.ToUint64(), 0x6162u);  // "ab"
  EXPECT_EQ(w2->value.ToUint64(), 0x6364u);  // "cd"
}

// §21.3.4.3: when a conversion stops on a conflicting input character, that
// character is left unread in the stream. After $fscanf consumes "12" and halts
// at 'x', the descriptor still points at 'x', so the next read returns it.
TEST(ReadFormattedTest, FscanfLeavesConflictingCharacterUnread) {
  SimFixture f;
  std::string tmp = "/tmp/deltahdl_test_fscanf_unread.txt";
  {
    std::ofstream ofs(tmp);
    ofs << "12x";
  }
  auto fd = EvalExpr(MkSysCall(f.arena, "$fopen",
                               {MkStr(f.arena, tmp), MkStr(f.arena, "r")}),
                     f.ctx, f.arena)
                .ToUint64();

  auto* d = f.ctx.CreateVariable("d", 32);
  d->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* scan = MkSysCall(
      f.arena, "$fscanf",
      {MkInt(f.arena, fd), MkStr(f.arena, "%d"), MkId(f.arena, "d")});
  EXPECT_EQ(EvalExpr(scan, f.ctx, f.arena).ToUint64(), 1u);
  EXPECT_EQ(d->value.ToUint64(), 12u);

  auto* getc = MkSysCall(f.arena, "$fgetc", {MkInt(f.arena, fd)});
  EXPECT_EQ(EvalExpr(getc, f.ctx, f.arena).ToUint64(),
            static_cast<uint64_t>('x'));  // the unread offending character

  EvalExpr(MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd)}), f.ctx, f.arena);
  std::remove(tmp.c_str());
}

// §21.3.4.3, Table 21-7: %u transfers unformatted 2-value binary data, taking
// as many raw bytes as the destination needs. A 16-bit target pulls two bytes
// (here both 0x42, so the result is byte-order independent) and the value
// carries no x/z.
TEST(ReadFormattedTest, SscanfReadsUnformattedBinary) {
  SimFixture f;
  auto* dest = f.ctx.CreateVariable("uv", 16);
  dest->value = MakeLogic4VecVal(f.arena, 16, 0);

  auto* expr = MkSysCall(
      f.arena, "$sscanf",
      {MkStr(f.arena, "BB"), MkStr(f.arena, "%u"), MkId(f.arena, "uv")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 1u);
  EXPECT_EQ(dest->value.ToUint64(), 0x4242u);  // two raw bytes
}

// §21.3.4.3, Table 21-7: the same unformatted-binary transfer applies to the
// $fscanf engine reading raw bytes from a file descriptor.
TEST(ReadFormattedTest, FscanfReadsUnformattedBinary) {
  SimFixture f;
  std::string tmp = "/tmp/deltahdl_test_fscanf_u.txt";
  {
    std::ofstream ofs(tmp);
    ofs << "BB";
  }
  auto fd = EvalExpr(MkSysCall(f.arena, "$fopen",
                               {MkStr(f.arena, tmp), MkStr(f.arena, "r")}),
                     f.ctx, f.arena)
                .ToUint64();

  auto* dest = f.ctx.CreateVariable("uv", 16);
  dest->value = MakeLogic4VecVal(f.arena, 16, 0);

  auto* expr = MkSysCall(
      f.arena, "$fscanf",
      {MkInt(f.arena, fd), MkStr(f.arena, "%u"), MkId(f.arena, "uv")});
  EXPECT_EQ(EvalExpr(expr, f.ctx, f.arena).ToUint64(), 1u);
  EXPECT_EQ(dest->value.ToUint64(), 0x4242u);

  EvalExpr(MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd)}), f.ctx, f.arena);
  std::remove(tmp.c_str());
}

}  // namespace
