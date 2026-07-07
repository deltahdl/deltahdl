#include <cstring>
#include <sstream>

#include "fixture_simulator.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// Runs a single-module source through elaboration and simulation while
// redirecting stdout into a string so the test can inspect what the display
// or write task actually wrote.
std::string CaptureDisplayOutput(const std::string& src, SimFixture& f) {
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  auto* design = ElaborateSrc(src, f);
  if (design != nullptr) LowerAndRun(design, f);
  std::cout.rdbuf(old_buf);
  return captured.str();
}

TEST(SubroutineCallExprSim, SystemTaskDisplay) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd10;\n"
      "    $display(\"x=%0d\", x);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}

TEST(SysTask, FormatOctal) {
  std::vector<Logic4Vec> vals;
  Arena arena;
  vals.push_back(MakeLogic4VecVal(arena, 32, 8));
  auto out = FormatDisplay("%o", vals);
  EXPECT_EQ(out, "00000000010");
}

TEST(SysTask, RealFormatExponential) {
  std::vector<Logic4Vec> vals;
  Arena arena;
  double dval = 1.5;
  uint64_t bits = 0;
  std::memcpy(&bits, &dval, sizeof(double));
  vals.push_back(MakeLogic4VecVal(arena, 64, bits));
  auto out = FormatDisplay("%e", vals);
  EXPECT_NE(out.find("1.5"), std::string::npos);
}

TEST(SysTask, RealFormatDecimal) {
  std::vector<Logic4Vec> vals;
  Arena arena;
  double dval = 2.5;
  uint64_t bits = 0;
  std::memcpy(&bits, &dval, sizeof(double));
  vals.push_back(MakeLogic4VecVal(arena, 64, bits));
  auto out = FormatDisplay("%f", vals);
  EXPECT_NE(out.find("2.5"), std::string::npos);
}

TEST(FormatArg, DecimalUnsigned) {
  Arena arena;
  auto val = MakeLogic4VecVal(arena, 8, 42);
  EXPECT_EQ(FormatArg(val, 'd'), "42");
}

// Table 21-1 spells every specifier as "%c or %C", so the uppercase form must
// behave identically to the lowercase one.
TEST(FormatArg, CharacterUppercaseMatchesLowercase) {
  Arena arena;
  auto val = MakeLogic4VecVal(arena, 8, 0x5A);
  EXPECT_EQ(FormatArg(val, 'C'), FormatArg(val, 'c'));
}

// Table 21-1: "%h or %H" -- both forms select hexadecimal display.
TEST(FormatArg, HexUppercaseMatchesLowercase) {
  Arena arena;
  auto val = MakeLogic4VecVal(arena, 16, 0xCAFE);
  EXPECT_EQ(FormatArg(val, 'H'), FormatArg(val, 'h'));
}

// Table 21-1: "%x or %X" is the alternate spelling for hexadecimal display.
TEST(FormatArg, HexAlternateUppercaseMatchesLowercase) {
  Arena arena;
  auto val = MakeLogic4VecVal(arena, 16, 0xBEEF);
  EXPECT_EQ(FormatArg(val, 'X'), FormatArg(val, 'x'));
}

// Table 21-1: "%d or %D" -- both forms select decimal display.
TEST(FormatArg, DecimalUppercaseMatchesLowercase) {
  Arena arena;
  auto val = MakeLogic4VecVal(arena, 16, 1234);
  EXPECT_EQ(FormatArg(val, 'D'), FormatArg(val, 'd'));
}

// Table 21-1: "%o or %O" -- both forms select octal display.
TEST(FormatArg, OctalUppercaseMatchesLowercase) {
  Arena arena;
  auto val = MakeLogic4VecVal(arena, 16, 0123);
  EXPECT_EQ(FormatArg(val, 'O'), FormatArg(val, 'o'));
}

// Table 21-1: "%b or %B" -- both forms select binary display.
TEST(FormatArg, BinaryUppercaseMatchesLowercase) {
  Arena arena;
  auto val = MakeLogic4VecVal(arena, 8, 0b10110100);
  EXPECT_EQ(FormatArg(val, 'B'), FormatArg(val, 'b'));
}

// Table 21-2: "%e or %E" -- exponential form for reals, case insensitive.
TEST(FormatArg, RealExponentialUppercaseMatchesLowercase) {
  Arena arena;
  double dval = 7.25;
  uint64_t bits = 0;
  std::memcpy(&bits, &dval, sizeof(double));
  auto val = MakeLogic4VecVal(arena, 64, bits);
  EXPECT_EQ(FormatArg(val, 'E'), FormatArg(val, 'e'));
}

// Table 21-2: "%f or %F" -- decimal form for reals, case insensitive.
TEST(FormatArg, RealDecimalUppercaseMatchesLowercase) {
  Arena arena;
  double dval = 3.5;
  uint64_t bits = 0;
  std::memcpy(&bits, &dval, sizeof(double));
  auto val = MakeLogic4VecVal(arena, 64, bits);
  EXPECT_EQ(FormatArg(val, 'F'), FormatArg(val, 'f'));
}

// Table 21-2: "%g or %G" -- shorter-of-the-two form for reals, case
// insensitive.
TEST(FormatArg, RealGeneralUppercaseMatchesLowercase) {
  Arena arena;
  double dval = 12.5;
  uint64_t bits = 0;
  std::memcpy(&bits, &dval, sizeof(double));
  auto val = MakeLogic4VecVal(arena, 64, bits);
  EXPECT_EQ(FormatArg(val, 'G'), FormatArg(val, 'g'));
}

// Table 21-1: %c in a format string consumes one expression argument and
// renders its low byte as an ASCII character.
TEST(SysTask, FormatCharacterInString) {
  std::vector<Logic4Vec> vals;
  Arena arena;
  vals.push_back(MakeLogic4VecVal(arena, 8, 0x42));
  auto out = FormatDisplay("%c", vals);
  EXPECT_EQ(out, "B");
}

// Table 21-2 lists "%g or %G" as the format that picks whichever of the
// decimal or exponential rendering yields the shorter printout. Exercise it
// directly with a value whose representation is obviously shorter in decimal
// than in exponential form.
TEST(SysTask, RealFormatGeneral) {
  std::vector<Logic4Vec> vals;
  Arena arena;
  double dval = 4.25;
  uint64_t bits = 0;
  std::memcpy(&bits, &dval, sizeof(double));
  vals.push_back(MakeLogic4VecVal(arena, 64, bits));
  auto out = FormatDisplay("%g", vals);
  EXPECT_NE(out.find("4.25"), std::string::npos);
}

// The %l/%L specifier is one of the three forms (with %m and %%) that this
// subclause excludes from the rule that every % must be followed by a
// matching expression argument. Calling FormatDisplay with an empty argument
// list must therefore still substitute something for the specifier rather
// than crash or leave the percent sign in the output.
TEST(SysTask, FormatLibrarySubstitutesWithoutArgument) {
  std::vector<Logic4Vec> vals;
  auto out = FormatDisplay("%l", vals);
  EXPECT_FALSE(out.empty());
  EXPECT_EQ(out.find('%'), std::string::npos);
}

// This subclause defines %l/%L as displaying the library binding using the
// "library.cell" form. The runtime currently substitutes a placeholder of
// that shape, so the rendered output must at least contain a dot separating
// the two halves of the binding.
TEST(SysTask, FormatLibraryRendersDotSeparatedBinding) {
  std::vector<Logic4Vec> vals;
  auto out = FormatDisplay("%l", vals);
  EXPECT_NE(out.find('.'), std::string::npos);
}

// Table 21-1 gives the specifier as "%l or %L", so the uppercase form must
// produce the same rendering as the lowercase one.
TEST(SysTask, FormatLibraryUppercaseMatchesLowercase) {
  std::vector<Logic4Vec> vals;
  EXPECT_EQ(FormatDisplay("%L", vals), FormatDisplay("%l", vals));
}

// The closing paragraph of this subclause states that %t cooperates with the
// $timeformat task to apply a common unit, precision, and suffix to time
// values. With a TimeFormatSpec supplied to the dispatcher, the rendered
// number must reflect the configured decimal precision and the rendered
// string must carry the configured suffix.
TEST(SysTask, FormatTimeUsesTimeformatSpec) {
  std::vector<Logic4Vec> vals;
  Arena arena;
  vals.push_back(MakeLogic4VecVal(arena, 32, 42));
  TimeFormatSpec spec;
  spec.precision_number = 2;
  spec.minimum_field_width = 1;
  spec.suffix_string = " ns";
  auto out = FormatDisplay("%t", vals, {.time_format = &spec});
  EXPECT_NE(out.find("42.00"), std::string::npos);
  EXPECT_NE(out.find(" ns"), std::string::npos);
}

// Table 21-1 lists "%t or %T". The case-fold for this specifier lives in the
// dispatcher (not in FormatArg's switch), because routing %t to
// FormatTimeUnderTimeformat happens before FormatArg is reached. This test
// observes that the dispatcher's case-fold also points %T at the timeformat
// path.
TEST(SysTask, FormatTimeUppercaseUsesTimeformatSpec) {
  std::vector<Logic4Vec> vals_lower;
  std::vector<Logic4Vec> vals_upper;
  Arena arena;
  vals_lower.push_back(MakeLogic4VecVal(arena, 32, 7));
  vals_upper.push_back(MakeLogic4VecVal(arena, 32, 7));
  TimeFormatSpec spec;
  spec.precision_number = 1;
  spec.minimum_field_width = 1;
  spec.suffix_string = " ps";
  auto lower = FormatDisplay("%t", vals_lower, {.time_format = &spec});
  auto upper = FormatDisplay("%T", vals_upper, {.time_format = &spec});
  EXPECT_EQ(lower, upper);
}

// A bare expression argument (no governing format string) takes its rendering
// from the task name; $displayb selects binary. The decimal value 5 must
// therefore appear in the output as the bit pattern 101.
TEST(SysTask, BareExpressionInDisplayBRendersAsBinary) {
  SimFixture f;
  std::string out = CaptureDisplayOutput(
      "module t;\n"
      "  integer v;\n"
      "  initial begin\n"
      "    v = 5;\n"
      "    $displayb(v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("101"), std::string::npos);
}

// $displayh selects hexadecimal for an unformatted argument. Loading the
// value 0xCAFE into a 16-bit integer and printing it via $displayh must
// produce the four hex digits in the output stream.
TEST(SysTask, BareExpressionInDisplayHRendersAsHex) {
  SimFixture f;
  std::string out = CaptureDisplayOutput(
      "module t;\n"
      "  reg [15:0] v;\n"
      "  initial begin\n"
      "    v = 16'hcafe;\n"
      "    $displayh(v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("cafe"), std::string::npos);
}

// $displayo selects octal for an unformatted argument. The value 8 is 010 in
// octal -- with leading zeros padding to the variable's width.
TEST(SysTask, BareExpressionInDisplayORendersAsOctal) {
  SimFixture f;
  std::string out = CaptureDisplayOutput(
      "module t;\n"
      "  integer v;\n"
      "  initial begin\n"
      "    v = 8;\n"
      "    $displayo(v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("10"), std::string::npos);
}

// The plain $display falls back to decimal for unformatted arguments. The
// value 42 must appear in the output as the two decimal digits "42".
TEST(SysTask, BareExpressionInDisplayRendersAsDecimal) {
  SimFixture f;
  std::string out = CaptureDisplayOutput(
      "module t;\n"
      "  integer v;\n"
      "  initial begin\n"
      "    v = 42;\n"
      "    $display(v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("42"), std::string::npos);
}

// A bare expression of `string` type renders as the character sequence the
// value carries, irrespective of the task name's default radix.
TEST(SysTask, BareStringExpressionRendersAsCharacterSequence) {
  SimFixture f;
  std::string out = CaptureDisplayOutput(
      "module t;\n"
      "  string s;\n"
      "  initial begin\n"
      "    s = \"hello\";\n"
      "    $display(s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("hello"), std::string::npos);
}

// A format specifier that is not defined in Table 21-1 or Table 21-2 is a
// misuse of the format string. The runtime must not silently render the
// value with a fallback radix; instead the unrecognized specifier surfaces
// in the output so the misuse is visible.
TEST(FormatArg, UnknownSpecifierSurfacesAsLiteralPercent) {
  Arena arena;
  auto val = MakeLogic4VecVal(arena, 8, 0);
  auto out = FormatArg(val, 'q');
  EXPECT_NE(out.find('%'), std::string::npos);
}

// §21.2.1.1: %u transfers the 2-value binary representation of the value as raw
// bytes, packed into 32-bit words with the LSB word first in native (little-
// endian) byte order. A one-byte-wide known value therefore occupies the low
// byte of a single 32-bit word, the remaining three bytes being zero.
TEST(FormatArg, UnformattedTwoValueEmitsLittleEndianWord) {
  Arena arena;
  auto val = MakeLogic4VecVal(arena, 8, 0xA5);
  auto out = FormatArg(val, 'u');
  ASSERT_EQ(out.size(), 4u);
  EXPECT_EQ(static_cast<unsigned char>(out[0]), 0xA5u);
  EXPECT_EQ(static_cast<unsigned char>(out[1]), 0x00u);
  EXPECT_EQ(static_cast<unsigned char>(out[2]), 0x00u);
  EXPECT_EQ(static_cast<unsigned char>(out[3]), 0x00u);
}

// §21.2.1.1: for %u, any unknown or high-impedance bit in the source shall be
// treated as zero. Bit 0 is z and bit 1 is x here, so only the known 1 at bit
// 2 survives into the 2-value word (0b0100 == 0x4).
TEST(FormatArg, UnformattedTwoValueTreatsXZAsZero) {
  Arena arena;
  auto val = MakeLogic4Vec(arena, 4);
  val.words[0].aval = 0x6;  // bit1 (x) and bit2 (1)
  val.words[0].bval = 0x3;  // bit0 (z) and bit1 (x) are unknown/high-Z
  auto out = FormatArg(val, 'u');
  ASSERT_EQ(out.size(), 4u);
  EXPECT_EQ(static_cast<unsigned char>(out[0]), 0x4u);
}

// §21.2.1.1: %z preserves x and z by emitting, per 32-bit chunk, the
// (aval, bval) pair. For the same value the aval word carries the driven bits
// and the bval word marks the unknown/high-Z positions -- unlike %u, which
// collapses them to zero.
TEST(FormatArg, UnformattedFourValuePreservesXZ) {
  Arena arena;
  auto val = MakeLogic4Vec(arena, 4);
  val.words[0].aval = 0x6;
  val.words[0].bval = 0x3;
  auto out = FormatArg(val, 'z');
  ASSERT_EQ(out.size(), 8u);
  EXPECT_EQ(static_cast<unsigned char>(out[0]), 0x6u);  // aval, LSB word first
  EXPECT_EQ(static_cast<unsigned char>(out[4]), 0x3u);  // bval follows
  // The four-value form differs from the two-value form for the same value.
  EXPECT_NE(FormatArg(val, 'z'), FormatArg(val, 'u'));
}

// Table 21-1 gives "%u or %U" and "%z or %Z"; the uppercase spellings must
// render identically to the lowercase ones.
TEST(FormatArg, UnformattedUppercaseMatchesLowercase) {
  Arena arena;
  auto val = MakeLogic4VecVal(arena, 16, 0xBEEF);
  EXPECT_EQ(FormatArg(val, 'U'), FormatArg(val, 'u'));
  EXPECT_EQ(FormatArg(val, 'Z'), FormatArg(val, 'z'));
}

// §21.2.1.1 end-to-end: a 4-bit value carrying x and z bits, written with %u,
// drives the "unknown/high-Z become zero" rule through the full pipeline. The
// literal 4'b01xz has bit2 == 1 as its only known set bit, so the single raw
// byte written to the output stream is 0x04.
TEST(SysTask, UnformattedTwoValueZeroesXZFromSource) {
  SimFixture f;
  std::string out = CaptureDisplayOutput(
      "module t;\n"
      "  logic [3:0] r;\n"
      "  initial begin\n"
      "    r = 4'b01xz;\n"
      "    $write(\"%u\", r);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_EQ(out.size(), 4u);
  EXPECT_EQ(static_cast<unsigned char>(out[0]), 0x4u);
  EXPECT_EQ(static_cast<unsigned char>(out[1]), 0x0u);
}

// §21.2.1.1: the Table 21-2 real specifiers carry the full C-language
// formatting capability. The subclause gives "%10.3g" as an example -- a
// minimum field width of 10 with 3 significant digits. The rendered value 3.14
// occupies four columns, so it is right-justified behind six leading spaces.
TEST(SysTask, RealFormatWidthAndPrecisionG) {
  std::vector<Logic4Vec> vals;
  Arena arena;
  double dval = 3.14159;
  uint64_t bits = 0;
  std::memcpy(&bits, &dval, sizeof(double));
  vals.push_back(MakeLogic4VecVal(arena, 64, bits));
  auto out = FormatDisplay("%10.3g", vals);
  ASSERT_EQ(out.size(), 10u);
  EXPECT_EQ(out.substr(6), "3.14");
  EXPECT_EQ(out[0], ' ');
}

// §21.2.1.1: a precision with no field width (e.g. "%.3f") fixes the number of
// fractional digits without imposing a minimum column count. 3.14159 rounded to
// three fractional digits is 3.142.
TEST(SysTask, RealFormatPrecisionOnlyF) {
  std::vector<Logic4Vec> vals;
  Arena arena;
  double dval = 3.14159;
  uint64_t bits = 0;
  std::memcpy(&bits, &dval, sizeof(double));
  vals.push_back(MakeLogic4VecVal(arena, 64, bits));
  auto out = FormatDisplay("%.3f", vals);
  EXPECT_EQ(out, "3.142");
}

// §21.2.1.1 end-to-end: a real variable declared and assigned in source, then
// displayed with a precision-bearing real specifier, must render with that
// precision through the full pipeline. 3.14159 under %.2f rounds to 3.14.
TEST(SysTask, RealFormatPrecisionFromSource) {
  SimFixture f;
  std::string out = CaptureDisplayOutput(
      "module t;\n"
      "  real r;\n"
      "  initial begin\n"
      "    r = 3.14159;\n"
      "    $display(\"%.2f\", r);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("3.14"), std::string::npos);
}

// §21.2.1.1: each '%' specifier (other than the no-argument %m/%l/%% forms) is
// filled by the expression that follows it, and the specifiers are filled in
// the order they appear. Two decimal specifiers therefore consume the two
// following values left to right. This ordered-consumption behaviour lives
// entirely in the format-string dispatcher and does not depend on how the
// values were produced, so a direct FormatDisplay call observes it.
TEST(SysTask, EachSpecifierConsumesFollowingArgumentInOrder) {
  std::vector<Logic4Vec> vals;
  Arena arena;
  vals.push_back(MakeLogic4VecVal(arena, 8, 3));
  vals.push_back(MakeLogic4VecVal(arena, 8, 7));
  auto out = FormatDisplay("%0d %0d", vals);
  EXPECT_EQ(out, "3 7");
}

// §21.2.1.1: the write family shares the default-radix rule with the display
// family -- an unformatted argument to $writeh is rendered in hexadecimal, the
// same as $displayh, but without the trailing newline. Driving it from source
// observes that the task-name-derived radix is applied by the runtime.
TEST(SysTask, BareExpressionInWriteHRendersAsHex) {
  SimFixture f;
  std::string out = CaptureDisplayOutput(
      "module t;\n"
      "  reg [15:0] v;\n"
      "  initial begin\n"
      "    v = 16'hbeef;\n"
      "    $writeh(v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("beef"), std::string::npos);
  // $write-family tasks add no newline, unlike the $display family.
  EXPECT_EQ(out.find('\n'), std::string::npos);
}

// §21.2.1.1: the integer specifiers may be used with an enumerated type, which
// is one of the integral types the rule admits. The enum constant BLUE has
// ordinal 2, so rendering it with %0d yields "2". Built from real enum source
// so the value reaches the formatter exactly as an enum expression produces it.
TEST(SysTask, IntegerSpecifierRendersEnumValue) {
  SimFixture f;
  std::string out = CaptureDisplayOutput(
      "module t;\n"
      "  typedef enum logic [1:0] {RED, GREEN, BLUE} color_t;\n"
      "  color_t c;\n"
      "  initial begin\n"
      "    c = BLUE;\n"
      "    $display(\"%0d\", c);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("2"), std::string::npos);
}

// §21.2.1.1: the integer specifiers may be used with a packed aggregate. A
// packed struct is a single integral value formed by concatenating its members
// (the first member is most significant), so {a=0xAA, b=0xBB} renders under %h
// as the 16-bit value aabb. Built from real packed-struct source.
TEST(SysTask, IntegerSpecifierRendersPackedStruct) {
  SimFixture f;
  std::string out = CaptureDisplayOutput(
      "module t;\n"
      "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
      "  ab_t s;\n"
      "  initial begin\n"
      "    s.a = 8'hAA;\n"
      "    s.b = 8'hBB;\n"
      "    $display(\"%h\", s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("aabb"), std::string::npos);
}

// §21.2.1.1: the integer specifiers may also be used with a user-defined type
// built (via typedef) from one of the integral base types. A typedef of an
// 8-bit vector holding 42 renders under %0d as "42". Built from real typedef
// source so the formatter sees the value as the typedef produces it.
TEST(SysTask, IntegerSpecifierRendersTypedefIntegral) {
  SimFixture f;
  std::string out = CaptureDisplayOutput(
      "module t;\n"
      "  typedef logic [7:0] byte_t;\n"
      "  byte_t v;\n"
      "  initial begin\n"
      "    v = 8'd42;\n"
      "    $display(\"%0d\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("42"), std::string::npos);
}

// §21.2.1.1 end-to-end (dependency §20.4.3): the %t specifier renders a time
// value through whatever configuration the most recent $timeformat installed.
// Driving a real $timeformat call and then a $display("%t", ...) observes this
// subclause's %t rule consuming the §20.4.3-produced configuration: the value 7
// prints with the configured two fractional digits and the " ns" suffix, rather
// than as the bare integer it would be without the timeformat wiring.
TEST(SysTask, TimeSpecifierAppliesTimeformatFromSource) {
  SimFixture f;
  std::string out = CaptureDisplayOutput(
      "module t;\n"
      "  initial begin\n"
      "    $timeformat(-9, 2, \" ns\", 6);\n"
      "    $display(\"%t\", 7);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("7.00"), std::string::npos);
  EXPECT_NE(out.find("ns"), std::string::npos);
}

// §21.2.1.1: a bare argument (no governing format specifier) that is an
// unpacked array of byte is rendered as the character string its element bytes
// spell. The ASCII codes for h, e, l, l, o are loaded into a five-element byte
// array from source, and $display prints them as "hello". Built and driven
// through the full pipeline so the array is produced exactly as its declaration
// and element assignments make it.
TEST(SysTask, BareUnpackedByteArrayRendersAsCharacterString) {
  SimFixture f;
  std::string out = CaptureDisplayOutput(
      "module t;\n"
      "  byte s[0:4];\n"
      "  initial begin\n"
      "    s[0] = 8'd104; s[1] = 8'd101; s[2] = 8'd108;\n"
      "    s[3] = 8'd108; s[4] = 8'd111;\n"
      "    $display(s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("hello"), std::string::npos);
}

// §21.2.1.1: a bare argument of any other unpacked data type -- here an
// unpacked array of int -- has no unformatted character-string rendering and is
// illegal. The source elaborates cleanly; the violation is caught when the
// display task runs, so the run records a diagnostic error and renders no value
// for it.
TEST(SysTask, BareUnpackedNonByteArrayIsIllegal) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int arr[0:2];\n"
      "  initial begin\n"
      "    arr[0] = 1; arr[1] = 2; arr[2] = 3;\n"
      "    $display(arr);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);  // the declaration and assignments are legal
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  LowerAndRun(design, f);
  std::cout.rdbuf(old_buf);
  EXPECT_TRUE(f.diag.HasErrors());  // the illegal display is reported at run
  // No numeric value is emitted for the rejected argument.
  EXPECT_EQ(captured.str().find('2'), std::string::npos);
}

// §21.2.1.1: the integer format specifiers shall not be applied to an unpacked
// aggregate. Passing an unpacked array of int to %d is therefore illegal -- the
// declaration and assignments elaborate cleanly, and the violation is reported
// when the display task runs. Built from real declaration + %d format-string
// source and driven through the full pipeline.
TEST(SysTask, IntegerSpecifierOnUnpackedArrayIsIllegal) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int arr[0:2];\n"
      "  initial begin\n"
      "    arr[0] = 1; arr[1] = 2; arr[2] = 3;\n"
      "    $display(\"%d\", arr);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);  // the declaration and assignments are legal
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  LowerAndRun(design, f);
  std::cout.rdbuf(old_buf);
  EXPECT_TRUE(f.diag.HasErrors());  // the %d-on-unpacked-array use is rejected
}

}  // namespace
