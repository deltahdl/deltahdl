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

TEST(SysTask, FormatReal_e) {
  std::vector<Logic4Vec> vals;
  Arena arena;
  double dval = 1.5;
  uint64_t bits = 0;
  std::memcpy(&bits, &dval, sizeof(double));
  vals.push_back(MakeLogic4VecVal(arena, 64, bits));
  auto out = FormatDisplay("%e", vals);
  EXPECT_NE(out.find("1.5"), std::string::npos);
}

TEST(SysTask, FormatReal_f) {
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

// Table 21-1: %c renders the low byte of the argument as a single ASCII
// character. The vector below carries the byte 0x41 (capital 'A').
TEST(FormatArg, CharacterFromLowByte) {
  Arena arena;
  auto val = MakeLogic4VecVal(arena, 8, 0x41);
  EXPECT_EQ(FormatArg(val, 'c'), "A");
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
TEST(SysTask, FormatRealGeneral_g) {
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

}  // namespace
