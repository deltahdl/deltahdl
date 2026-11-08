#include <gtest/gtest.h>

#include <cstdint>
#include <cstring>
#include <iostream>
#include <sstream>
#include <streambuf>
#include <string>
#include <vector>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

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
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd10;\n"
      "    $display(\"x=%0d\", x);\n"
      "  end\n"
      "endmodule\n",
      f, "x");
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
  vals.push_back(MakeRealVec(arena, 1.5, 64));
  auto out = FormatDisplay("%e", vals);
  EXPECT_NE(out.find("1.5"), std::string::npos);
}

TEST(SysTask, RealFormatDecimal) {
  std::vector<Logic4Vec> vals;
  Arena arena;
  vals.push_back(MakeRealVec(arena, 2.5, 64));
  auto out = FormatDisplay("%f", vals);
  EXPECT_NE(out.find("2.5"), std::string::npos);
}

TEST(DisplayFormat, RealSpecifierDecodesA32BitVectorAsSinglePrecision) {
  std::vector<Logic4Vec> vals;
  Arena arena;
  float fval = 1.5f;
  uint32_t bits = 0;
  std::memcpy(&bits, &fval, sizeof(float));
  ASSERT_EQ(bits, 0x3FC00000u);
  auto val = MakeLogic4VecVal(arena, 32, bits);
  val.is_real = true;
  vals.push_back(val);
  auto out = FormatDisplay("%f", vals);
  EXPECT_EQ(out, "1.500000");
}

TEST(FormatArg, DecimalUnsigned) {
  Arena arena;
  auto val = MakeLogic4VecVal(arena, 8, 42);
  EXPECT_EQ(FormatArg(val, 'd'), "42");
}

TEST(FormatArg, CharacterUppercaseMatchesLowercase) {
  Arena arena;
  auto val = MakeLogic4VecVal(arena, 8, 0x5A);
  EXPECT_EQ(FormatArg(val, 'C'), FormatArg(val, 'c'));
}

TEST(FormatArg, HexUppercaseMatchesLowercase) {
  Arena arena;
  auto val = MakeLogic4VecVal(arena, 16, 0xCAFE);
  EXPECT_EQ(FormatArg(val, 'H'), FormatArg(val, 'h'));
}

TEST(FormatArg, HexAlternateUppercaseMatchesLowercase) {
  Arena arena;
  auto val = MakeLogic4VecVal(arena, 16, 0xBEEF);
  EXPECT_EQ(FormatArg(val, 'X'), FormatArg(val, 'x'));
}

TEST(FormatArg, DecimalUppercaseMatchesLowercase) {
  Arena arena;
  auto val = MakeLogic4VecVal(arena, 16, 1234);
  EXPECT_EQ(FormatArg(val, 'D'), FormatArg(val, 'd'));
}

TEST(FormatArg, OctalUppercaseMatchesLowercase) {
  Arena arena;
  auto val = MakeLogic4VecVal(arena, 16, 0123);
  EXPECT_EQ(FormatArg(val, 'O'), FormatArg(val, 'o'));
}

TEST(FormatArg, BinaryUppercaseMatchesLowercase) {
  Arena arena;
  auto val = MakeLogic4VecVal(arena, 8, 0b10110100);
  EXPECT_EQ(FormatArg(val, 'B'), FormatArg(val, 'b'));
}

TEST(FormatArg, RealExponentialUppercaseWritesAnUppercaseExponentLetter) {
  Arena arena;
  auto val = MakeRealVec(arena, 7.25, 64);
  EXPECT_EQ(FormatArg(val, 'e'), "7.250000e+00");
  EXPECT_EQ(FormatArg(val, 'E'), "7.250000E+00");
}

TEST(FormatArg, RealDecimalUppercaseMatchesLowercase) {
  Arena arena;
  auto val = MakeRealVec(arena, 3.5, 64);
  EXPECT_EQ(FormatArg(val, 'F'), FormatArg(val, 'f'));
}

TEST(FormatArg, RealGeneralUppercaseMatchesLowercase) {
  Arena arena;
  auto val = MakeRealVec(arena, 12.5, 64);
  EXPECT_EQ(FormatArg(val, 'G'), FormatArg(val, 'g'));
}

TEST(SysTask, FormatCharacterInString) {
  std::vector<Logic4Vec> vals;
  Arena arena;
  vals.push_back(MakeLogic4VecVal(arena, 8, 0x42));
  auto out = FormatDisplay("%c", vals);
  EXPECT_EQ(out, "B");
}

TEST(SysTask, RealFormatGeneral) {
  std::vector<Logic4Vec> vals;
  Arena arena;
  vals.push_back(MakeRealVec(arena, 4.25, 64));
  auto out = FormatDisplay("%g", vals);
  EXPECT_NE(out.find("4.25"), std::string::npos);
}

TEST(SysTask, FormatLibrarySubstitutesWithoutArgument) {
  std::vector<Logic4Vec> vals;
  auto out = FormatDisplay("%l", vals);
  EXPECT_FALSE(out.empty());
  EXPECT_EQ(out.find('%'), std::string::npos);
}

TEST(SysTask, FormatLibraryRendersDotSeparatedBinding) {
  std::vector<Logic4Vec> vals;
  auto out = FormatDisplay("%l", vals);
  EXPECT_NE(out.find('.'), std::string::npos);
}

TEST(SysTask, FormatLibraryUppercaseMatchesLowercase) {
  std::vector<Logic4Vec> vals;
  EXPECT_EQ(FormatDisplay("%L", vals), FormatDisplay("%l", vals));
}

TEST(SysTask, FormatTimeUsesTimeformatSpec) {
  std::vector<Logic4Vec> vals;
  Arena arena;
  vals.push_back(MakeLogic4VecVal(arena, 32, 42));
  TimeFormatSpec spec;
  spec.precision_number = 2;
  spec.minimum_field_width = 1;
  spec.suffix_string = " ns";
  auto out = FormatDisplay("%t", vals, {.time_format = &spec, .loc = {}});
  EXPECT_NE(out.find("42.00"), std::string::npos);
  EXPECT_NE(out.find(" ns"), std::string::npos);
}

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
  auto lower =
      FormatDisplay("%t", vals_lower, {.time_format = &spec, .loc = {}});
  auto upper =
      FormatDisplay("%T", vals_upper, {.time_format = &spec, .loc = {}});
  EXPECT_EQ(lower, upper);
}

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

TEST(FormatArg, UnknownSpecifierSurfacesAsLiteralPercent) {
  Arena arena;
  auto val = MakeLogic4VecVal(arena, 8, 0);
  auto out = FormatArg(val, 'q');
  EXPECT_NE(out.find('%'), std::string::npos);
}

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

TEST(FormatArg, UnformattedTwoValueTreatsXZAsZero) {
  Arena arena;
  auto val = MakeLogic4Vec(arena, 4);
  val.words[0].aval = 0x6;
  val.words[0].bval = 0x3;
  auto out = FormatArg(val, 'u');
  ASSERT_EQ(out.size(), 4u);
  EXPECT_EQ(static_cast<unsigned char>(out[0]), 0x4u);
}

TEST(FormatArg, UnformattedFourValuePreservesXZ) {
  Arena arena;
  auto val = MakeLogic4Vec(arena, 4);
  val.words[0].aval = 0x6;
  val.words[0].bval = 0x3;
  auto out = FormatArg(val, 'z');
  ASSERT_EQ(out.size(), 8u);
  EXPECT_EQ(static_cast<unsigned char>(out[0]), 0x6u);
  EXPECT_EQ(static_cast<unsigned char>(out[4]), 0x3u);
  EXPECT_NE(FormatArg(val, 'z'), FormatArg(val, 'u'));
}

TEST(FormatArg, UnformattedUppercaseMatchesLowercase) {
  Arena arena;
  auto val = MakeLogic4VecVal(arena, 16, 0xBEEF);
  EXPECT_EQ(FormatArg(val, 'U'), FormatArg(val, 'u'));
  EXPECT_EQ(FormatArg(val, 'Z'), FormatArg(val, 'z'));
}

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

TEST(SysTask, RealFormatWidthAndPrecisionG) {
  std::vector<Logic4Vec> vals;
  Arena arena;
  vals.push_back(MakeRealVec(arena, 3.14159, 64));
  auto out = FormatDisplay("%10.3g", vals);
  ASSERT_EQ(out.size(), 10u);
  EXPECT_EQ(out.substr(6), "3.14");
  EXPECT_EQ(out[0], ' ');
}

TEST(SysTask, RealFormatPrecisionOnlyF) {
  std::vector<Logic4Vec> vals;
  Arena arena;
  vals.push_back(MakeRealVec(arena, 3.14159, 64));
  auto out = FormatDisplay("%.3f", vals);
  EXPECT_EQ(out, "3.142");
}

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

TEST(SysTask, RealFormatTakesCFlags) {
  SimFixture f;
  std::string out = CaptureDisplayOutput(
      "module t;\n"
      "  real x = 3.14159, n = -2.5;\n"
      "  string s;\n"
      "  initial begin\n"
      "    $display(\"[%-10.3f][%+e][%#.0f][% f][%010.3f][%08.2f]\",\n"
      "             x, x, x, x, x, n);\n"
      "    s = $sformatf(\"[%-8.2f][%+.1f][% .1f]\", n, n, x);\n"
      "    $display(\"%s\", s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "[3.142     ][+3.141590e+00][3.][ 3.141590][000003.142][-0002.50]\n"
            "[-2.50   ][-2.5][ 3.1]\n");
}

TEST(SysTask, UppercaseRealSpecifiersWriteUppercaseLetters) {
  SimFixture f;
  std::string out = CaptureDisplayOutput(
      "module t;\n"
      "  shortreal sr = 2.5;\n"
      "  real r = 3.14159265, big = 1.0e10;\n"
      "  string s;\n"
      "  initial begin\n"
      "    $display(\"%E %e\", sr, sr);\n"
      "    $display(\"[%G][%10.2E][%F]\", big, r, r);\n"
      "    s = $sformatf(\"%E\", r);\n"
      "    $display(\"%s\", s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out,
            "2.500000E+00 2.500000e+00\n"
            "[1E+10][  3.14E+00][3.141593]\n"
            "3.141593E+00\n");
}

TEST(SysTask, LeadingZeroWidthOnDecimalIsNoZeroFlag) {
  SimFixture f;
  std::string out = CaptureDisplayOutput(
      "module t;\n"
      "  initial $display(\"[%05d][%5d]\", 7, 7);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[    7][    7]\n");
}

TEST(SysTask, EachSpecifierConsumesFollowingArgumentInOrder) {
  std::vector<Logic4Vec> vals;
  Arena arena;
  vals.push_back(MakeLogic4VecVal(arena, 8, 3));
  vals.push_back(MakeLogic4VecVal(arena, 8, 7));
  auto out = FormatDisplay("%0d %0d", vals);
  EXPECT_EQ(out, "3 7");
}

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
  EXPECT_EQ(out.find('\n'), std::string::npos);
}

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
  EXPECT_NE(out.find('2'), std::string::npos);
}

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
  EXPECT_FALSE(f.has_errors);
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  LowerAndRun(design, f);
  std::cout.rdbuf(old_buf);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unformatted unpacked argument", 5, "21.2.1.1"));
  EXPECT_EQ(captured.str().find('2'), std::string::npos);
}

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
  EXPECT_FALSE(f.has_errors);
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  LowerAndRun(design, f);
  std::cout.rdbuf(old_buf);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an integer format specifier cannot be applied", 5,
                            "21.2.1.1"));
}

TEST(SysTask, BareUnpackedNonByteArrayNames21_2_1_1) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int nums[0:1];\n"
      "  initial begin\n"
      "    nums[0] = 4; nums[1] = 5;\n"
      "    $display(nums);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  std::ostringstream sink;
  std::streambuf* saved = std::cout.rdbuf(sink.rdbuf());
  LowerAndRun(design, f);
  std::cout.rdbuf(saved);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "unformatted unpacked argument", 5, "21.2.1.1"));
}

TEST(SysTask, IntegerSpecifierOnUnpackedArrayNames21_2_1_1) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int nums[0:1];\n"
      "  initial begin\n"
      "    nums[0] = 6; nums[1] = 7;\n"
      "    $display(\"%d\", nums);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  std::ostringstream sink;
  std::streambuf* saved = std::cout.rdbuf(sink.rdbuf());
  LowerAndRun(design, f);
  std::cout.rdbuf(saved);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "an integer format specifier cannot be applied", 5,
                            "21.2.1.1"));
}

TEST(SysTask, ExpressionAfterATemplateWithoutConversionsPrintsInDecimal) {
  SimFixture f;
  std::string out = CaptureDisplayOutput(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial begin\n"
      "    a = 42;\n"
      "    $display(\"x\", a);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "x 42\n");
}

TEST(SysTask, TemplateTakesAsManyArgumentsAsItHasConversions) {
  SimFixture f;
  std::string out = CaptureDisplayOutput(
      "module t;\n"
      "  int a = 5;\n"
      "  initial $display(\"%0d\", a, \"y%0d\", \"B\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "5y66\n");
}

TEST(SysTask, ScopeAndPercentSpecsTakeNoArgument) {
  SimFixture f;
  std::string out = CaptureDisplayOutput(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial begin\n"
      "    a = 7;\n"
      "    $display(\"%m%%\", a);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "t%  7\n");
}

TEST(SysTask, RealSpecifierShowsAnIntegralOperandsValue) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  parameter P = 5;\n"
                       "  int si = -3;\n"
                       "  logic [3:0] u = 4'hF;\n"
                       "  logic [3:0] xz = 4'b1x0z;\n"
                       "  initial $display(\"%f %f %f %f %e %g\",\n"
                       "                   P, si, u, xz, -3, 2);\n"
                       "endmodule\n",
                       f),
            "5.000000 -3.000000 15.000000 8.000000 -3.000000e+00 2\n");
}

}  // namespace
