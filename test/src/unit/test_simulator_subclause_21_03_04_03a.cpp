#include <gtest/gtest.h>

#include <cstdio>
#include <string>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_temp_file.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

std::string ScanStrengthInto(const std::string& seq, SysTaskFixture& f) {
  return RunCapture(
      "module t;\n"
      "  reg r;\n"
      "  integer n;\n"
      "  initial begin\n"
      "    n = $sscanf(\"" +
          seq +
          "\", \"%v\", r);\n"
          "    $display(\"n=%0d r=%b\", n, r);\n"
          "  end\n"
          "endmodule\n",
      f);
}

TEST(ReadingFormattedData, FscanfReadsFieldsAndReturnsCount) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213403_fields.txt";
  SeedFile(tmp, "42 ff");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, n, m, d, h, e;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    n = $fscanf(fd, \"%d %h\", d, h);\n"
          "    $display(\"n=%0d d=%0d h=%0h\", n, d, h);\n"
          "    $fclose(fd);\n"
          "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    m = $fscanf(fd, \"%d %d %d\", d, h, e);\n"
          "    $display(\"m=%0d\", m);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("n=2 d=42 h=ff"), std::string::npos) << out;
  EXPECT_NE(out.find("m=1"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

TEST(ReadingFormattedData, FormatMayBeAVariableExpression) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213403_fmtvar.txt";
  SeedFile(tmp, "beef");
  std::string out = RunCapture(
      "module t;\n"
      "  string sfmt;\n"
      "  reg [15:0] ifmt;\n"
      "  integer fd, n, m, d, h;\n"
      "  initial begin\n"
      "    sfmt = \"%d\";\n"
      "    n = $sscanf(\"42\", sfmt, d);\n"
      "    $display(\"n=%0d d=%0d\", n, d);\n"
      "    ifmt = \"%h\";\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    m = $fscanf(fd, ifmt, h);\n"
          "    $display(\"m=%0d h=%0h\", m, h);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("n=1 d=42"), std::string::npos) << out;
  EXPECT_NE(out.find("m=1 h=beef"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

TEST(ReadingFormattedData, SscanfStrSourceForms) {
  SysTaskFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  string ss;\n"
      "  reg [15:0] is;\n"
      "  byte bs [0:1];\n"
      "  integer n1, n2, n3, a, b, c;\n"
      "  initial begin\n"
      "    ss = \"11\";\n"
      "    is = \"22\";\n"
      "    bs[0] = \"3\"; bs[1] = \"3\";\n"
      "    n1 = $sscanf(ss, \"%d\", a);\n"
      "    n2 = $sscanf(is, \"%d\", b);\n"
      "    n3 = $sscanf(bs, \"%d\", c);\n"
      "    $display(\"n1=%0d a=%0d n2=%0d b=%0d n3=%0d c=%0d\",\n"
      "             n1, a, n2, b, n3, c);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("n1=1 a=11 n2=1 b=22 n3=1 c=33"), std::string::npos)
      << out;
}

TEST(ReadingFormattedData, SscanfNulCharactersAreWhiteSpace) {
  SysTaskFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  reg [23:0] src;\n"
      "  integer n, a, b;\n"
      "  initial begin\n"
      "    src = {\"7\", 8'h00, \"8\"};\n"
      "    n = $sscanf(src, \"%d %d\", a, b);\n"
      "    $display(\"n=%0d a=%0d b=%0d\", n, a, b);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("n=2 a=7 b=8"), std::string::npos) << out;
}

TEST(ReadingFormattedData, ExcessArgumentsAreIgnored) {
  SysTaskFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  integer n, a, b;\n"
      "  initial begin\n"
      "    b = 7;\n"
      "    n = $sscanf(\"3\", \"%d\", a, b);\n"
      "    $display(\"n=%0d a=%0d b=%0d\", n, a, b);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("n=1 a=3 b=7"), std::string::npos) << out;
}

TEST(ReadingFormattedData, NarrowDestinationTakesLsbs) {
  SysTaskFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  reg [7:0] narrow;\n"
      "  integer n;\n"
      "  initial begin\n"
      "    n = $sscanf(\"511\", \"%d\", narrow);\n"
      "    $display(\"n=%0d narrow=%0d\", n, narrow);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("n=1 narrow=255"), std::string::npos) << out;
}

TEST(ReadingFormattedData, RealDestinationOverflowBecomesInfinity) {
  SysTaskFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  real rp, rn;\n"
      "  integer n, m;\n"
      "  initial begin\n"
      "    n = $sscanf(\"1e400\", \"%f\", rp);\n"
      "    m = $sscanf(\"-1e400\", \"%f\", rn);\n"
      "    $display(\"n=%0d rp=%g m=%0d rn=%g\", n, rp, m, rn);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("n=1 rp=inf m=1 rn=-inf"), std::string::npos) << out;
}

TEST(ReadingFormattedData, OrdinaryCharactersMustMatch) {
  SysTaskFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  integer n, m, v;\n"
      "  initial begin\n"
      "    n = $sscanf(\"a=5\", \"a=%d\", v);\n"
      "    $display(\"n=%0d v=%0d\", n, v);\n"
      "    v = 99;\n"
      "    m = $sscanf(\"y5\", \"x%d\", v);\n"
      "    $display(\"m=%0d v=%0d\", m, v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("n=1 v=5"), std::string::npos) << out;
  EXPECT_NE(out.find("m=0 v=99"), std::string::npos) << out;
}

TEST(ReadingFormattedData, SuppressedConversionTakesNoArgument) {
  SysTaskFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  integer n, kept;\n"
      "  initial begin\n"
      "    n = $sscanf(\"3 4\", \"%*d %d\", kept);\n"
      "    $display(\"n=%0d kept=%0d\", n, kept);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("n=1 kept=4"), std::string::npos) << out;
}

TEST(ReadingFormattedData, MaximumFieldWidthBoundsTheField) {
  SysTaskFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  integer n, a, b;\n"
      "  initial begin\n"
      "    n = $sscanf(\"12345\", \"%2d%d\", a, b);\n"
      "    $display(\"n=%0d a=%0d b=%0d\", n, a, b);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("n=2 a=12 b=345"), std::string::npos) << out;
}

TEST(ReadingFormattedData, CharConversionDoesNotSkipWhiteSpace) {
  SysTaskFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  reg [7:0] cv;\n"
      "  integer n, m, d;\n"
      "  initial begin\n"
      "    n = $sscanf(\" A\", \"%c\", cv);\n"
      "    $display(\"n=%0d cv=%0d\", n, cv);\n"
      "    m = $sscanf(\"   42\", \"%d\", d);\n"
      "    $display(\"m=%0d d=%0d\", m, d);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("n=1 cv=32"), std::string::npos) << out;
  EXPECT_NE(out.find("m=1 d=42"), std::string::npos) << out;
}

TEST(ReadingFormattedData, IntegerCodesReadEnumAndPackedTypes) {
  SysTaskFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef enum logic [3:0] {E0, E1, E2, E3} e_t;\n"
      "  e_t ev;\n"
      "  struct packed { logic [3:0] hi; logic [3:0] lo; } ps;\n"
      "  integer n, m;\n"
      "  initial begin\n"
      "    n = $sscanf(\"3\", \"%d\", ev);\n"
      "    m = $sscanf(\"a5\", \"%h\", ps);\n"
      "    $display(\"n=%0d ev=%0d m=%0d ps=%h hi=%h\", n, ev, m, ps, ps.hi);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("n=1 ev=3 m=1 ps=a5 hi=a"), std::string::npos) << out;
}

TEST(ReadingFormattedData, IntegerCodeRejectsUnpackedAggregate) {
  SysTaskFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  integer m [0:1];\n"
      "  integer n;\n"
      "  initial begin\n"
      "    m[0] = 9;\n"
      "    n = $sscanf(\"5\", \"%d\", m);\n"
      "    $display(\"n=%0d m0=%0d\", n, m[0]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("n=0 m0=9"), std::string::npos) << out;
}

TEST(ReadingFormattedData, IntegerFieldsAcceptFourStateDigits) {
  SysTaskFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  reg [3:0] bv;\n"
      "  reg [11:0] hv;\n"
      "  reg [3:0] uv;\n"
      "  integer n, m, k;\n"
      "  initial begin\n"
      "    n = $sscanf(\"1x0z\", \"%b\", bv);\n"
      "    m = $sscanf(\"aZ3\", \"%h\", hv);\n"
      "    k = $sscanf(\"10_10\", \"%b\", uv);\n"
      "    $display(\"n=%0d bv=%b m=%0d hv=%h k=%0d uv=%b\",\n"
      "             n, bv, m, hv, k, uv);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("n=1 bv=1x0z m=1 hv=az3 k=1 uv=1010"), std::string::npos)
      << out;
}

TEST(ReadingFormattedData, DecimalFieldAcceptsSignAndLoneXz) {
  SysTaskFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  integer n, m, k, sv;\n"
      "  reg [3:0] xv, zv;\n"
      "  initial begin\n"
      "    n = $sscanf(\"-12\", \"%d\", sv);\n"
      "    m = $sscanf(\"x\", \"%d\", xv);\n"
      "    k = $sscanf(\"?\", \"%d\", zv);\n"
      "    $display(\"n=%0d sv=%0d m=%0d xv=%b k=%0d zv=%b\",\n"
      "             n, sv, m, xv, k, zv);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("n=1 sv=-12 m=1 xv=xxxx k=1 zv=zzzz"), std::string::npos)
      << out;
}

TEST(ReadingFormattedData, StrengthFieldReadsThreeCharacterSequence) {
  SysTaskFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  reg r1, rz;\n"
      "  integer n;\n"
      "  initial begin\n"
      "    n = $sscanf(\"St1 HiZ\", \"%v %v\", r1, rz);\n"
      "    $display(\"n=%0d r1=%b rz=%b\", n, r1, rz);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("n=2 r1=1 rz=z"), std::string::npos) << out;
}

TEST(ReadingFormattedData, TimeFieldScalesPerTimeformat) {
  SysTaskFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  real tv;\n"
      "  integer n;\n"
      "  initial begin\n"
      "    $timeformat(-3, 2, \" ms\", 10);\n"
      "    n = $sscanf(\"10.345\", \"%t\", tv);\n"
      "    $display(\"n=%0d tv=%g\", n, tv);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("n=1 tv=1.035e+07"), std::string::npos) << out;
}

TEST(ReadingFormattedData, UnformattedTwoValueRoundTripsThroughFwrite) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213403_u.bin";
  std::string out = RunCapture(
      "module t;\n"
      "  reg [15:0] src, dst;\n"
      "  integer fd, n;\n"
      "  initial begin\n"
      "    src = 16'hbeef;\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"w\");\n"
          "    $fwrite(fd, \"%u\", src);\n"
          "    $fclose(fd);\n"
          "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    n = $fscanf(fd, \"%u\", dst);\n"
          "    $display(\"n=%0d dst=%h\", n, dst);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("n=1 dst=beef"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

TEST(ReadingFormattedData, UnformattedFourValueRoundTripsPreservingXz) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213403_z.bin";
  std::string out = RunCapture(
      "module t;\n"
      "  reg [7:0] src, dst;\n"
      "  integer fd, n;\n"
      "  initial begin\n"
      "    src = 8'b1x0z01zx;\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"w\");\n"
          "    $fwrite(fd, \"%z\", src);\n"
          "    $fclose(fd);\n"
          "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    n = $fscanf(fd, \"%z\", dst);\n"
          "    $display(\"n=%0d dst=%b\", n, dst);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("n=1 dst=1x0z01zx"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

TEST(ReadingFormattedData, HierPathFieldConsumesNoInput) {
  SysTaskFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  string p;\n"
      "  integer n, v;\n"
      "  initial begin\n"
      "    n = $sscanf(\"77\", \"%m%d\", p, v);\n"
      "    $display(\"n=%0d p=[%s] v=%0d\", n, p, v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("n=2 p=[t] v=77"), std::string::npos) << out;
}

TEST(ReadingFormattedData, StringFieldDestinationForms) {
  SysTaskFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  string sv;\n"
      "  byte ba [0:3];\n"
      "  reg [15:0] pv;\n"
      "  integer n;\n"
      "  initial begin\n"
      "    sv = \"previous-longer-content\";\n"
      "    n = $sscanf(\"wxyz stuv hi\", \"%s %s %s\", sv, ba, pv);\n"
      "    $display(\"n=%0d sv=[%s] ba=[%s] pv=[%s]\", n, sv, ba, pv);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("n=3 sv=[wxyz] ba=[stuv] pv=[hi]"), std::string::npos)
      << out;
}

TEST(ReadingFormattedData, UnknownBitsInFormatOrStrReturnEof) {
  SysTaskFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  reg [15:0] bad;\n"
      "  integer n, m, d;\n"
      "  initial begin\n"
      "    bad = 16'hxxxx;\n"
      "    n = $sscanf(\"42\", bad, d);\n"
      "    m = $sscanf(bad, \"%d\", d);\n"
      "    $display(\"n=%0d m=%0d\", n, m);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("n=-1 m=-1"), std::string::npos) << out;
}

TEST(ReadingFormattedData, ConflictingAndTrailingCharactersStayUnread) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213403_unread.txt";
  SeedFile(tmp, "12x 34 z");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, n, d, c1, c2;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    n = $fscanf(fd, \"%d\", d);\n"
          "    c1 = $fgetc(fd);\n"
          "    n = $fscanf(fd, \"%d\", d);\n"
          "    c2 = $fgetc(fd);\n"
          "    $display(\"c1=%0d d=%0d c2=%0d\", c1, d, c2);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("c1=120 d=34 c2=32"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

TEST(ReadingFormattedData, EofAndMatchingFailureReturnValues) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213403_empty.txt";
  SeedFile(tmp, "");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, n, m, d;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    n = $fscanf(fd, \"%d\", d);\n"
          "    $fclose(fd);\n"
          "    m = $sscanf(\"abc\", \"%d\", d);\n"
          "    $display(\"n=%0d m=%0d\", n, m);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("n=-1 m=0"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

TEST(ReadingFormattedData, LiteralPercentMatchesWithoutAssigning) {
  SysTaskFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  integer n, v;\n"
      "  initial begin\n"
      "    n = $sscanf(\"%5\", \"%%%d\", v);\n"
      "    $display(\"n=%0d v=%0d\", n, v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("n=1 v=5"), std::string::npos) << out;
}

TEST(ReadingFormattedData, OctalFieldAcceptsFourStateDigits) {
  SysTaskFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  integer n, m, ov;\n"
      "  reg [8:0] xv;\n"
      "  initial begin\n"
      "    n = $sscanf(\"17\", \"%o\", ov);\n"
      "    m = $sscanf(\"2x_7\", \"%o\", xv);\n"
      "    $display(\"n=%0d ov=%0d m=%0d xv=%o\", n, ov, m, xv);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("n=1 ov=15 m=1 xv=2x7"), std::string::npos) << out;
}

TEST(ReadingFormattedData, UppercaseConversionCodesMatchLowercase) {
  SysTaskFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  integer n, m, d, h;\n"
      "  initial begin\n"
      "    n = $sscanf(\"42\", \"%D\", d);\n"
      "    m = $sscanf(\"ff\", \"%H\", h);\n"
      "    $display(\"n=%0d d=%0d m=%0d h=%0h\", n, d, m, h);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("n=1 d=42 m=1 h=ff"), std::string::npos) << out;
}

TEST(ReadingFormattedData, WideDestinationTakesWholeField) {
  SysTaskFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  reg [95:0] wv;\n"
      "  integer n;\n"
      "  initial begin\n"
      "    n = $sscanf(\"0123456789abcdef01234567\", \"%h\", wv);\n"
      "    $display(\"n=%0d wv=%h\", n, wv);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("n=1 wv=0123456789abcdef01234567"), std::string::npos)
      << out;
}

TEST(ReadingFormattedData, WhitespaceDirectiveMatchesRunAndConsumesTrailing) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213403_wsdir.txt";
  SeedFile(tmp, "5  x");
  std::string out = RunCapture(
      "module t;\n"
      "  reg [31:0] src;\n"
      "  integer fd, n, m, a, b, d, c;\n"
      "  initial begin\n"
      "    src = {\"1\", 8'h09, 8'h0a, \"2\"};\n"
      "    n = $sscanf(src, \"%d %d\", a, b);\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    m = $fscanf(fd, \"%d \", d);\n"
          "    c = $fgetc(fd);\n"
          "    $display(\"n=%0d a=%0d b=%0d m=%0d d=%0d c=%0d\",\n"
          "             n, a, b, m, d, c);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("n=2 a=1 b=2 m=1 d=5 c=120"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

TEST(ReadingFormattedData, WhitespaceOnlyInputReturnsEof) {
  SysTaskFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  integer n, d;\n"
      "  initial begin\n"
      "    n = $sscanf(\"   \", \"%d\", d);\n"
      "    $display(\"n=%0d\", n);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("n=-1"), std::string::npos) << out;
}

TEST(ReadingFormattedData, FormatExpressionFormsCrossFunctions) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213403_fmtcross.txt";
  SeedFile(tmp, "55");
  std::string out = RunCapture(
      "module t;\n"
      "  reg [15:0] ifmt;\n"
      "  string sfmt;\n"
      "  integer fd, n, m, a, b;\n"
      "  initial begin\n"
      "    ifmt = \"%d\";\n"
      "    n = $sscanf(\"64\", ifmt, a);\n"
      "    sfmt = \"%d\";\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    m = $fscanf(fd, sfmt, b);\n"
          "    $display(\"n=%0d a=%0d m=%0d b=%0d\", n, a, m, b);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("n=1 a=64 m=1 b=55"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

TEST(ReadingFormattedData, HexFieldViaXCode) {
  SysTaskFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  reg [7:0] hv;\n"
      "  integer n;\n"
      "  initial begin\n"
      "    n = $sscanf(\"z9\", \"%x\", hv);\n"
      "    $display(\"n=%0d hv=%h\", n, hv);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("n=1 hv=z9"), std::string::npos) << out;
}

TEST(ReadingFormattedData, RealFieldAliasCodes) {
  SysTaskFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  real re, rg;\n"
      "  integer n, m;\n"
      "  initial begin\n"
      "    n = $sscanf(\"1.5e2\", \"%e\", re);\n"
      "    m = $sscanf(\"-0.25\", \"%g\", rg);\n"
      "    $display(\"n=%0d re=%g m=%0d rg=%g\", n, re, m, rg);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("n=1 re=150 m=1 rg=-0.25"), std::string::npos) << out;
}

TEST(ReadingFormattedData, StrengthFieldReadsUnknownValue) {
  SysTaskFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  reg rx;\n"
      "  integer n;\n"
      "  initial begin\n"
      "    n = $sscanf(\"StX\", \"%v\", rx);\n"
      "    $display(\"n=%0d rx=%b\", n, rx);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("n=1 rx=x"), std::string::npos) << out;
}

TEST(ReadingFormattedData, LiteralPercentMismatchEndsScan) {
  SysTaskFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  integer n, v;\n"
      "  initial begin\n"
      "    v = 88;\n"
      "    n = $sscanf(\"5\", \"%%%d\", v);\n"
      "    $display(\"n=%0d v=%0d\", n, v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("n=0 v=88"), std::string::npos) << out;
}

TEST(ReadingFormattedData, FscanfUnknownBitsInFormatReturnsEof) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213403_fmtxz.txt";
  SeedFile(tmp, "42");
  std::string out = RunCapture(
      "module t;\n"
      "  reg [15:0] bad;\n"
      "  integer fd, n, d;\n"
      "  initial begin\n"
      "    bad = 16'hxxxx;\n"
      "    d = 6;\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    n = $fscanf(fd, bad, d);\n"
          "    $display(\"n=%0d d=%0d\", n, d);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("n=-1 d=6"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

TEST(ReadingFormattedData, RealFieldConvertsIntoRealDestination) {
  SysTaskFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  real rv;\n"
      "  integer n;\n"
      "  initial begin\n"
      "    n = $sscanf(\"2.5e1\", \"%f\", rv);\n"
      "    $display(\"n=%0d rv=%g\", n, rv);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("n=1 rv=25"), std::string::npos) << out;
}

TEST(ReadingFormattedData, IntegerCodeOnAggregateNames21_3_4_3) {
  SysTaskFixture f;
  RunCapture(
      "module t;\n"
      "  integer cells [0:1];\n"
      "  integer n;\n"
      "  initial begin\n"
      "    cells[0] = 3;\n"
      "    n = $sscanf(\"8\", \"%d\", cells);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "may not read into unpacked aggregate", 6,
                              "21.3.4.3"));
}

TEST(ReadingFormattedData, StrengthFieldReadsAmbiguousZeroOrHighZ) {
  SysTaskFixture f;
  std::string out = ScanStrengthInto("StL", f);
  EXPECT_NE(out.find("n=1 r=x"), std::string::npos) << out;
}

TEST(ReadingFormattedData, StrengthFieldReadsAmbiguousOneOrHighZ) {
  SysTaskFixture f;
  std::string out = ScanStrengthInto("PuH", f);
  EXPECT_NE(out.find("n=1 r=x"), std::string::npos) << out;
}

TEST(ReadingFormattedData, StrengthFieldReadsBackWhatPercentVWrote) {
  SysTaskFixture f;
  NetStrength ns;
  ns.s0_hi = Strength::kStrong;
  ns.s0_lo = Strength::kHighz;
  ns.s1_hi = Strength::kHighz;
  ns.s1_lo = Strength::kHighz;
  std::string out = ScanStrengthInto(FormatStrength(ns), f);
  EXPECT_NE(out.find("n=1 r=x"), std::string::npos) << out;
}

TEST(ReadingFormattedData, SscanfDestinationWakesAnAlwaysCombReadingIt) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  integer v;\n"
      "  integer y;\n"
      "  integer n;\n"
      "  always_comb y = v + 1;\n"
      "  initial begin\n"
      "    #1 n = $sscanf(\"7\", \"%d\", v);\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 8u);
}

}  // namespace
