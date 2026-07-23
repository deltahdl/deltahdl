#include <cstdio>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// §21.3.4.3 governs $fscanf and $sscanf. Both read characters ($fscanf from a
// file descriptor, $sscanf from a str expression), interpret them under a
// control string, and store the converted fields into the argument variables,
// returning the count of matched-and-assigned items (0 on an early matching
// failure, EOF when the input runs out first). Every rule operates on inputs
// produced elsewhere -- a §21.3.1 descriptor, a declared destination, a
// $timeformat configuration -- so each test builds those from real source
// syntax and drives the full pipeline.

// Runs a single-module source through parse -> elaborate -> lower -> run while
// capturing everything the run writes to stdout.
static std::string RunCapture(const std::string& src, SysTaskFixture& f) {
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  auto* design = ElaborateSrc(src, f);
  if (design != nullptr) LowerAndRun(design, f);
  std::cout.rdbuf(old_buf);
  return captured.str();
}

// Creates `path` holding `content` so a read-type $fopen has data to deliver.
static void SeedFile(const std::string& path, const std::string& content) {
  std::ofstream ofs(path, std::ios::binary);
  ofs << content;
}

// C1 + C15: $fscanf reads formatted fields from the file specified by fd and
// returns the number of successfully matched and assigned items; when the
// input ends partway through the control string, the completed conversions
// still count.
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
  // "ff" fails %d, so only one field converts on the second pass.
  EXPECT_NE(out.find("m=1"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// C5: the format can be an expression -- a string-typed variable for $sscanf
// and an integral variable holding the control characters for $fscanf -- not
// only a literal.
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

// C2: the str argument of $sscanf may be a string-typed expression, an
// integral expression whose packed bytes spell the text, or an unpacked array
// of byte read from its left bound.
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

// C6: for $sscanf, null characters shall also be considered white space. A
// NUL sitting between two digit runs separates them the way a blank would;
// were it dropped instead, the runs would fuse into one number.
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

// C3: when the format is exhausted while arguments remain, the excess
// arguments are ignored and keep their prior values.
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

// C4: an argument too small to hold the converted input takes the LSBs.
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

// C4: when the destination is real and the converted input exceeds its range,
// the value +Inf (or -Inf) is transferred.
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

// C7: an ordinary character in the control string shall match the next input
// character; a mismatch ends the scan with nothing assigned.
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

// C8: the assignment-suppression character * converts and consumes an input
// field without taking a destination argument, and the suppressed field does
// not count toward the return value.
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

// C8 + C9: a decimal maximum field width bounds how many characters one
// conversion may consume; the next conversion resumes right after it.
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

// C9: leading white space ahead of an input field is ignored for every
// conversion except %c, which takes the next character verbatim.
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
  EXPECT_NE(out.find("n=1 cv=32"), std::string::npos) << out;  // the blank
  EXPECT_NE(out.find("m=1 d=42"), std::string::npos) << out;
}

// C10: the integer format specifiers read into any integral data type,
// including an enumerated type (declared through typedef) and a packed
// aggregate.
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

// C10 negative: the integer format specifiers shall not be used with any
// unpacked aggregate data type; the misuse converts nothing and the elements
// keep their values.
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

// C11 (Table 21-7, b/h rows): a binary or hexadecimal field admits x, z (and
// ?) digits alongside the base digits, each contributing its bit group to the
// 4-state result, and underscores inside the digit string are skipped.
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

// C11 (Table 21-7, d row): a decimal field is an optionally signed digit
// string, or a single x/z/? standing for an entirely unknown or
// high-impedance value.
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

// C11 (Table 21-7, v row): %v matches a three-character net signal strength
// sequence in the §21.2.1.4 form; the logic value is converted to its 4-value
// equivalent and assigned.
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

// C11 (Table 21-7, t row): a %t field is a floating-point number scaled and
// rounded according to the timescale configured by $timeformat (§20.4.3). The
// LRM's own figures: with a 1ns time unit (the default here) and
// $timeformat(-3,2," ms",10), reading "10.345" yields 10350000.0.
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

// C11 (Table 21-7, u row): %u transfers unformatted 2-value binary data
// sufficient to fill the destination, in the same layout a matching
// $fwrite("%u", data) emits, so a write-then-read round trip reproduces the
// value.
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

// C11 (Table 21-7, z row): %z transfers unformatted 4-value binary data in
// the s_vpi_vecval pair layout, preserving x and z across a $fwrite("%z")
// round trip.
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

// C11 (Table 21-7, m row): %m assigns the current hierarchical path
// (§21.2.1.5) as a string and does not read data from the input, so the
// following conversion still sees the whole input.
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

// C12: %s stores a run of nonwhite characters into a string variable (which
// resizes to the run), an unpacked array of byte (one character per element
// from the left bound), or a packed integral variable.
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

// C13: unknown bits (x or z) in the format string or in the str argument of
// $sscanf make the function return EOF (-1).
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

// C14: when conversion terminates on a conflicting input character, that
// character is left unread; trailing white space not matched by a directive
// is left unread too. The next $fgetc calls observe both.
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
  // 'x' (120) conflicted with the first %d; the blank (32) after "34" was not
  // matched by any directive.
  EXPECT_NE(out.find("c1=120 d=34 c2=32"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// C15: EOF (-1) is returned when the input ends before the first conversion,
// and 0 when an input character fails to match the control string early.
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

// C8 + Table 21-7 (% row): %% matches a literal percent in the input and
// assigns nothing; the digit after it still converts under %d.
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

// C11 (Table 21-7, o row): an octal field is a sequence from the octal digits
// plus x, z (or ?), and underscores; an x digit contributes a three-bit x
// group to the 4-state result.
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

// C11: each integer conversion code has an uppercase alternate (%D, %H, %B,
// %O) that behaves like its lowercase form.
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

// C4: arguments of any length are supported -- a destination wider than one
// machine word takes the whole converted field.
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

// C6 + C14: a single white-space character in the control string matches a
// whole run of mixed input white space (blank, tab, newline); and when a
// trailing white-space directive is present, the trailing input white space
// IS consumed -- the "unless matched by a directive" arm -- so the next read
// starts at the character after it.
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
  // The tab+newline run separates 1 from 2; the trailing directive ate both
  // blanks, so $fgetc sees 'x' (120) rather than a blank.
  EXPECT_NE(out.find("n=2 a=1 b=2 m=1 d=5 c=120"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// C14 + C15: leading white space may be skipped without constituting a match,
// so an input holding only white space still returns EOF (-1) rather than 0.
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

// C5: the remaining format-expression combinations -- $sscanf driven by an
// integral variable holding the control characters, and $fscanf driven by a
// string-typed variable -- so each front end is observed with each
// non-literal format form.
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

// C11 (Table 21-7, h/x row): %x is an alternate spelling of the hexadecimal
// conversion, including its 4-state digits.
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

// C11 (Table 21-7, f/e/g row): %e and %g are alternate spellings of the
// floating-point conversion and accept the same token forms as %f.
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

// C11 (Table 21-7, v row): the strength sequence's logic value may itself be
// unknown -- reading "StX" assigns x.
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

// C8 negative (Table 21-7, % row): %% demands a literal percent in the input;
// when the input holds something else, the scan ends with nothing assigned.
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

// C13 via the $fscanf front end: unknown bits in a variable-held format make
// $fscanf report EOF (-1), leaving the destination untouched.
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

// C11 (Table 21-7, f/e/g rows) + C15: a floating-point field with an exponent
// part converts into a real destination, and the count reflects it.
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

}  // namespace
