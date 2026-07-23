#include <cstdio>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// §21.3.4.1 governs $fgetc and $ungetc. Every rule here operates on a file
// descriptor, and its behavior depends entirely on how that descriptor was
// produced -- the §21.3.1 $fopen that created it -- so each test builds the
// descriptor from real $fopen source syntax and drives the whole pipeline,
// observing the read results through $display.

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

// §21.3.4.1: $fgetc reads a single byte from the file named by fd and yields
// its value; each call consumes exactly one byte, so consecutive calls walk
// the data byte by byte.
TEST(ReadCharacterAtATime, FgetcReadsOneBytePerCall) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213411_seq.txt";
  SeedFile(tmp, "AB");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, c1, c2;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    c1 = $fgetc(fd);\n"
          "    c2 = $fgetc(fd);\n"
          "    $display(\"c1=%0d c2=%0d\", c1, c2);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("c1=65 c2=66"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// §21.3.4.1: $fgetc is a function, so besides the assignment form shown by the
// standard's example it can sit directly in expression-operand position; the
// byte it yields participates in the enclosing comparison.
TEST(ReadCharacterAtATime, FgetcAsExpressionOperand) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213411_operand.txt";
  SeedFile(tmp, "Z");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    if ($fgetc(fd) == 90) $display(\"operand=match\");\n"
          "    else $display(\"operand=miss\");\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("operand=match"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// §21.3.4.1: the descriptor a character is read from may equally come from a
// read-update open type -- "r+" admits reading just as "r" does, and the
// byte-per-call semantics are identical.
TEST(ReadCharacterAtATime, FgetcReadsThroughReadUpdateDescriptor) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213411_rplus.txt";
  SeedFile(tmp, "GH");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, c1, c2;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r+\");\n"
          "    c1 = $fgetc(fd);\n"
          "    c2 = $fgetc(fd);\n"
          "    $display(\"c1=%0d c2=%0d\", c1, c2);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("c1=71 c2=72"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// §21.3.4.1: when the read cannot deliver a byte, the result is set to EOF
// (-1). Exhausting the data drives that path without any descriptor misuse.
TEST(ReadCharacterAtATime, FgetcReturnsEofWhenDataExhausted) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213411_eof.txt";
  SeedFile(tmp, "Z");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, c1, c2;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    c1 = $fgetc(fd);\n"
          "    c2 = $fgetc(fd);\n"
          "    $display(\"c1=%0d c2=%0d\", c1, c2);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("c1=90 c2=-1"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// §21.3.4.1: a genuine read error -- here, a descriptor whose file has been
// closed out from under it -- also sets the result to EOF (-1), and $ferror
// can then describe the cause (via the §21.3.7 per-descriptor record). A
// subsequent successful read on a fresh descriptor reports no error.
TEST(ReadCharacterAtATime, FgetcErrorYieldsEofAndFerrorReportsCause) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213411_err.txt";
  SeedFile(tmp, "Z");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, c, err, c2, err2;\n"
      "  reg [639:0] s;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    $fclose(fd);\n"
          "    c = $fgetc(fd);\n"
          "    err = $ferror(fd, s);\n"
          "    $display(\"c=%0d errnz=%0d\", c, err != 0);\n"
          "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    c2 = $fgetc(fd);\n"
          "    err2 = $ferror(fd, s);\n"
          "    $display(\"c2=%0d err2=%0d\", c2, err2);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("c=-1 errnz=1"), std::string::npos) << out;
  EXPECT_NE(out.find("c2=90 err2=0"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// §21.3.4.1: the result of $fgetc is wider than 8 bits precisely so a data
// byte of 0xFF (255) stays distinct from the EOF sentinel (-1). The byte
// occupies the low 8 bits with zero extension.
TEST(ReadCharacterAtATime, FgetcHighByteDistinctFromEof) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213411_ff.txt";
  SeedFile(tmp, std::string(1, '\xFF'));
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, c;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    c = $fgetc(fd);\n"
          "    $display(\"c=%0d iseof=%0d\", c, c == -1);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("c=255 iseof=0"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// §21.3.4.1: the character pushed by $ungetc shall be the one returned by the
// next $fgetc on that descriptor; reads after that continue with the stream's
// own remaining data. A successful push back yields the result code zero.
TEST(ReadCharacterAtATime, UngetcCharacterReturnedByNextFgetc) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213411_push.txt";
  SeedFile(tmp, "XY");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, c1, code, c2, c3;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    c1 = $fgetc(fd);\n"
          "    code = $ungetc(8'h5A, fd);\n"
          "    c2 = $fgetc(fd);\n"
          "    c3 = $fgetc(fd);\n"
          "    $display(\"c1=%0d code=%0d c2=%0d c3=%0d\", c1, code, c2, c3);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  // Read 'X', push 'Z', read back 'Z', then continue with the stream's 'Y'.
  EXPECT_NE(out.find("c1=88 code=0 c2=90 c3=89"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// §21.3.4.1: the pushed character c is an expression; a parameter constant is
// as valid a source for it as a literal, and the pushed value round-trips
// through the next $fgetc unchanged.
TEST(ReadCharacterAtATime, UngetcAcceptsParameterCharacter) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213411_param.txt";
  SeedFile(tmp, "Q");
  std::string out = RunCapture(
      "module t;\n"
      "  parameter [7:0] P = 8'h4B;\n"
      "  integer fd, code, c;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    code = $ungetc(P, fd);\n"
          "    c = $fgetc(fd);\n"
          "    $display(\"code=%0d c=%0d\", code, c);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("code=0 c=75"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// §21.3.4.1: the pushed character may equally come from a variable -- the
// classic shape pushes back the very character just read, so the following
// $fgetc delivers it a second time before the stream moves on.
TEST(ReadCharacterAtATime, UngetcPushesBackVariableJustRead) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213411_var.txt";
  SeedFile(tmp, "MN");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, c1, code, c2, c3;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    c1 = $fgetc(fd);\n"
          "    code = $ungetc(c1, fd);\n"
          "    c2 = $fgetc(fd);\n"
          "    c3 = $fgetc(fd);\n"
          "    $display(\"c1=%0d code=%0d c2=%0d c3=%0d\", c1, code, c2, c3);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  // 'M' is read, pushed back from the variable, read again, then 'N' follows.
  EXPECT_NE(out.find("c1=77 code=0 c2=77 c3=78"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// §21.3.4.1: the file itself is unchanged by $ungetc -- the push back lives
// only in the descriptor's buffer. Reopening the file after a push back and a
// read back delivers the original bytes with no trace of the pushed character.
TEST(ReadCharacterAtATime, UngetcLeavesFileUnchanged) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213411_unchanged.txt";
  SeedFile(tmp, "XY");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, code, c, r1, r2, r3;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    code = $ungetc(8'h5A, fd);\n"
          "    c = $fgetc(fd);\n"
          "    $fclose(fd);\n"
          "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    r1 = $fgetc(fd);\n"
          "    r2 = $fgetc(fd);\n"
          "    r3 = $fgetc(fd);\n"
          "    $display(\"c=%0d r1=%0d r2=%0d r3=%0d\", c, r1, r2, r3);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  // The pushed 'Z' was read back, yet the reopened file still holds exactly
  // "XY" -- two bytes, then EOF.
  EXPECT_NE(out.find("c=90 r1=88 r2=89 r3=-1"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// §21.3.4.1: when the push back cannot be performed the result code is EOF
// rather than zero, and $ferror can describe the failure. Pushing EOF itself
// (-1, in real negative-literal syntax) is refused by the stream, driving the
// failure branch deterministically.
TEST(ReadCharacterAtATime, UngetcErrorYieldsEofAndFerrorReportsCause) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213411_pusherr.txt";
  SeedFile(tmp, "PQ");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, code, err;\n"
      "  reg [639:0] s;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    code = $ungetc(-1, fd);\n"
          "    err = $ferror(fd, s);\n"
          "    $display(\"code=%0d errnz=%0d\", code, err != 0);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("code=-1 errnz=1"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// §21.3.4.1: a refused push back inserts nothing -- the guarantee that the
// pushed character is returned by the next $fgetc applies only to a push that
// succeeded, so after a failed push the next read delivers the stream's own
// byte.
TEST(ReadCharacterAtATime, FailedUngetcPushesNothing) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213411_pushnone.txt";
  SeedFile(tmp, "PQ");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, code, c;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    code = $ungetc(-1, fd);\n"
          "    c = $fgetc(fd);\n"
          "    $display(\"code=%0d c=%0d\", code, c);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  // The failed push left the stream untouched: the first read still sees 'P'.
  EXPECT_NE(out.find("code=-1 c=80"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

}  // namespace
