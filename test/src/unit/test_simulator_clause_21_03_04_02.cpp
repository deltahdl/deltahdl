#include <cstdio>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// §21.3.4.2 governs $fgets. It reads characters from a file descriptor into a
// destination variable until the variable is filled, a newline is read (and
// itself transferred), or end-of-file is reached; a packed destination's
// capacity counts only whole bytes; the call returns the count of characters
// read, or zero when an error produced none, with $ferror describing a
// failure. Every rule operates on a descriptor produced by a §21.3.1 $fopen
// and on a destination produced by a declaration, so each test builds both
// from real source syntax and drives the full pipeline.

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

// C1: a newline ends the read and is itself transferred into the variable;
// the characters after it stay in the file, so the next call picks up the
// following line. The returned count includes the newline.
TEST(ReadingALineAtATime, NewlineEndsReadAndIsTransferred) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213402_newline.txt";
  SeedFile(tmp, "Hi\nmore\n");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, c1, c2;\n"
      "  reg [8*16:1] str;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    c1 = $fgets(str, fd);\n"
          "    $display(\"c1=%0d line=[%0s]\", c1, str);\n"
          "    c2 = $fgets(str, fd);\n"
          "    $display(\"c2=%0d line=[%0s]\", c2, str);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("c1=3 line=[Hi\n]"), std::string::npos) << out;
  EXPECT_NE(out.find("c2=5 line=[more\n]"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// C1: filling the destination ends the read mid-line. A 24-bit variable holds
// three characters, so a six-character line arrives across two calls of three
// each, and the trailing newline is left for a third call.
TEST(ReadingALineAtATime, FilledVariableEndsReadAndNextCallResumes) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213402_fill.txt";
  SeedFile(tmp, "ABCDEF\n");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, c1, c2, c3;\n"
      "  reg [23:0] str;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    c1 = $fgets(str, fd);\n"
          "    $display(\"c1=%0d h1=%h\", c1, str);\n"
          "    c2 = $fgets(str, fd);\n"
          "    $display(\"c2=%0d h2=%h\", c2, str);\n"
          "    c3 = $fgets(str, fd);\n"
          "    $display(\"c3=%0d\", c3);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("c1=3 h1=414243"), std::string::npos) << out;  // "ABC"
  EXPECT_NE(out.find("c2=3 h2=444546"), std::string::npos) << out;  // "DEF"
  EXPECT_NE(out.find("c3=1"), std::string::npos) << out;            // "\n"
  std::remove(tmp.c_str());
}

// C2: a declared width that is not a multiple of eight contributes only its
// whole bytes. A 20-bit variable spans two whole bytes plus a partial byte
// that is ignored, so each call reads two characters -- and the second call
// starting exactly at the third character proves the partial byte consumed
// nothing from the stream.
TEST(ReadingALineAtATime, PartialByteDoesNotCountTowardCapacity) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213402_partial.txt";
  SeedFile(tmp, "ABCD");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, c1, c2;\n"
      "  reg [19:0] str;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    c1 = $fgets(str, fd);\n"
          "    $display(\"c1=%0d h1=%0h\", c1, str);\n"
          "    c2 = $fgets(str, fd);\n"
          "    $display(\"c2=%0d h2=%0h\", c2, str);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("c1=2 h1=4142"), std::string::npos) << out;  // "AB"
  EXPECT_NE(out.find("c2=2 h2=4344"), std::string::npos) << out;  // "CD"
  std::remove(tmp.c_str());
}

// C2 (edge): a destination narrower than one byte has no whole bytes, so its
// capacity is zero -- the call reads nothing and returns zero, and the file's
// first character is still there for a byte-wide destination afterward.
TEST(ReadingALineAtATime, SubByteDestinationReadsNothing) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213402_subbyte.txt";
  SeedFile(tmp, "AB");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, c1, c2;\n"
      "  reg [3:0] narrow;\n"
      "  reg [7:0] wide;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    c1 = $fgets(narrow, fd);\n"
          "    c2 = $fgets(wide, fd);\n"
          "    $display(\"c1=%0d c2=%0d wide=%0d\", c1, c2, wide);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("c1=0 c2=1 wide=65"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// C1: a string-typed destination resizes to the line rather than filling, so
// a line longer than the string's prior contents arrives whole; a following
// shorter line replaces it completely. The newline is kept in both.
TEST(ReadingALineAtATime, StringDestinationTakesWholeLine) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213402_string.txt";
  SeedFile(tmp, "HelloWorld\nBye\n");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, c1, c2;\n"
      "  string s;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    c1 = $fgets(s, fd);\n"
          "    $display(\"c1=%0d line=[%0s]\", c1, s);\n"
          "    c2 = $fgets(s, fd);\n"
          "    $display(\"c2=%0d line=[%0s]\", c2, s);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("c1=11 line=[HelloWorld\n]"), std::string::npos) << out;
  EXPECT_NE(out.find("c2=4 line=[Bye\n]"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// C1/C3/C4: a final line without a trailing newline is ended by end-of-file
// and transferred with its true count; a further call at end-of-file returns
// zero -- and $ferror reports no error, because exhaustion is not a failure.
TEST(ReadingALineAtATime, EofEndsReadAndReturnsZeroWithoutError) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213402_eof.txt";
  SeedFile(tmp, "AB");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, c1, c2, err;\n"
      "  reg [8*8:1] str;\n"
      "  reg [639:0] s;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    c1 = $fgets(str, fd);\n"
          "    c2 = $fgets(str, fd);\n"
          "    err = $ferror(fd, s);\n"
          "    $display(\"c1=%0d c2=%0d err=%0d\", c1, c2, err);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("c1=2 c2=0 err=0"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// C3/C4: an error reading -- here a descriptor opened for writing only, which
// §21.3.4 forbids reading -- makes the returned count zero, and $ferror then
// describes the cause of the failed $fgets.
TEST(ReadingALineAtATime, ErrorReturnsZeroAndFerrorReportsCause) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213402_werr.txt";
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, c, err;\n"
      "  reg [8*8:1] str;\n"
      "  reg [639:0] s;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"w\");\n"
          "    c = $fgets(str, fd);\n"
          "    err = $ferror(fd, s);\n"
          "    $display(\"c=%0d errnz=%0d\", c, err != 0);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("c=0 errnz=1"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// C3/C4: reading through a descriptor already closed also yields a zero count
// with a $ferror-visible cause, while a fresh working descriptor reads
// cleanly and reports no error -- separating zero-for-error from
// zero-at-end-of-file.
TEST(ReadingALineAtATime, ClosedDescriptorReturnsZeroAndFreshOneClears) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213402_closed.txt";
  SeedFile(tmp, "ok\n");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, c, err, c2, err2;\n"
      "  reg [8*8:1] str;\n"
      "  reg [639:0] s;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    $fclose(fd);\n"
          "    c = $fgets(str, fd);\n"
          "    err = $ferror(fd, s);\n"
          "    $display(\"c=%0d errnz=%0d\", c, err != 0);\n"
          "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    c2 = $fgets(str, fd);\n"
          "    err2 = $ferror(fd, s);\n"
          "    $display(\"c2=%0d err2=%0d\", c2, err2);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("c=0 errnz=1"), std::string::npos) << out;
  EXPECT_NE(out.find("c2=3 err2=0"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// C3: $fgets is a function, so besides the assignment form of the standard's
// example its count can sit directly in expression-operand position.
TEST(ReadingALineAtATime, CountUsableAsExpressionOperand) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213402_operand.txt";
  SeedFile(tmp, "ab\n");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd;\n"
      "  reg [8*8:1] str;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    if ($fgets(str, fd) == 3) $display(\"operand=match\");\n"
          "    else $display(\"operand=miss\");\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("operand=match"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// C1: a read-update descriptor ("r+") admits line reads just as "r" does --
// the other §21.3.1 open type §21.3.4 permits for reading.
TEST(ReadingALineAtATime, ReadsThroughReadUpdateDescriptor) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213402_rplus.txt";
  SeedFile(tmp, "up\n");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, c;\n"
      "  reg [8*8:1] str;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r+\");\n"
          "    c = $fgets(str, fd);\n"
          "    $display(\"c=%0d line=[%0s]\", c, str);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("c=3 line=[up\n]"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

}  // namespace
