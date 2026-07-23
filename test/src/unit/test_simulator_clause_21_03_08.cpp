#include <cstdio>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// §21.3.8 governs $feof. Its single rule is stateful: the function yields
// nonzero only when a read on the descriptor has previously detected
// end-of-file. That state depends entirely on how the descriptor was produced
// (§21.3.1 $fopen) and which reads ran against it (§21.3.4.1 $fgetc,
// §21.3.4.2 $fgets, §21.3.4.3 $fscanf, §21.3.4.4 $fread), so every test
// builds the descriptor and the reads from real source syntax and drives the
// whole pipeline, observing $feof through $display.

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

// §21.3.8: before any read has run, no end-of-file can have been detected, so
// $feof yields zero on a freshly opened descriptor.
TEST(DetectingEof, FeofZeroBeforeAnyRead) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_21308_fresh.txt";
  SeedFile(tmp, "data\n");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, e;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    e = $feof(fd);\n"
          "    $display(\"e=%0d\", e);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("e=0"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// §21.3.8: nonzero is reported only after end-of-file "has previously been
// detected reading" -- consuming the last byte leaves the position at the end
// but no read has yet come up short, so $feof still yields zero; only the
// following failed $fgetc flips it to nonzero.
TEST(DetectingEof, FeofZeroAtEndUntilAReadFails) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_21308_lastbyte.txt";
  SeedFile(tmp, "x");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, c, e1, e2;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    c = $fgetc(fd);\n"
          "    e1 = $feof(fd);\n"
          "    c = $fgetc(fd);\n"
          "    e2 = $feof(fd);\n"
          "    $display(\"e1=%0d e2n=%0d\", e1, e2 != 0);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("e1=0 e2n=1"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// §21.3.8 with §21.3.4.2: a $fgets that delivers a full line stops at the
// newline without touching end-of-file; the next $fgets finds nothing, and
// that failed read is what makes $feof report nonzero.
TEST(DetectingEof, FeofNonzeroAfterFgetsExhaustsFile) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_21308_fgets.txt";
  SeedFile(tmp, "hi\n");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, n, e1, e2;\n"
      "  reg [8*8:1] line;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    n = $fgets(line, fd);\n"
          "    e1 = $feof(fd);\n"
          "    n = $fgets(line, fd);\n"
          "    e2 = $feof(fd);\n"
          "    $display(\"n=%0d e1=%0d e2n=%0d\", n, e1, e2 != 0);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("n=0 e1=0 e2n=1"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// §21.3.8 with §21.3.4.3: the canonical read loop -- $feof guarding $fscanf in
// expression-operand position -- terminates. The scan that runs out of input
// detects end-of-file even though $fscanf repositions the host stream
// internally, so the guard observes it. The bounded for-loop keeps a
// regression from hanging the test instead of failing it: two values convert,
// the third scan returns EOF, and the guard stops the loop on its next test.
TEST(DetectingEof, FeofGuardedFscanfLoopTerminates) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_21308_loop.txt";
  SeedFile(tmp, "1\n2\n");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, r, v, n, guard;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    n = 0;\n"
          "    guard = 0;\n"
          "    while (!$feof(fd) && guard < 5) begin\n"
          "      r = $fscanf(fd, \"%d\", v);\n"
          "      if (r == 1) n = n + 1;\n"
          "      guard = guard + 1;\n"
          "    end\n"
          "    $display(\"n=%0d guard=%0d\", n, guard);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("n=2 guard=3"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// §21.3.8 with §21.3.4.3: a numeric conversion is delimiter-terminated, so
// converting a final token that has no trailing newline forces a look one
// character past the field -- that look detects end-of-file even though the
// conversion itself succeeded.
TEST(DetectingEof, FeofNonzeroAfterFscanfReadsFinalUnterminatedToken) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_21308_notrail.txt";
  SeedFile(tmp, "7");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, r, v, e;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    r = $fscanf(fd, \"%d\", v);\n"
          "    e = $feof(fd);\n"
          "    $display(\"r=%0d v=%0d en=%0d\", r, v, e != 0);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("r=1 v=7 en=1"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// §21.3.8 with §21.3.4.3: %c takes exactly the characters it asks for and
// never looks past them, so a scan whose %c consumes the final byte has not
// detected end-of-file -- $feof stays zero, distinguishing detection from
// mere position, through the buffered $fscanf path as well.
TEST(DetectingEof, FeofZeroAfterFscanfExactCharTakesLastByte) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_21308_exactc.txt";
  SeedFile(tmp, "A");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, r, e;\n"
      "  reg [7:0] ch;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    r = $fscanf(fd, \"%c\", ch);\n"
          "    e = $feof(fd);\n"
          "    $display(\"r=%0d ch=%0d e=%0d\", r, ch, e);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("r=1 ch=65 e=0"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// §21.3.8 with §21.3.4.4: a $fread that fills its destination from the
// remaining bytes succeeds; the next $fread transfers nothing, and that
// failed read is what $feof reports.
TEST(DetectingEof, FeofNonzeroAfterFreadPastEnd) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_21308_fread.bin";
  SeedFile(tmp, "Q");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, r1, r2, e;\n"
      "  reg [7:0] b;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    r1 = $fread(b, fd);\n"
          "    r2 = $fread(b, fd);\n"
          "    e = $feof(fd);\n"
          "    $display(\"r1=%0d r2=%0d en=%0d\", r1, r2, e != 0);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("r1=1 r2=0 en=1"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// §21.3.8: the detection is stream state, not a permanent mark. After a
// buffered $fscanf detects end-of-file, repositioning re-enables reading:
// $rewind returns $feof to zero and the value converts again; a second
// detection is then cleared the same way by $fseek to the start.
TEST(DetectingEof, FeofClearedByRepositioningAfterFscanfDetection) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_21308_rewind.txt";
  SeedFile(tmp, "5");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, r, v, e1, e2, e3, e4;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    r = $fscanf(fd, \"%d\", v);\n"
          "    e1 = $feof(fd);\n"
          "    r = $rewind(fd);\n"
          "    e2 = $feof(fd);\n"
          "    r = $fscanf(fd, \"%d\", v);\n"
          "    e3 = $feof(fd);\n"
          "    r = $fseek(fd, 0, 0);\n"
          "    e4 = $feof(fd);\n"
          "    $display(\"e1n=%0d e2=%0d e3n=%0d e4=%0d v=%0d\",\n"
          "             e1 != 0, e2, e3 != 0, e4, v);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("e1n=1 e2=0 e3n=1 e4=0 v=5"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// §21.3.8 against §21.3.7: a refused read on a write-only descriptor is an
// error, not an end-of-file detection -- no read ever came up short against
// the data, so $feof stays zero while $ferror has something to report.
TEST(DetectingEof, FeofZeroOnWriteOnlyDescriptorAfterRefusedRead) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_21308_wonly.txt";
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, c, e;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"w\");\n"
          "    c = $fgetc(fd);\n"
          "    e = $feof(fd);\n"
          "    $display(\"cn=%0d e=%0d\", c == -1, e);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("cn=1 e=0"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// §21.3.8 Syntax 21-11: the fd operand is an expression. The descriptor here
// reaches $feof through an arithmetic expression rather than a bare variable,
// and the detection state reads the same both before and after the failed
// read that flips it.
TEST(DetectingEof, FeofFdArgumentAsExpression) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_21308_fdexpr.txt";
  SeedFile(tmp, "k");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, c, e1, e2;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    e1 = $feof(fd + 1 - 1);\n"
          "    c = $fgetc(fd);\n"
          "    c = $fgetc(fd);\n"
          "    e2 = $feof(fd + 1 - 1);\n"
          "    $display(\"e1=%0d e2n=%0d\", e1, e2 != 0);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("e1=0 e2n=1"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// §21.3.8 Syntax 21-11: the fd operand may be a function-call result -- the
// descriptor flows straight from the §21.3.1 opening call into the detection
// function. A descriptor no read has ever touched reports zero.
TEST(DetectingEof, FeofOnDescriptorStraightFromFopen) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_21308_direct.txt";
  SeedFile(tmp, "d");
  std::string out = RunCapture(
      "module t;\n"
      "  integer e;\n"
      "  initial begin\n"
      "    e = $feof($fopen(\"" +
          tmp +
          "\", \"r\"));\n"
          "    $display(\"e=%0d\", e);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("e=0"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// §21.3.8 boundary: a closed descriptor can never deliver another byte, so
// $feof reads it as end-of-file. This keeps the canonical
// `while (!$feof(fd))` guard from spinning forever on a dead descriptor.
TEST(DetectingEof, FeofNonzeroOnClosedDescriptor) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_21308_closed.txt";
  SeedFile(tmp, "z");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, e;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    $fclose(fd);\n"
          "    e = $feof(fd);\n"
          "    $display(\"en=%0d\", e != 0);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("en=1"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

}  // namespace
