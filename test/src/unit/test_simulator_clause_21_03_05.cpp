#include <cstdio>
#include <fstream>
#include <iostream>
#include <sstream>

#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

// §21.3.5: every positioning rule operates on a descriptor whose behavior is
// decided by how it was produced -- the type argument of the §21.3.1 $fopen
// that created it -- so these tests build the descriptor from real $fopen
// source syntax, drive the whole pipeline, and observe the positioning
// functions' results through $display.

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

// §21.3.5: $ftell returns the offset from the beginning of the file of the
// byte the next operation on the descriptor will read or write -- zero on a
// freshly opened file, and the count of characters consumed after reads.
TEST(FilePositioning, FtellReportsPositionOfNextByte) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_2135_ftell.txt";
  SeedFile(tmp, "abcdef");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, p0, p3, c;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    p0 = $ftell(fd);\n"
          "    c = $fgetc(fd);\n"
          "    c = $fgetc(fd);\n"
          "    c = $fgetc(fd);\n"
          "    p3 = $ftell(fd);\n"
          "    $display(\"p0=%0d p3=%0d\", p0, p3);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("p0=0 p3=3"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// §21.3.5: $ftell equally reports the position of the next byte to be
// WRITTEN -- on a write-type descriptor it advances with each output
// operation.
TEST(FilePositioning, FtellReportsPositionOfNextByteToWrite) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_2135_ftell_write.txt";
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, p3, p5;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"w\");\n"
          "    $fwrite(fd, \"abc\");\n"
          "    p3 = $ftell(fd);\n"
          "    $fwrite(fd, \"de\");\n"
          "    p5 = $ftell(fd);\n"
          "    $display(\"p3=%0d p5=%0d\", p3, p5);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("p3=3 p5=5"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// §21.3.5: a value obtained from $ftell can be handed back to a subsequent
// $fseek to reposition the file to that same point.
TEST(FilePositioning, FtellValueRepositionsThroughFseek) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_2135_ftell_seek.txt";
  SeedFile(tmp, "abcdef");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, saved, r, c;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    c = $fgetc(fd);\n"
          "    c = $fgetc(fd);\n"
          "    saved = $ftell(fd);\n"
          "    c = $fgetc(fd);\n"
          "    c = $fgetc(fd);\n"
          "    r = $fseek(fd, saved, 0);\n"
          "    c = $fgetc(fd);\n"
          "    $display(\"r=%0d c=%c\", r, c);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("r=0 c=c"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// §21.3.5: operation value 0 sets the position to exactly offset bytes from
// the beginning of the file.
TEST(FilePositioning, FseekFromBeginning) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_2135_seek0.txt";
  SeedFile(tmp, "abcdef");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, r, c;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    r = $fseek(fd, 3, 0);\n"
          "    c = $fgetc(fd);\n"
          "    $display(\"r=%0d c=%c\", r, c);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("r=0 c=d"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// §21.3.5: operation value 1 sets the position to the current location plus
// the offset.
TEST(FilePositioning, FseekFromCurrentPosition) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_2135_seek1.txt";
  SeedFile(tmp, "abcdef");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, r, c;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    c = $fgetc(fd);\n"
          "    c = $fgetc(fd);\n"
          "    r = $fseek(fd, 1, 1);\n"
          "    c = $fgetc(fd);\n"
          "    $display(\"r=%0d c=%c\", r, c);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("r=0 c=d"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// §21.3.5: operation value 2 sets the position to EOF plus the offset; the
// offset is a signed distance, so a negative value seeks backward from the
// end of the file.
TEST(FilePositioning, FseekFromEndWithNegativeOffset) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_2135_seek2.txt";
  SeedFile(tmp, "abcdef");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, r, c;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    r = $fseek(fd, -2, 2);\n"
          "    c = $fgetc(fd);\n"
          "    $display(\"r=%0d c=%c\", r, c);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("r=0 c=e"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// §21.3.5: offset and operation are ordinary expressions -- here a parameter
// and a localparam constant supply them, and the offset arrives through a
// variable as well.
TEST(FilePositioning, FseekArgumentsFromConstantsAndVariables) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_2135_seek_forms.txt";
  SeedFile(tmp, "abcdef");
  std::string out = RunCapture(
      "module t;\n"
      "  parameter OFF = -2;\n"
      "  localparam OP_END = 2;\n"
      "  integer fd, off_var, r1, r2, c1, c2;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    r1 = $fseek(fd, OFF, OP_END);\n"
          "    c1 = $fgetc(fd);\n"
          "    off_var = 3;\n"
          "    r2 = $fseek(fd, off_var, 0);\n"
          "    c2 = $fgetc(fd);\n"
          "    $display(\"r1=%0d c1=%c r2=%0d c2=%c\", r1, c1, r2, c2);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("r1=0 c1=e r2=0 c2=d"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// §21.3.5: $fseek changes the position of the next input OR output operation;
// on a read-update ("r+") descriptor a reposition followed by a write
// overwrites the byte at that spot in place.
TEST(FilePositioning, FseekOnReadUpdateDescriptorRepositionsWrite) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_2135_rplus.txt";
  SeedFile(tmp, "abcdef");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, r, c0, c1, c2, c3, c4, c5;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r+\");\n"
          "    r = $fseek(fd, 2, 0);\n"
          "    $fwrite(fd, \"Z\");\n"
          "    $fclose(fd);\n"
          "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    c0 = $fgetc(fd);\n"
          "    c1 = $fgetc(fd);\n"
          "    c2 = $fgetc(fd);\n"
          "    c3 = $fgetc(fd);\n"
          "    c4 = $fgetc(fd);\n"
          "    c5 = $fgetc(fd);\n"
          "    $display(\"r=%0d %c%c%c%c%c%c\", r, c0, c1, c2, c3, c4, c5);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("r=0 abZdef"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// §21.3.5: $rewind is equivalent to $fseek(fd, 0, 0) -- it reports 0 and the
// next read starts over at the first byte.
TEST(FilePositioning, RewindEquivalentToFseekZeroZero) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_2135_rewind.txt";
  SeedFile(tmp, "abcdef");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, r, c;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    c = $fgetc(fd);\n"
          "    c = $fgetc(fd);\n"
          "    r = $rewind(fd);\n"
          "    c = $fgetc(fd);\n"
          "    $display(\"r=%0d c=%c\", r, c);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("r=0 c=a"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// §21.3.5: a repositioning error sets the returned code to -1 -- both for a
// descriptor that cannot be repositioned and for an operation value outside
// 0, 1, and 2 -- while a successful reposition returns 0.
TEST(FilePositioning, FseekReturnsZeroOnSuccessMinusOneOnError) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_2135_seek_code.txt";
  SeedFile(tmp, "abcdef");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, ok, bad_fd, bad_op;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    ok = $fseek(fd, 3, 0);\n"
          "    bad_fd = $fseek(32'h0001_2345, 0, 0);\n"
          "    bad_op = $fseek(fd, 0, 3);\n"
          "    $display(\"ok=%0d bad_fd=%0d bad_op=%0d\", ok, bad_fd, "
          "bad_op);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("ok=0 bad_fd=-1 bad_op=-1"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// §21.3.5: $rewind reports -1 when the reposition fails.
TEST(FilePositioning, RewindReturnsMinusOneOnInvalidDescriptor) {
  SysTaskFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  integer r;\n"
      "  initial begin\n"
      "    r = $rewind(32'h0001_2345);\n"
      "    $display(\"r=%0d\", r);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("r=-1"), std::string::npos) << out;
}

// §21.3.5: when an error occurs, $ftell returns EOF (-1), and the application
// can call the §21.3.7 $ferror function to determine the cause of the most
// recent error.
TEST(FilePositioning, PositioningErrorCauseReportedThroughFerror) {
  SysTaskFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  integer p, e;\n"
      "  reg [639:0] msg;\n"
      "  initial begin\n"
      "    p = $ftell(32'h0001_2345);\n"
      "    e = $ferror(32'h0001_2345, msg);\n"
      "    $display(\"p=%0d nz=%0d has_msg=%0d\", p, e != 0, msg != 0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("p=-1 nz=1 has_msg=1"), std::string::npos) << out;
}

// §21.3.5: repositioning with $fseek shall cancel a pending $ungetc
// push-back -- the next read resumes from the file, not the pushed character.
TEST(FilePositioning, FseekCancelsUngetcPushback) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_2135_seek_ungetc.txt";
  SeedFile(tmp, "abcdef");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, r, c;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    c = $fgetc(fd);\n"
          "    r = $ungetc(\"Z\", fd);\n"
          "    r = $fseek(fd, 0, 0);\n"
          "    c = $fgetc(fd);\n"
          "    $display(\"c=%c\", c);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("c=a"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// §21.3.5: repositioning with $rewind shall likewise cancel a pending $ungetc
// push-back.
TEST(FilePositioning, RewindCancelsUngetcPushback) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_2135_rewind_ungetc.txt";
  SeedFile(tmp, "abcdef");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, r, c;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    c = $fgetc(fd);\n"
          "    r = $ungetc(\"Z\", fd);\n"
          "    r = $rewind(fd);\n"
          "    c = $fgetc(fd);\n"
          "    $display(\"c=%c\", c);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("c=a"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// §21.3.5: the position indicator may be set beyond the end of the existing
// data, but $fseek by itself does not extend the size of the file -- seeking
// back to EOF afterward still finds the original six bytes.
TEST(FilePositioning, FseekBeyondEndDoesNotExtendFile) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_2135_past_eof.txt";
  SeedFile(tmp, "abcdef");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, r, far, at_end;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    r = $fseek(fd, 100, 0);\n"
          "    far = $ftell(fd);\n"
          "    r = $fseek(fd, 0, 2);\n"
          "    at_end = $ftell(fd);\n"
          "    $display(\"far=%0d at_end=%0d\", far, at_end);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("far=100 at_end=6"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// §21.3.5: when data are written at a point beyond the existing end of the
// file, reads of the gap between the old end and that point return zero.
TEST(FilePositioning, GapLeftBySeekPastEndReadsAsZero) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_2135_gap.txt";
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, r, c0, c1, c2, c3, c4;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"w\");\n"
          "    $fwrite(fd, \"AB\");\n"
          "    r = $fseek(fd, 4, 0);\n"
          "    $fwrite(fd, \"Z\");\n"
          "    $fclose(fd);\n"
          "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    c0 = $fgetc(fd);\n"
          "    c1 = $fgetc(fd);\n"
          "    c2 = $fgetc(fd);\n"
          "    c3 = $fgetc(fd);\n"
          "    c4 = $fgetc(fd);\n"
          "    $display(\"%0d %0d %0d %0d %0d\", c0, c1, c2, c3, c4);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("65 66 0 0 90"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// §21.3.5: on a file opened for append, $fseek may move the pointer, but
// written output disregards it -- everything lands at the end of the file and
// the pointer is then repositioned to the end of that output.
TEST(FilePositioning, AppendOutputIgnoresSeekAndLandsAtEnd) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_2135_append.txt";
  SeedFile(tmp, "abc");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, r, after, c0, c1, c2, c3, c4;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"a\");\n"
          "    r = $fseek(fd, 0, 0);\n"
          "    $fwrite(fd, \"XY\");\n"
          "    after = $ftell(fd);\n"
          "    $fclose(fd);\n"
          "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    c0 = $fgetc(fd);\n"
          "    c1 = $fgetc(fd);\n"
          "    c2 = $fgetc(fd);\n"
          "    c3 = $fgetc(fd);\n"
          "    c4 = $fgetc(fd);\n"
          "    $display(\"after=%0d %c%c%c%c%c\", after, c0, c1, c2, c3, c4);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("after=5 abcXY"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// §21.3.5: the append-update type ("a+") shows the same behavior -- output
// written after a reposition still lands at the end of the file.
TEST(FilePositioning, AppendUpdateOutputAlsoLandsAtEnd) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_2135_append_plus.txt";
  SeedFile(tmp, "abc");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, r, c0, c1, c2, c3;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"a+\");\n"
          "    r = $fseek(fd, 0, 0);\n"
          "    $fwrite(fd, \"Q\");\n"
          "    $fclose(fd);\n"
          "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    c0 = $fgetc(fd);\n"
          "    c1 = $fgetc(fd);\n"
          "    c2 = $fgetc(fd);\n"
          "    c3 = $fgetc(fd);\n"
          "    $display(\"%c%c%c%c\", c0, c1, c2, c3);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("abcQ"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

}  // namespace
