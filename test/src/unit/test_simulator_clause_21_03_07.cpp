#include <cstdio>
#include <fstream>
#include <iostream>
#include <sstream>

#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

// §21.3.7: $ferror reports on the most recent file I/O operation, so what it
// returns is decided entirely by how the descriptor was produced (the §21.3.1
// $fopen type) and which operation ran last (a §21.3.4 read or a §21.3.5
// reposition). These tests therefore build that history from real source
// syntax, drive the whole pipeline, and observe $ferror through $display.

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

// §21.3.7: when the most recent operation did not result in an error, the
// value returned shall be zero and the str variable shall be cleared -- a
// previously populated destination must not keep stale characters.
TEST(IoErrorStatus, ReturnsZeroAndClearsStrWhenNoError) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_2137_clear.txt";
  SeedFile(tmp, "ok");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, c, e;\n"
      "  reg [639:0] msg;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    msg = \"stale text\";\n"
          "    c = $fgetc(fd);\n"
          "    e = $ferror(fd, msg);\n"
          "    $display(\"e=%0d cleared=%0d\", e, msg == 0);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("e=0 cleared=1"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// §21.3.7: when the most recent operation failed -- here a §21.3.4 read
// refused on a descriptor opened for writing -- $ferror returns a nonzero
// error code and writes a textual description of the error into str.
TEST(IoErrorStatus, ReportsRefusedReadWithDescription) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_2137_refused.txt";
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, c, e;\n"
      "  reg [639:0] msg;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"w\");\n"
          "    c = $fgetc(fd);\n"
          "    e = $ferror(fd, msg);\n"
          "    $display(\"c=%0d nz=%0d msg=%0s\", c, e != 0, msg);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("c=-1 nz=1"), std::string::npos) << out;
  EXPECT_NE(out.find("not open for reading"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// §21.3.7: a failed §21.3.5 reposition (an operation value outside 0..2) is
// also an error of the most recent file I/O operation, reported by $ferror
// with its own description.
TEST(IoErrorStatus, ReportsInvalidSeekOperation) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_2137_badop.txt";
  SeedFile(tmp, "abc");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, r, e;\n"
      "  reg [639:0] msg;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    r = $fseek(fd, 0, 3);\n"
          "    e = $ferror(fd, msg);\n"
          "    $display(\"r=%0d nz=%0d msg=%0s\", r, e != 0, msg);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("r=-1 nz=1"), std::string::npos) << out;
  EXPECT_NE(out.find("operation"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// §21.3.7: the str destination may be a string-typed variable rather than a
// packed array; the description is stored with its own length.
TEST(IoErrorStatus, WritesDescriptionIntoStringTypedVariable) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_2137_strvar.txt";
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, c, e;\n"
      "  string msg;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"w\");\n"
          "    c = $fgetc(fd);\n"
          "    e = $ferror(fd, msg);\n"
          "    $display(\"nz=%0d msg=%0s\", e != 0, msg);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("nz=1"), std::string::npos) << out;
  EXPECT_NE(out.find("not open for reading"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// §21.3.7: the standard recommends at least 640 bits for a packed str
// destination, but a narrower one is still an accepted destination -- the
// description is coerced to the declared width, keeping its trailing
// characters, rather than being dropped.
TEST(IoErrorStatus, NarrowPackedDestinationReceivesTruncatedDescription) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_2137_narrow.txt";
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, c, e;\n"
      "  reg [127:0] msg;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"w\");\n"
          "    c = $fgetc(fd);\n"
          "    e = $ferror(fd, msg);\n"
          "    $display(\"nz=%0d msg=%0s\", e != 0, msg);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  // 128 bits hold sixteen characters: the tail of the full description.
  EXPECT_NE(out.find("nz=1"), std::string::npos) << out;
  EXPECT_NE(out.find("open for reading"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// §21.3.7: clearing on success applies to a string-typed destination too -- a
// stale value assigned earlier is emptied, not merely overwritten in part.
TEST(IoErrorStatus, ClearsStringTypedDestinationWhenNoError) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_2137_clear_str.txt";
  SeedFile(tmp, "ok");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, c, e;\n"
      "  string msg;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    msg = \"stale\";\n"
          "    c = $fgetc(fd);\n"
          "    e = $ferror(fd, msg);\n"
          "    $display(\"e=%0d msg=[%0s]\", e, msg);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("e=0 msg=[]"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// §21.3.7: only the most recent operation counts -- a successful §21.3.5
// reposition after a failed one leaves no error to report: the code returns
// to zero and the str variable is cleared of the earlier description.
TEST(IoErrorStatus, SuccessfulOperationSupersedesEarlierError) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_2137_supersede.txt";
  SeedFile(tmp, "abc");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, r1, r2, e;\n"
      "  reg [639:0] msg;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    r1 = $fseek(fd, 0, 3);\n"
          "    r2 = $fseek(fd, 0, 0);\n"
          "    e = $ferror(fd, msg);\n"
          "    $display(\"r1=%0d r2=%0d e=%0d cleared=%0d\", r1, r2, e,\n"
          "             msg == 0);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("r1=-1 r2=0 e=0 cleared=1"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

}  // namespace
