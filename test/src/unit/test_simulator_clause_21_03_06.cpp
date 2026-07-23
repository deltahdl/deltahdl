#include <cstdio>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// §21.3.6 governs $fflush. Its one semantic rule operates on a descriptor
// whose meaning is decided by how it was produced -- the §21.3.1 $fopen that
// created it (two-argument form yields an fd, single-argument form an mcd) --
// so every test builds the descriptor from real $fopen source syntax and
// drives the whole pipeline. The flush is observed by opening a second,
// independent read descriptor on the same path: bytes still sitting in the
// writer's stream buffer are invisible to it, while flushed bytes are read
// back, so a pre-flush read of -1 (EOF) against a post-flush read of the data
// discriminates the flush itself from the write.

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

// Creates `path` holding `content` so an update- or append-type $fopen has an
// existing file to operate on.
static void SeedFile(const std::string& path, const std::string& content) {
  std::ofstream ofs(path, std::ios::binary);
  ofs << content;
}

// §21.3.6: $fflush given a single file descriptor writes that descriptor's
// buffered output to its file. Before the flush an independent reader sees an
// empty file; after it, the written bytes.
TEST(FlushingOutput, FdArgumentPublishesBufferedBytes) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_21306_fd.txt";
  std::remove(tmp.c_str());
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, r1, r2, pre_c, post_c;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"w\");\n"
          "    $fwrite(fd, \"hi\");\n"
          "    r1 = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    pre_c = $fgetc(r1);\n"
          "    $fclose(r1);\n"
          "    $fflush(fd);\n"
          "    r2 = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    post_c = $fgetc(r2);\n"
          "    $fclose(r2);\n"
          "    $display(\"pre=%0d post=%0d\", pre_c, post_c);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("pre=-1 post=104"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// §21.3.6: $fflush given a multichannel descriptor writes the buffered output
// of the file(s) the mcd selects. The single-argument $fopen of §21.3.1 is
// what produces such a descriptor, and flushing it must resolve the set bit to
// its channel's file rather than treating the value as an fd.
TEST(FlushingOutput, McdArgumentPublishesSelectedChannel) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_21306_mcd.txt";
  std::remove(tmp.c_str());
  std::string out = RunCapture(
      "module t;\n"
      "  integer mcd, r1, r2, pre_c, post_c;\n"
      "  initial begin\n"
      "    mcd = $fopen(\"" +
          tmp +
          "\");\n"
          "    $fwrite(mcd, \"M\");\n"
          "    r1 = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    pre_c = $fgetc(r1);\n"
          "    $fclose(r1);\n"
          "    $fflush(mcd);\n"
          "    r2 = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    post_c = $fgetc(r2);\n"
          "    $fclose(r2);\n"
          "    $display(\"pre=%0d post=%0d\", pre_c, post_c);\n"
          "    $fclose(mcd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("pre=-1 post=77"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// §21.3.6: the mcd argument names "the file(s)" it selects -- an mcd built by
// ORing two §21.3.1 channels selects both, and one flush must publish the
// buffered output of each. The ORed value also exercises the argument as a
// computed expression rather than a plain variable.
TEST(FlushingOutput, OredMcdFlushesEverySelectedFile) {
  SysTaskFixture f;
  std::string pa = "/tmp/deltahdl_21306_ora.txt";
  std::string pb = "/tmp/deltahdl_21306_orb.txt";
  std::remove(pa.c_str());
  std::remove(pb.c_str());
  std::string out = RunCapture(
      "module t;\n"
      "  integer m1, m2, ra, rb, ca, cb;\n"
      "  initial begin\n"
      "    m1 = $fopen(\"" +
          pa +
          "\");\n"
          "    m2 = $fopen(\"" +
          pb +
          "\");\n"
          "    $fwrite(m1, \"A\");\n"
          "    $fwrite(m2, \"B\");\n"
          "    $fflush(m1 | m2);\n"
          "    ra = $fopen(\"" +
          pa +
          "\", \"r\");\n"
          "    ca = $fgetc(ra);\n"
          "    $fclose(ra);\n"
          "    rb = $fopen(\"" +
          pb +
          "\", \"r\");\n"
          "    cb = $fgetc(rb);\n"
          "    $fclose(rb);\n"
          "    $display(\"ca=%0d cb=%0d\", ca, cb);\n"
          "    $fclose(m1);\n"
          "    $fclose(m2);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("ca=65 cb=66"), std::string::npos) << out;
  std::remove(pa.c_str());
  std::remove(pb.c_str());
}

// §21.3.6: invoked with no arguments, $fflush writes the buffered output of
// all open files -- here one opened as an fd and one as an mcd, neither named
// by the call.
TEST(FlushingOutput, NoArgumentFlushesAllOpenFiles) {
  SysTaskFixture f;
  std::string pa = "/tmp/deltahdl_21306_all_fd.txt";
  std::string pb = "/tmp/deltahdl_21306_all_mcd.txt";
  std::remove(pa.c_str());
  std::remove(pb.c_str());
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, mcd, ra, rb, ca, cb;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          pa +
          "\", \"w\");\n"
          "    mcd = $fopen(\"" +
          pb +
          "\");\n"
          "    $fwrite(fd, \"F\");\n"
          "    $fwrite(mcd, \"G\");\n"
          "    $fflush();\n"
          "    ra = $fopen(\"" +
          pa +
          "\", \"r\");\n"
          "    ca = $fgetc(ra);\n"
          "    $fclose(ra);\n"
          "    rb = $fopen(\"" +
          pb +
          "\", \"r\");\n"
          "    cb = $fgetc(rb);\n"
          "    $fclose(rb);\n"
          "    $display(\"ca=%0d cb=%0d\", ca, cb);\n"
          "    $fclose(fd);\n"
          "    $fclose(mcd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("ca=70 cb=71"), std::string::npos) << out;
  std::remove(pa.c_str());
  std::remove(pb.c_str());
}

// §21.3.6 negative-adjacent form: an mcd of zero selects no channels, so the
// flush must publish nothing -- discriminating the with-argument form from a
// flush-all. Only the later flush that names the fd makes the bytes visible.
TEST(FlushingOutput, EmptyMcdSelectsNoFiles) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_21306_empty.txt";
  std::remove(tmp.c_str());
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, r1, r2, pre_c, post_c;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"w\");\n"
          "    $fwrite(fd, \"Q\");\n"
          "    $fflush(0);\n"
          "    r1 = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    pre_c = $fgetc(r1);\n"
          "    $fclose(r1);\n"
          "    $fflush(fd);\n"
          "    r2 = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    post_c = $fgetc(r2);\n"
          "    $fclose(r2);\n"
          "    $display(\"pre=%0d post=%0d\", pre_c, post_c);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("pre=-1 post=81"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// §21.3.6 negative form: a value carrying the fd high bit but naming no open
// file resolves to no stream. The flush publishes nothing (another channel's
// buffered byte stays invisible) and the run continues normally.
TEST(FlushingOutput, UnopenedFdFlushesNothingAndIsHarmless) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_21306_stale.txt";
  std::remove(tmp.c_str());
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, r1, pre_c;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"w\");\n"
          "    $fwrite(fd, \"Q\");\n"
          "    $fflush(32'h8000_0005);\n"
          "    r1 = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    pre_c = $fgetc(r1);\n"
          "    $fclose(r1);\n"
          "    $display(\"pre=%0d alive=1\", pre_c);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("pre=-1 alive=1"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// §21.3.6: flushing writes the buffered output without disturbing the stream
// -- the descriptor stays open at its position, so writes may continue and a
// second flush publishes the later bytes after the earlier ones. Also drives
// the descriptor through an int (rather than integer) variable.
TEST(FlushingOutput, StreamRemainsUsableAfterFlush) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_21306_resume.txt";
  std::remove(tmp.c_str());
  std::string out = RunCapture(
      "module t;\n"
      "  int fd;\n"
      "  integer r, c1, c2, c3, c4;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"w\");\n"
          "    $fwrite(fd, \"ab\");\n"
          "    $fflush(fd);\n"
          "    $fwrite(fd, \"cd\");\n"
          "    $fflush(fd);\n"
          "    r = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    c1 = $fgetc(r);\n"
          "    c2 = $fgetc(r);\n"
          "    c3 = $fgetc(r);\n"
          "    c4 = $fgetc(r);\n"
          "    $fclose(r);\n"
          "    $display(\"c=%0d %0d %0d %0d\", c1, c2, c3, c4);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("c=97 98 99 100"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// §21.3.6: the fd argument admits a descriptor of any open type, not only the
// write type -- here a read-update ("r+") descriptor whose in-place overwrite
// sits in the buffer. An independent reader still sees the seeded bytes before
// the flush and the overwritten bytes after it.
TEST(FlushingOutput, ReadUpdateDescriptorPublishesOnFlush) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_21306_rplus.txt";
  SeedFile(tmp, "ab");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, r1, r2, pre_c, post_c;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r+\");\n"
          "    $fwrite(fd, \"XY\");\n"
          "    r1 = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    pre_c = $fgetc(r1);\n"
          "    $fclose(r1);\n"
          "    $fflush(fd);\n"
          "    r2 = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    post_c = $fgetc(r2);\n"
          "    $fclose(r2);\n"
          "    $display(\"pre=%0d post=%0d\", pre_c, post_c);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("pre=97 post=88"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// §21.3.6: an append-type descriptor is likewise a valid fd argument. Its
// writes land at the end of the file, and flushing it completes without
// disturbing the stream -- the appended byte follows the seeded ones.
TEST(FlushingOutput, AppendDescriptorFlushCompletes) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_21306_append.txt";
  SeedFile(tmp, "ab");
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, r, c1, c2, c3;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"a\");\n"
          "    $fwrite(fd, \"c\");\n"
          "    $fflush(fd);\n"
          "    r = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    c1 = $fgetc(r);\n"
          "    c2 = $fgetc(r);\n"
          "    c3 = $fgetc(r);\n"
          "    $fclose(r);\n"
          "    $display(\"c=%0d %0d %0d\", c1, c2, c3);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("c=97 98 99"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

// §21.3.6: the descriptor argument is an ordinary expression, so it can come
// from an array element rather than a scalar variable; the flush publishes the
// bytes written through that same element.
TEST(FlushingOutput, ArrayElementExpressionArgument) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_21306_elem.txt";
  std::remove(tmp.c_str());
  std::string out = RunCapture(
      "module t;\n"
      "  integer fds [0:1];\n"
      "  integer r, c;\n"
      "  initial begin\n"
      "    fds[0] = $fopen(\"" +
          tmp +
          "\", \"w\");\n"
          "    $fwrite(fds[0], \"E\");\n"
          "    $fflush(fds[0]);\n"
          "    r = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    c = $fgetc(r);\n"
          "    $fclose(r);\n"
          "    $display(\"c=%0d\", c);\n"
          "    $fclose(fds[0]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("c=69"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

}  // namespace
