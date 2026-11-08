#include <gtest/gtest.h>

#include <cstdio>
#include <string>

#include "fixture_simulator.h"
#include "helpers_temp_file.h"

using namespace delta;

namespace {

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
