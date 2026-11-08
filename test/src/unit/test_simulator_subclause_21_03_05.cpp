#include <gtest/gtest.h>

#include <cstdio>

#include "fixture_simulator.h"
#include "helpers_temp_file.h"

using namespace delta;

namespace {

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

TEST(FilePositioning, FseekCancelsAWriteOnlyFdsPushBack) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_2135_seek_ungetc_w.txt";
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, u, s, c;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"w\");\n"
          "    u = $ungetc(\"Z\", fd);\n"
          "    s = $fseek(fd, 0, 0);\n"
          "    c = $fgetc(fd);\n"
          "    $display(\"u=%0d s=%0d c=%0d\", u, s, c);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("u=0 s=0 c=-1"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

TEST(FilePositioning, RewindCancelsAWriteOnlyFdsPushBack) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_2135_rewind_ungetc_w.txt";
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, u, s, c;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"w\");\n"
          "    u = $ungetc(\"Z\", fd);\n"
          "    s = $rewind(fd);\n"
          "    c = $fgetc(fd);\n"
          "    $display(\"u=%0d s=%0d c=%0d\", u, s, c);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("u=0 s=0 c=-1"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

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
