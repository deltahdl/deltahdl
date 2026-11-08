#include <gtest/gtest.h>

#include <cstdio>
#include <string>

#include "fixture_simulator.h"
#include "helpers_temp_file.h"

using namespace delta;

namespace {

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
