#include <gtest/gtest.h>

#include <cstdio>
#include <string>

#include "fixture_simulator.h"
#include "helpers_temp_file.h"

using namespace delta;

namespace {

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
  EXPECT_NE(out.find("c1=88 code=0 c2=90 c3=89"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

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
  EXPECT_NE(out.find("c1=77 code=0 c2=77 c3=78"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

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
  EXPECT_NE(out.find("c=90 r1=88 r2=89 r3=-1"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

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
  EXPECT_NE(out.find("code=-1 c=80"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

TEST(ReadCharacterAtATime, UngetcOfEofOntoAWriteOnlyFdFailsAndPushesNothing) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213411_w_pusheof.txt";
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, code, err, c;\n"
      "  reg [639:0] s;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"w\");\n"
          "    code = $ungetc(-1, fd);\n"
          "    err = $ferror(fd, s);\n"
          "    c = $fgetc(fd);\n"
          "    $display(\"code=%0d errnz=%0d c=%0d\", code, err != 0, c);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("code=-1 errnz=1 c=-1"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

TEST(ReadCharacterAtATime, UngetcOntoAClosedFdFails) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213411_closed_push.txt";
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, code, err;\n"
      "  reg [639:0] s;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"w\");\n"
          "    $fclose(fd);\n"
          "    code = $ungetc(72, fd);\n"
          "    err = $ferror(fd, s);\n"
          "    $display(\"code=%0d errnz=%0d\", code, err != 0);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_NE(out.find("code=-1 errnz=1"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

}  // namespace
