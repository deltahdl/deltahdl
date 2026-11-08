#include <gtest/gtest.h>

#include <cstdio>
#include <string>

#include "fixture_simulator.h"
#include "helpers_temp_file.h"

using namespace delta;

namespace {

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
  EXPECT_NE(out.find("c1=3 h1=414243"), std::string::npos) << out;
  EXPECT_NE(out.find("c2=3 h2=444546"), std::string::npos) << out;
  EXPECT_NE(out.find("c3=1"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

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
  EXPECT_NE(out.find("c1=2 h1=4142"), std::string::npos) << out;
  EXPECT_NE(out.find("c2=2 h2=4344"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

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

TEST(ReadingALineAtATime, FgetsDestinationWakesAnEventControlOnIt) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_213402_event.txt";
  SeedFile(tmp, "Hi\n");
  auto* var = RunAndFindVar(
      "module t;\n"
      "  integer fd, c, hits;\n"
      "  reg [8*16:1] str;\n"
      "  always @(str) hits = hits + 1;\n"
      "  initial begin\n"
      "    hits = 0;\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    #1 c = $fgets(str, fd);\n"
          "    $fclose(fd);\n"
          "    #1 $finish;\n"
          "  end\n"
          "endmodule\n",
      f, "hits");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
  std::remove(tmp.c_str());
}

TEST(ReadingALineAtATime, FgetsIntoFormalsAndClassProperties) {
  SimFixture f;
  std::string tmp = "/tmp/deltahdl_213402_props.txt";
  SeedFile(tmp, "hello\nagain\nthird\nfourth\n");
  std::string out = RunCapture(
      "module t;\n"
      "  class Rd;\n"
      "    string line;\n"
      "    logic [23:0] w;\n"
      "    function void get(integer fd); void'($fgets(line, fd)); "
      "endfunction\n"
      "  endclass\n"
      "  Rd r = new;\n"
      "  task automatic readline(integer fd, output string o);\n"
      "    void'($fgets(o, fd));\n"
      "  endtask\n"
      "  integer fd;\n"
      "  string got;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
          tmp +
          "\", \"r\");\n"
          "    readline(fd, got);\n"
          "    $write(\"%s\", got);\n"
          "    void'($fgets(r.line, fd));\n"
          "    $write(\"%s\", r.line);\n"
          "    r.get(fd);\n"
          "    $write(\"%s\", r.line);\n"
          "    void'($fgets(r.w, fd));\n"
          "    $display(\"%s\", r.w);\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "hello\nagain\nthird\nfou\n");
  std::remove(tmp.c_str());
}

}  // namespace
