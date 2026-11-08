#include <gtest/gtest.h>

#include <cstdio>
#include <string>

#include "fixture_simulator.h"
#include "helpers_temp_file.h"

using namespace delta;

namespace {

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
  EXPECT_NE(out.find("nz=1"), std::string::npos) << out;
  EXPECT_NE(out.find("open for reading"), std::string::npos) << out;
  std::remove(tmp.c_str());
}

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

TEST(IoErrorStatus, FailedOpenIsReportedOnTheZeroDescriptor) {
  SimFixture f;
  std::string ok_path = "/tmp/deltahdl_t210307_ok.txt";
  std::string out = RunCapture(
      "module t;\n"
      "  integer fd, m, e;\n"
      "  string msg;\n"
      "  initial begin\n"
      "    fd = $fopen(\"/tmp/deltahdl_no_such_dir/none.txt\", \"r\");\n"
      "    e = $ferror(fd, msg);\n"
      "    $display(\"%0d %0d %0d\", fd, e != 0, msg.len() > 0);\n"
      "    m = $fopen(\"/tmp/deltahdl_no_such_dir/mcd.txt\");\n"
      "    e = $ferror(m, msg);\n"
      "    $display(\"%0d %0d\", m, e != 0);\n"
      "    fd = $fopen(\"" +
          ok_path +
          "\", \"w\");\n"
          "    $fwrite(fd, \"x\");\n"
          "    e = $ferror(fd, msg);\n"
          "    $display(\"%0d %0d\", e, msg.len());\n"
          "    $fclose(fd);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "0 1 1\n0 1\n0 0\n");
  std::remove(ok_path.c_str());
}

}  // namespace
