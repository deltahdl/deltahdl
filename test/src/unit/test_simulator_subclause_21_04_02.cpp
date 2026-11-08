#include <gtest/gtest.h>

#include <cstdio>
#include <fstream>
#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

std::string WriteData(const std::string& tag, const std::string& data) {
  std::string path = "/tmp/deltahdl_t210402_" + tag + ".mem";
  std::ofstream ofs(path);
  ofs << data;
  ofs.close();
  return path;
}

TEST(Readmem2StateSim, BitVectorBinaryXZDigitsBecomeZero) {
  SimFixture f;
  std::string path = WriteData("bvec", "1010\n1x0z\n");
  std::string out = RunCapture(
      "module t;\n"
      "  bit [3:0] mem [0:1];\n"
      "  initial begin\n"
      "    $readmemb(\"" +
          path +
          "\", mem);\n"
          "    $display(\"%b %b\", mem[0], mem[1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "1010 1000\n");
  std::remove(path.c_str());
}

TEST(Readmem2StateSim, IntHexXZDigitsBecomeZero) {
  SimFixture f;
  std::string path = WriteData("int", "3x\nzA\n");
  std::string out = RunCapture(
      "module t;\n"
      "  int mem [0:1];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem);\n"
          "    $display(\"%h %h\", mem[0], mem[1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "00000030 0000000a\n");
  std::remove(path.c_str());
}

TEST(Readmem2StateSim, UppercaseAndUnderscoreFormsConvert) {
  SimFixture f;
  std::string path = WriteData("case", "1_x1\nZ0X1\n");
  std::string out = RunCapture(
      "module t;\n"
      "  bit [3:0] mem [0:1];\n"
      "  initial begin\n"
      "    $readmemb(\"" +
          path +
          "\", mem);\n"
          "    $display(\"%b %b\", mem[0], mem[1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "0101 0001\n");
  std::remove(path.c_str());
}

TEST(Readmem2StateSim, ShortintElementConvertsXZ) {
  SimFixture f;
  std::string path = WriteData("shortint", "12x4\nz_FF\n");
  std::string out = RunCapture(
      "module t;\n"
      "  shortint mem [0:1];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem);\n"
          "    $display(\"%h %h\", mem[0], mem[1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "1204 00ff\n");
  std::remove(path.c_str());
}

TEST(Readmem2StateSim, LongintElementConvertsXZAtWordEdges) {
  SimFixture f;
  std::string path = WriteData("longint", "x23456789ABCDEFz\n");
  std::string out = RunCapture(
      "module t;\n"
      "  longint mem [0:0];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem);\n"
          "    $display(\"%h\", mem[0]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "023456789abcdef0\n");
  std::remove(path.c_str());
}

TEST(Readmem2StateSim, FourStateElementRetainsXZ) {
  SimFixture f;
  std::string path = WriteData("logic", "1010\n1x0z\n");
  std::string out = RunCapture(
      "module t;\n"
      "  logic [3:0] mem [0:1];\n"
      "  initial begin\n"
      "    $readmemb(\"" +
          path +
          "\", mem);\n"
          "    $display(\"%b %b\", mem[0], mem[1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "1010 1x0z\n");
  std::remove(path.c_str());
}

TEST(Readmem2StateSim, QueueOfIntConvertsXZ) {
  SimFixture f;
  std::string path = WriteData("queue", "5x\nX_2\n");
  std::string out = RunCapture(
      "module t;\n"
      "  int q [$];\n"
      "  initial begin\n"
      "    q.push_back(32'hFF);\n"
      "    q.push_back(32'hFF);\n"
      "    $readmemh(\"" +
          path +
          "\", q);\n"
          "    $display(\"%h %h\", q[0], q[1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "00000050 00000002\n");
  std::remove(path.c_str());
}

TEST(Readmem2StateSim, DynamicArrayOfByteConvertsXZ) {
  SimFixture f;
  std::string path = WriteData("dyn", "5x\nX_2\n");
  std::string out = RunCapture(
      "module t;\n"
      "  byte mem [];\n"
      "  initial begin\n"
      "    mem = new[2];\n"
      "    $readmemh(\"" +
          path +
          "\", mem);\n"
          "    $display(\"%h %h\", mem[0], mem[1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "50 02\n");
  std::remove(path.c_str());
}

TEST(Readmem2StateSim, AssocArrayOfIntConvertsXZ) {
  SimFixture f;
  std::string path = WriteData("assoc", "3x\nz7\n");
  std::string out = RunCapture(
      "module t;\n"
      "  int aa [int];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", aa);\n"
          "    $display(\"%h %h\", aa[0], aa[1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "00000030 00000007\n");
  std::remove(path.c_str());
}

TEST(Readmem2StateSim, WideElementConvertsXZAboveBitSixtyThree) {
  SimFixture f;
  std::string path = WriteData("wide", "x5_00000000_00000003\n");
  std::string out = RunCapture(
      "module t;\n"
      "  bit [71:0] mem [0:0];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem);\n"
          "    $display(\"%h\", mem[0]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "050000000000000003\n");
  std::remove(path.c_str());
}

TEST(Readmem2StateSim, EnumDefaultValuesLoadNumerically) {
  SimFixture f;
  std::string path = WriteData("enum", "0\n2\n1\n");
  std::string out = RunCapture(
      "module t;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  color_t mem [0:2];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem);\n"
          "    $display(\"%0d %0d %0d\", mem[0], mem[1], mem[2]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(out, "0 2 1\n");
  std::remove(path.c_str());
}

TEST(Readmem2StateSim, EnumExplicitValuesLoadNumerically) {
  SimFixture f;
  std::string path = WriteData("enumex", "4\n1\n");
  std::string out = RunCapture(
      "module t;\n"
      "  typedef enum bit [2:0] {A = 1, B = 4} sparse_t;\n"
      "  sparse_t mem [0:1];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem);\n"
          "    $display(\"%0d %0d\", mem[0], mem[1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(out, "4 1\n");
  std::remove(path.c_str());
}

TEST(Readmem2StateSim, EnumBinaryTaskLoadsNumerically) {
  SimFixture f;
  std::string path = WriteData("enumb", "010\n001\n");
  std::string out = RunCapture(
      "module t;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  color_t mem [0:1];\n"
      "  initial begin\n"
      "    $readmemb(\"" +
          path +
          "\", mem);\n"
          "    $display(\"%0d %0d\", mem[0], mem[1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(out, "2 1\n");
  std::remove(path.c_str());
}

TEST(Readmem2StateSim, XIntoEnumCollapsesToZeroValuedElement) {
  SimFixture f;
  std::string path = WriteData("enumx", "x\n1\n");
  std::string out = RunCapture(
      "module t;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  color_t mem [0:1];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem);\n"
          "    $display(\"%0d %0d\", mem[0], mem[1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(out, "0 1\n");
  std::remove(path.c_str());
}

TEST(Readmem2StateSim, InlineEnumDeclarationLoadsNumerically) {
  SimFixture f;
  std::string path = WriteData("enumin", "1\n0\n");
  std::string out = RunCapture(
      "module t;\n"
      "  enum {OFF, ON} mem [0:1];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem);\n"
          "    $display(\"%0d %0d\", mem[0], mem[1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(out, "1 0\n");
  std::remove(path.c_str());
}

TEST(Readmem2StateSim, OutOfRangeEnumValueErrorsAndStopsReading) {
  SimFixture f;
  std::string path = WriteData("oor", "1\n5\n2\n");
  std::string out = RunCapture(
      "module t;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  color_t mem [0:2];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem);\n"
          "    $display(\"%0d %0d %0d\", mem[0], mem[1], mem[2]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "value out of range for the enumerated type", 5,
                            "21.4.2"));
  EXPECT_EQ(out, "1 0 0\n");
  std::remove(path.c_str());
}

TEST(Readmem2StateSim, SparseGapValueIsOutOfRange) {
  SimFixture f;
  std::string path = WriteData("gap", "2\n");
  std::string out = RunCapture(
      "module t;\n"
      "  typedef enum bit [2:0] {A = 1, B = 4} sparse_t;\n"
      "  sparse_t mem [0:0];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem);\n"
          "    $display(\"%0d\", mem[0]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "value out of range for the enumerated type", 5,
                            "21.4.2"));
  EXPECT_EQ(out, "0\n");
  std::remove(path.c_str());
}

TEST(Readmem2StateSim, OutOfRangeEnumValueNames21_4_2) {
  SimFixture f;
  std::string path = WriteData("oor_sub", "0\n7\n");
  RunCapture(
      "module t;\n"
      "  typedef enum {LO, MID, HI} lvl_t;\n"
      "  lvl_t mem [0:1];\n"
      "  initial $readmemh(\"" +
          path +
          "\", mem);\n"
          "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "value out of range for the enumerated type", 4,
                            "21.4.2"));
  std::remove(path.c_str());
}

}  // namespace
