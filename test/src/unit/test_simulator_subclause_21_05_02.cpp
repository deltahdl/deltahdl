#include <gtest/gtest.h>

#include <cstdio>
#include <string>

#include "fixture_simulator.h"
#include "helpers_temp_file.h"

using namespace delta;

namespace {

TEST(WritememTwoStateSim, IntArrayWrittenAsPlainNumbers) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210502_int.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  int src [0:2];\n"
      "  int dst [0:2];\n"
      "  initial begin\n"
      "    src[0] = 42; src[1] = -1; src[2] = 32'hDEADBEEF;\n"
      "    $writememh(\"" +
          path +
          "\", src);\n"
          "    $readmemh(\"" +
          path +
          "\", dst);\n"
          "    $display(\"%h %h %h\", dst[0], dst[1], dst[2]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "0000002a ffffffff deadbeef\n");
  EXPECT_EQ(SlurpFile(path), "0000002a\nffffffff\ndeadbeef\n");
  std::remove(path.c_str());
}

TEST(WritememTwoStateSim, NarrowAndWideIntegerTypesWrittenAtTypeWidth) {
  SimFixture f;
  std::string path_b = "/tmp/deltahdl_t210502_byte.mem";
  std::string path_s = "/tmp/deltahdl_t210502_short.mem";
  std::string path_l = "/tmp/deltahdl_t210502_long.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  byte bsrc [0:1];\n"
      "  shortint ssrc [0:1];\n"
      "  longint lsrc [0:1];\n"
      "  longint ldst [0:1];\n"
      "  initial begin\n"
      "    bsrc[0] = 8'h2A; bsrc[1] = 8'hF0;\n"
      "    $writememh(\"" +
          path_b +
          "\", bsrc);\n"
          "    ssrc[0] = 16'hBEEF; ssrc[1] = 16'h0001;\n"
          "    $writememh(\"" +
          path_s +
          "\", ssrc);\n"
          "    lsrc[0] = 64'hFEDCBA9876543210; lsrc[1] = 64'h1;\n"
          "    $writememh(\"" +
          path_l +
          "\", lsrc);\n"
          "    $readmemh(\"" +
          path_l +
          "\", ldst);\n"
          "    $display(\"%h %h\", ldst[0], ldst[1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "fedcba9876543210 0000000000000001\n");
  EXPECT_EQ(SlurpFile(path_b), "2a\nf0\n");
  EXPECT_EQ(SlurpFile(path_s), "beef\n0001\n");
  EXPECT_EQ(SlurpFile(path_l), "fedcba9876543210\n0000000000000001\n");
  std::remove(path_b.c_str());
  std::remove(path_s.c_str());
  std::remove(path_l.c_str());
}

TEST(WritememTwoStateSim, BitVectorArrayWrittenPerBitByWritememb) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210502_bits.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  bit [7:0] src [0:1];\n"
      "  bit [7:0] dst [0:1];\n"
      "  initial begin\n"
      "    src[0] = 8'b10100101; src[1] = 8'b00001111;\n"
      "    $writememb(\"" +
          path +
          "\", src);\n"
          "    $readmemb(\"" +
          path +
          "\", dst);\n"
          "    $display(\"%b %b\", dst[0], dst[1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "10100101 00001111\n");
  EXPECT_EQ(SlurpFile(path), "10100101\n00001111\n");
  std::remove(path.c_str());
}

TEST(WritememTwoStateSim, DefaultTwoStateArrayWritesZerosNeverFourStateDigits) {
  SimFixture f;
  std::string path_h = "/tmp/deltahdl_t210502_zh.mem";
  std::string path_b = "/tmp/deltahdl_t210502_zb.mem";
  RunCapture(
      "module t;\n"
      "  int zmem [0:1];\n"
      "  initial begin\n"
      "    $writememh(\"" +
          path_h +
          "\", zmem);\n"
          "    $writememb(\"" +
          path_b +
          "\", zmem);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(SlurpFile(path_h), "00000000\n00000000\n");
  EXPECT_EQ(SlurpFile(path_b),
            "00000000000000000000000000000000\n"
            "00000000000000000000000000000000\n");
  std::remove(path_h.c_str());
  std::remove(path_b.c_str());
}

TEST(WritememTwoStateSim, WideTwoStateElementWrittenWhole) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210502_wide.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  bit [71:0] src [0:0];\n"
      "  bit [71:0] dst [0:0];\n"
      "  initial begin\n"
      "    src[0] = 72'hAB_CDEF0123_456789AB;\n"
      "    $writememh(\"" +
          path +
          "\", src);\n"
          "    $readmemh(\"" +
          path +
          "\", dst);\n"
          "    $display(\"%h\", dst[0]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "abcdef0123456789ab\n");
  EXPECT_EQ(SlurpFile(path), "abcdef0123456789ab\n");
  std::remove(path.c_str());
}

TEST(WritememTwoStateSim, TwoStateQueueAndDynamicArrayWritten) {
  SimFixture f;
  std::string path_q = "/tmp/deltahdl_t210502_q.mem";
  std::string path_d = "/tmp/deltahdl_t210502_d.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  int q [$];\n"
      "  int d [];\n"
      "  int dst [0:1];\n"
      "  initial begin\n"
      "    q.push_back(7); q.push_back(8);\n"
      "    $writememh(\"" +
          path_q +
          "\", q);\n"
          "    d = new[2]; d[0] = 3; d[1] = 4;\n"
          "    $writememh(\"" +
          path_d +
          "\", d);\n"
          "    $readmemh(\"" +
          path_q +
          "\", dst);\n"
          "    $display(\"%0d %0d\", dst[0], dst[1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "7 8\n");
  EXPECT_EQ(SlurpFile(path_q), "00000007\n00000008\n");
  EXPECT_EQ(SlurpFile(path_d), "00000003\n00000004\n");
  std::remove(path_q.c_str());
  std::remove(path_d.c_str());
}

TEST(WritememTwoStateSim, EnumArrayWritesOrdinalValues) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210502_enum.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  typedef enum int {RED=2, GREEN=5, BLUE=9} color_e;\n"
      "  color_e src [0:2];\n"
      "  color_e dst [0:2];\n"
      "  initial begin\n"
      "    src[0] = GREEN; src[1] = RED; src[2] = BLUE;\n"
      "    $writememh(\"" +
          path +
          "\", src);\n"
          "    $readmemh(\"" +
          path +
          "\", dst);\n"
          "    $display(\"%0d %0d %0d\", dst[0], dst[1], dst[2]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "5 2 9\n");
  EXPECT_EQ(SlurpFile(path), "00000005\n00000002\n00000009\n");
  std::remove(path.c_str());
}

TEST(WritememTwoStateSim, EnumAutoOrdinalsFollowDeclarationOrder) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210502_auto.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  typedef enum {ALPHA, BETA, GAMMA} abc_e;\n"
      "  abc_e src [0:2];\n"
      "  abc_e dst [0:2];\n"
      "  initial begin\n"
      "    src[0] = GAMMA; src[1] = ALPHA; src[2] = BETA;\n"
      "    $writememh(\"" +
          path +
          "\", src);\n"
          "    $readmemh(\"" +
          path +
          "\", dst);\n"
          "    $display(\"%0d %0d %0d\", dst[0], dst[1], dst[2]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "2 0 1\n");
  EXPECT_EQ(SlurpFile(path), "00000002\n00000000\n00000001\n");
  std::remove(path.c_str());
}

TEST(WritememTwoStateSim, EnumArrayWritemembWritesOrdinalBits) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210502_enumb.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  typedef enum int {RED=2, GREEN=5, BLUE=9} color_e;\n"
      "  color_e src [0:2];\n"
      "  color_e dst [0:2];\n"
      "  initial begin\n"
      "    src[0] = GREEN; src[1] = RED; src[2] = BLUE;\n"
      "    $writememb(\"" +
          path +
          "\", src);\n"
          "    $readmemb(\"" +
          path +
          "\", dst);\n"
          "    $display(\"%0d %0d %0d\", dst[0], dst[1], dst[2]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "5 2 9\n");
  EXPECT_EQ(SlurpFile(path),
            "00000000000000000000000000000101\n"
            "00000000000000000000000000000010\n"
            "00000000000000000000000000001001\n");
  std::remove(path.c_str());
}

}  // namespace
