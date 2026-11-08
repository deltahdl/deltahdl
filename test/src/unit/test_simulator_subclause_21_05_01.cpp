#include <gtest/gtest.h>

#include <cstdio>
#include <string>

#include "fixture_simulator.h"
#include "helpers_temp_file.h"

using namespace delta;

namespace {

TEST(WritememPackedDataSim, PackedVectorElementWrittenAsWholeWord) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210501_vec.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  logic [15:0] src [0:1];\n"
      "  logic [15:0] dst [0:1];\n"
      "  initial begin\n"
      "    src[0] = 16'hABCD; src[1] = 16'h1234;\n"
      "    $writememh(\"" +
          path +
          "\", src);\n"
          "    $readmemh(\"" +
          path +
          "\", dst);\n"
          "    $display(\"%h %h\", dst[0], dst[1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "abcd 1234\n");
  EXPECT_EQ(SlurpFile(path), "abcd\n1234\n");
  std::remove(path.c_str());
}

TEST(WritememPackedDataSim, PackedStructElementWrittenAsVectorEquivalent) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210501_pstruct.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  typedef struct packed { logic [3:0] hi; logic [11:0] lo; } st_t;\n"
      "  st_t src [0:1];\n"
      "  st_t dst [0:1];\n"
      "  initial begin\n"
      "    src[0] = 16'hABCD; src[1] = 16'h1234;\n"
      "    $writememh(\"" +
          path +
          "\", src);\n"
          "    $readmemh(\"" +
          path +
          "\", dst);\n"
          "    $display(\"%h %h\", dst[0], dst[1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "abcd 1234\n");
  EXPECT_EQ(SlurpFile(path), "abcd\n1234\n");
  std::remove(path.c_str());
}

TEST(WritememPackedDataSim, MultiDimPackedElementWrittenAsFlatVector) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210501_mdp.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  logic [1:0][7:0] src [0:1];\n"
      "  logic [1:0][7:0] dst [0:1];\n"
      "  initial begin\n"
      "    src[0] = 16'hBEEF; src[1] = 16'hCAFE;\n"
      "    $writememh(\"" +
          path +
          "\", src);\n"
          "    $readmemh(\"" +
          path +
          "\", dst);\n"
          "    $display(\"%h %h\", dst[0], dst[1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "beef cafe\n");
  EXPECT_EQ(SlurpFile(path), "beef\ncafe\n");
  std::remove(path.c_str());
}

TEST(WritememPackedDataSim, WidePackedElementWrittenWhole) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210501_wide.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  logic [79:0] src [0:0];\n"
      "  logic [79:0] dst [0:0];\n"
      "  initial begin\n"
      "    src[0] = 80'h0123456789ABCDEF0123;\n"
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
  EXPECT_EQ(out, "0123456789abcdef0123\n");
  EXPECT_EQ(SlurpFile(path), "0123456789abcdef0123\n");
  std::remove(path.c_str());
}

TEST(WritememPackedDataSim, PackedRangeVariantsWrittenAtDeclaredWidth) {
  SimFixture f;
  std::string path_r = "/tmp/deltahdl_t210501_rng.mem";
  std::string path_a = "/tmp/deltahdl_t210501_asc.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  logic [11:4] rsrc [0:1];\n"
      "  logic [11:4] rdst [0:1];\n"
      "  logic [0:15] asrc [0:1];\n"
      "  logic [0:15] adst [0:1];\n"
      "  initial begin\n"
      "    rsrc[0] = 8'hA5; rsrc[1] = 8'h5A;\n"
      "    $writememh(\"" +
          path_r +
          "\", rsrc);\n"
          "    $readmemh(\"" +
          path_r +
          "\", rdst);\n"
          "    asrc[0] = 16'hF00D; asrc[1] = 16'h0DDC;\n"
          "    $writememh(\"" +
          path_a +
          "\", asrc);\n"
          "    $readmemh(\"" +
          path_a +
          "\", adst);\n"
          "    $display(\"%h %h %h %h\", rdst[0], rdst[1], adst[0], adst[1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "a5 5a f00d 0ddc\n");
  EXPECT_EQ(SlurpFile(path_r), "a5\n5a\n");
  EXPECT_EQ(SlurpFile(path_a), "f00d\n0ddc\n");
  std::remove(path_r.c_str());
  std::remove(path_a.c_str());
}

TEST(WritememPackedDataSim, WritemembEmitsPerBitFourStateDigits) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210501_b4.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] src [0:0];\n"
      "  logic [7:0] dst [0:0];\n"
      "  initial begin\n"
      "    src[0] = 8'b10xz1001;\n"
      "    $writememb(\"" +
          path +
          "\", src);\n"
          "    $readmemb(\"" +
          path +
          "\", dst);\n"
          "    $display(\"%b\", dst[0]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "10xz1001\n");
  EXPECT_EQ(SlurpFile(path), "10xz1001\n");
  std::remove(path.c_str());
}

TEST(WritememPackedDataSim, WritememhEmitsWholeDigitUnknownAndHighZ) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210501_h4.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  logic [15:0] src [0:0];\n"
      "  logic [15:0] dst [0:0];\n"
      "  initial begin\n"
      "    src[0] = 16'hax_z5;\n"
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
  EXPECT_EQ(out, "axz5\n");
  EXPECT_EQ(SlurpFile(path), "axz5\n");
  std::remove(path.c_str());
}

TEST(WritememPackedDataSim, MixedUnknownNibbleDegradesToReadableDigit) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210501_mix.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] src [0:0];\n"
      "  logic [7:0] dst [0:0];\n"
      "  initial begin\n"
      "    src[0] = 8'b1x0z0101;\n"
      "    $writememh(\"" +
          path +
          "\", src);\n"
          "    $readmemh(\"" +
          path +
          "\", dst);\n"
          "    $display(\"%b\", dst[0]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "xxxx0101\n");
  EXPECT_EQ(SlurpFile(path), "X5\n");
  std::remove(path.c_str());
}

TEST(WritememPackedDataSim, QueueOfPackedElementsWrittenAsWholeWords) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210501_queue.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  logic [15:0] q [$];\n"
      "  logic [15:0] dst [0:1];\n"
      "  initial begin\n"
      "    q.push_back(16'hABCD); q.push_back(16'h1234);\n"
      "    $writememh(\"" +
          path +
          "\", q);\n"
          "    $readmemh(\"" +
          path +
          "\", dst);\n"
          "    $display(\"%h %h\", dst[0], dst[1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "abcd 1234\n");
  EXPECT_EQ(SlurpFile(path), "abcd\n1234\n");
  std::remove(path.c_str());
}

}  // namespace
