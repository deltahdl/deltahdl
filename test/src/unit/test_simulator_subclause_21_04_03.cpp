#include <gtest/gtest.h>

#include <cstdio>
#include <fstream>
#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_temp_file.h"

using namespace delta;

namespace {

std::string WriteData(const std::string& tag, const std::string& data) {
  std::string path = "/tmp/deltahdl_t21403_" + tag + ".mem";
  std::ofstream ofs(path);
  ofs << data;
  ofs.close();
  return path;
}

TEST(ReadmemMultiDimSim, RowMajorLowestDimensionVariesFastest) {
  SimFixture f;
  std::string path = WriteData("rowmajor", "11\n22\n33\n44\n");
  std::string out = RunCapture(
      "module t;\n"
      "  bit [7:0] mem [0:1][0:1];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem);\n"
          "    $display(\"%h %h %h %h\", mem[0][0], mem[0][1], mem[1][0], "
          "mem[1][1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "11 22 33 44\n");
  std::remove(path.c_str());
}

TEST(ReadmemMultiDimSim, ThreeDimensionalHierarchicalOrder) {
  SimFixture f;
  std::string path = WriteData("threed", "01\n02\n03\n04\n05\n06\n07\n08\n");
  std::string out = RunCapture(
      "module t;\n"
      "  bit [7:0] mem [0:1][0:1][5:6];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem);\n"
          "    $display(\"%h %h %h %h %h %h %h %h\",\n"
          "             mem[0][0][5], mem[0][0][6], mem[0][1][5], "
          "mem[0][1][6],\n"
          "             mem[1][0][5], mem[1][0][6], mem[1][1][5], "
          "mem[1][1][6]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "01 02 03 04 05 06 07 08\n");
  std::remove(path.c_str());
}

TEST(ReadmemMultiDimSim, DeclarationDirectionDoesNotAffectLayout) {
  SimFixture f;
  std::string path = WriteData("revdims", "11\n22\n33\n44\n");
  std::string out = RunCapture(
      "module t;\n"
      "  bit [7:0] fwd [0:1][5:6];\n"
      "  bit [7:0] rev [1:0][6:5];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", fwd);\n"
          "    $readmemh(\"" +
          path +
          "\", rev);\n"
          "    $display(\"%h %h %h %h\", fwd[0][5], fwd[0][6], fwd[1][5], "
          "fwd[1][6]);\n"
          "    $display(\"%h %h %h %h\", rev[0][5], rev[0][6], rev[1][5], "
          "rev[1][6]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "11 22 33 44\n11 22 33 44\n");
  std::remove(path.c_str());
}

TEST(ReadmemMultiDimSim, SingleReversedDimensionSameLayout) {
  SimFixture f;
  std::string path = WriteData("onerev", "11\n22\n33\n44\n");
  std::string out = RunCapture(
      "module t;\n"
      "  bit [7:0] fwd [0:1][5:6];\n"
      "  bit [7:0] mix [1:0][5:6];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", fwd);\n"
          "    $readmemh(\"" +
          path +
          "\", mix);\n"
          "    $display(\"%h %h %h %h\", fwd[0][5], fwd[0][6], fwd[1][5], "
          "fwd[1][6]);\n"
          "    $display(\"%h %h %h %h\", mix[0][5], mix[0][6], mix[1][5], "
          "mix[1][6]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "11 22 33 44\n11 22 33 44\n");
  std::remove(path.c_str());
}

TEST(ReadmemMultiDimSim, ReadmembFillsRowMajor) {
  SimFixture f;
  std::string path =
      WriteData("binary", "00000001\n00000010\n00000011\n00000100\n");
  std::string out = RunCapture(
      "module t;\n"
      "  bit [7:0] mem [0:1][0:1];\n"
      "  initial begin\n"
      "    $readmemb(\"" +
          path +
          "\", mem);\n"
          "    $display(\"%0d %0d %0d %0d\", mem[0][0], mem[0][1], mem[1][0], "
          "mem[1][1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "1 2 3 4\n");
  std::remove(path.c_str());
}

TEST(ReadmemMultiDimSim, IncompleteFileLeavesRemainderUnchanged) {
  SimFixture f;
  std::string path = WriteData("incomplete", "11\n22\n33\n");
  std::string out = RunCapture(
      "module t;\n"
      "  bit [7:0] mem [0:1][0:1];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem);\n"
          "    $display(\"%h %h %h %h\", mem[0][0], mem[0][1], mem[1][0], "
          "mem[1][1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "11 22 33 00\n");
  std::remove(path.c_str());
}

TEST(ReadmemMultiDimSim, IncompleteFileFourStateRemainderKeepsX) {
  SimFixture f;
  std::string path = WriteData("incomplete4s", "11\n22\n33\n");
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] mem [0:1][0:1];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem);\n"
          "    $display(\"%h %h %h %h\", mem[0][0], mem[0][1], mem[1][0], "
          "mem[1][1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "11 22 33 xx\n");
  std::remove(path.c_str());
}

TEST(ReadmemMultiDimSim, OneDimensionalBackwardCompatible) {
  SimFixture f;
  std::string path = WriteData("onedim", "11\n22\n@3\n44\n");
  std::string out = RunCapture(
      "module t;\n"
      "  bit [7:0] mem [0:3];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem);\n"
          "    $display(\"%h %h %h %h\", mem[0], mem[1], mem[2], mem[3]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "11 22 00 44\n");
  std::remove(path.c_str());
}

TEST(ReadmemMultiDimSim, MultipleAddressEntriesRepositionWords) {
  SimFixture f;
  std::string path = WriteData("multi_addr", "@2\n55\n66\n@0\n11\n22\n");
  std::string out = RunCapture(
      "module t;\n"
      "  bit [7:0] mem [0:2][0:1];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem);\n"
          "    $display(\"%h %h %h %h %h %h\", mem[0][0], mem[0][1],\n"
          "             mem[1][0], mem[1][1], mem[2][0], mem[2][1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "11 22 00 00 55 66\n");
  std::remove(path.c_str());
}

TEST(ReadmemMultiDimSim, AddressEntryHonorsNonzeroHighestDimLow) {
  SimFixture f;
  std::string path = WriteData("addr_nzlo", "@2\naa\nbb\n");
  std::string out = RunCapture(
      "module t;\n"
      "  bit [7:0] mem [1:2][0:1];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem);\n"
          "    $display(\"%h %h %h %h\", mem[1][0], mem[1][1], mem[2][0], "
          "mem[2][1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "00 00 aa bb\n");
  std::remove(path.c_str());
}

TEST(ReadmemMultiDimSim, AddressedWordInsufficientDataLeavesSubwords) {
  SimFixture f;
  std::string path = WriteData("addr_partial", "@1\naa\n");
  std::string out = RunCapture(
      "module t;\n"
      "  bit [7:0] mem [0:1][0:1];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem);\n"
          "    $display(\"%h %h %h %h\", mem[0][0], mem[0][1], mem[1][0], "
          "mem[1][1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "00 00 aa 00\n");
  std::remove(path.c_str());
}

TEST(ReadmemMultiDimSim, AddressedWordUnderfillFourStateKeepsX) {
  SimFixture f;
  std::string path = WriteData("addr_partial4s", "@1\naa\n");
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] mem [0:1][0:1];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem);\n"
          "    $display(\"%h %h %h %h\", mem[0][0], mem[0][1], mem[1][0], "
          "mem[1][1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "xx xx aa xx\n");
  std::remove(path.c_str());
}

TEST(ReadmemMultiDimSim, AddressBeyondHighestDimensionIsError) {
  SimFixture f;
  std::string path = WriteData("addr_oob", "@5\naa\n");
  std::string out = RunCapture(
      "module t;\n"
      "  bit [7:0] mem [0:1][0:1];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem);\n"
          "    $display(\"%h %h\", mem[0][0], mem[1][1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "file address outside the highest dimension's range", 4, "21.4.3"));
  EXPECT_EQ(out, "00 00\n");
  std::remove(path.c_str());
}

TEST(ReadmemMultiDimSim, PackedDimensionsComposeFullFileWord) {
  SimFixture f;
  std::string path = WriteData("packed", "dead\nbeef\n0001\nf00d\n");
  std::string out = RunCapture(
      "module t;\n"
      "  logic [1:0][7:0] mem [0:1][0:1];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem);\n"
          "    $display(\"%h %h %h %h\", mem[0][0], mem[0][1], mem[1][0], "
          "mem[1][1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "dead beef 0001 f00d\n");
  std::remove(path.c_str());
}

TEST(ReadmemMultiDimSim, PartiallyIndexedSubArrayFillsRowMajor) {
  SimFixture f;
  std::string path = WriteData("partial_idx", "11\n22\n33\n44\n");
  std::string out = RunCapture(
      "module t;\n"
      "  bit [7:0] mem [0:1][0:1][0:1];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem[1]);\n"
          "    $display(\"%h %h %h %h %h\", mem[1][0][0], mem[1][0][1],\n"
          "             mem[1][1][0], mem[1][1][1], mem[0][0][0]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "11 22 33 44 00\n");
  std::remove(path.c_str());
}

TEST(ReadmemMultiDimSim, WritememhDumpsMultiDimRowMajor) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t21403_wdump.mem";
  RunCapture(
      "module t;\n"
      "  bit [7:0] mem [0:1][0:1];\n"
      "  initial begin\n"
      "    mem[0][0] = 8'h11; mem[0][1] = 8'h22;\n"
      "    mem[1][0] = 8'h33; mem[1][1] = 8'h44;\n"
      "    $writememh(\"" +
          std::string(path) +
          "\", mem);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(SlurpFile(path), "11\n22\n33\n44\n");
  std::remove(path.c_str());
}

TEST(ReadmemMultiDimSim, WritememRoundTripReloadsReversedDeclaration) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t21403_wround.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  bit [7:0] src [0:1][0:1];\n"
      "  bit [7:0] dst [1:0][1:0];\n"
      "  initial begin\n"
      "    src[0][0] = 8'h11; src[0][1] = 8'h22;\n"
      "    src[1][0] = 8'h33; src[1][1] = 8'h44;\n"
      "    $writememb(\"" +
          std::string(path) +
          "\", src);\n"
          "    $readmemb(\"" +
          std::string(path) +
          "\", dst);\n"
          "    $display(\"%h %h %h %h\", dst[0][0], dst[0][1], dst[1][0], "
          "dst[1][1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "11 22 33 44\n");
  std::remove(path.c_str());
}

TEST(ReadmemMultiDimSim, WritememhThreeDimensionalRowMajor) {
  SimFixture f;
  std::string src_path =
      WriteData("w3d_in", "01\n02\n03\n04\n05\n06\n07\n08\n");
  std::string path = "/tmp/deltahdl_t21403_w3d.mem";
  RunCapture(
      "module t;\n"
      "  bit [7:0] mem [0:1][0:1][5:6];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          src_path +
          "\", mem);\n"
          "    $writememh(\"" +
          std::string(path) +
          "\", mem);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(SlurpFile(path), "01\n02\n03\n04\n05\n06\n07\n08\n");
  std::remove(src_path.c_str());
  std::remove(path.c_str());
}

TEST(ReadmemMultiDimSim, AddressBeyondHighestDimensionNames21_4_3) {
  SimFixture f;
  std::string path = WriteData("addr_sub", "@9\nbb\n");
  RunCapture(
      "module t;\n"
      "  bit [7:0] mem [0:2][0:1];\n"
      "  initial $readmemh(\"" +
          path +
          "\", mem);\n"
          "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "outside the highest dimension's range", 3,
                            "21.4.3"));
  std::remove(path.c_str());
}

}  // namespace
