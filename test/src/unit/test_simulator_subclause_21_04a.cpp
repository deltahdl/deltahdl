#include <gtest/gtest.h>

#include <cstdio>
#include <fstream>
#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

std::string WriteData(const std::string& tag, const std::string& data) {
  std::string path = "/tmp/deltahdl_t2104_" + tag + ".mem";
  std::ofstream ofs(path);
  ofs << data;
  ofs.close();
  return path;
}

TEST(ReadmemFileLoadSim, ReadmemhLoadsSuccessiveWords) {
  SimFixture f;
  std::string path = WriteData("succ_h", "0A\n14\n1E\n");
  std::string out = RunCapture(
      "module t;\n"
      "  reg [7:0] mem [0:7];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem);\n"
          "    $display(\"%h %h %h\", mem[0], mem[1], mem[2]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "0a 14 1e\n");
  std::remove(path.c_str());
}

TEST(ReadmemFileLoadSim, ReadmembReadsBinaryNumbers) {
  SimFixture f;
  std::string path = WriteData("succ_b", "1010\n0110\n");
  std::string out = RunCapture(
      "module t;\n"
      "  reg [7:0] mem [0:7];\n"
      "  initial begin\n"
      "    $readmemb(\"" +
          path +
          "\", mem);\n"
          "    $display(\"%0d %0d\", mem[0], mem[1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "10 6\n");
  std::remove(path.c_str());
}

TEST(ReadmemFileLoadSim, CommentsAndWhitespaceSeparateNumbers) {
  SimFixture f;
  std::string path = WriteData(
      "comments", "// leading line comment\n0A /* inline */ 14\n\t1E    1F\n");
  std::string out = RunCapture(
      "module t;\n"
      "  reg [7:0] mem [0:7];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem);\n"
          "    $display(\"%h %h %h %h\", mem[0], mem[1], mem[2], mem[3]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "0a 14 1e 1f\n");
  std::remove(path.c_str());
}

TEST(ReadmemFileLoadSim, HexNumberAcceptsUnknownHighZAndUnderscore) {
  SimFixture f;
  std::string path = WriteData("xzu_h", "Ax z5 1_F\n");
  std::string out = RunCapture(
      "module t;\n"
      "  reg [7:0] mem [0:3];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem);\n"
          "    $display(\"%h %h %h\", mem[0], mem[1], mem[2]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "ax z5 1f\n");
  std::remove(path.c_str());
}

TEST(ReadmemFileLoadSim, BinaryNumberAcceptsUnknownAndUnderscore) {
  SimFixture f;
  std::string path = WriteData("xzu_b", "10x1\n1_0_1\n");
  std::string out = RunCapture(
      "module t;\n"
      "  reg [7:0] mem [0:3];\n"
      "  initial begin\n"
      "    $readmemb(\"" +
          path +
          "\", mem);\n"
          "    $display(\"%b %b\", mem[0], mem[1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "000010x1 00000101\n");
  std::remove(path.c_str());
}

TEST(ReadmemFileLoadSim, AtAddressRepositionsCursor) {
  SimFixture f;
  std::string path = WriteData("at", "@2\nAA\nBB\n");
  std::string out = RunCapture(
      "module t;\n"
      "  reg [7:0] mem [0:7];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem);\n"
          "    $display(\"%h %h %h %h\", mem[0], mem[1], mem[2], mem[3]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "xx xx aa bb\n");
  std::remove(path.c_str());
}

TEST(ReadmemFileLoadSim, AtAddressAcceptsUpperAndLowerHexDigits) {
  SimFixture f;
  std::string path = WriteData("at_hex", "@0a\nAA\n@1B\nBB\n");
  std::string out = RunCapture(
      "module t;\n"
      "  reg [7:0] mem [0:63];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem);\n"
          "    $display(\"%h %h\", mem[10], mem[27]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "aa bb\n");
  std::remove(path.c_str());
}

TEST(ReadmemFileLoadSim, MultipleAtAddresses) {
  SimFixture f;
  std::string path = WriteData("at_multi", "@2\nAA\n@5\nBB\n");
  std::string out = RunCapture(
      "module t;\n"
      "  reg [7:0] mem [0:7];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem);\n"
          "    $display(\"%h %h %h\", mem[2], mem[3], mem[5]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "aa xx bb\n");
  std::remove(path.c_str());
}

TEST(ReadmemFileLoadSim, DefaultStartIsLowestAddressUpward) {
  SimFixture f;
  std::string path = WriteData("default", "01\n02\n");
  std::string out = RunCapture(
      "module t;\n"
      "  reg [7:0] mem [1:4];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem);\n"
          "    $display(\"%h %h %h %h\", mem[1], mem[2], mem[3], mem[4]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "01 02 xx xx\n");
  std::remove(path.c_str());
}

TEST(ReadmemFileLoadSim, StartAddressOnlyLoadsUpward) {
  SimFixture f;
  std::string path = WriteData("start_only", "AA\nBB\n");
  std::string out = RunCapture(
      "module t;\n"
      "  reg [7:0] mem [0:7];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem, 4);\n"
          "    $display(\"%h %h %h\", mem[3], mem[4], mem[5]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "xx aa bb\n");
  std::remove(path.c_str());
}

TEST(ReadmemFileLoadSim, StartGreaterThanFinishLoadsDownward) {
  SimFixture f;
  std::string path = WriteData("down", "11\n22\n33\n44\n");
  std::string out = RunCapture(
      "module t;\n"
      "  reg [7:0] mem [0:7];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem, 5, 2);\n"
          "    $display(\"%h %h %h %h\", mem[5], mem[4], mem[3], mem[2]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "11 22 33 44\n");
  EXPECT_EQ(f.diag.WarningCount(), 0u);
  std::remove(path.c_str());
}

TEST(ReadmemFileLoadSim, DownwardDirectionPersistsAfterAtAddress) {
  SimFixture f;
  std::string path = WriteData("dir_down", "@5\nAA\nBB\n");
  std::string out = RunCapture(
      "module t;\n"
      "  reg [7:0] mem [0:7];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem, 7, 0);\n"
          "    $display(\"%h %h\", mem[5], mem[4]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "aa bb\n");
  std::remove(path.c_str());
}

TEST(ReadmemFileLoadSim, UpwardDirectionPersistsAfterAtAddress) {
  SimFixture f;
  std::string path = WriteData("dir_up", "@3\nAA\nBB\n");
  std::string out = RunCapture(
      "module t;\n"
      "  reg [7:0] mem [0:7];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem, 1);\n"
          "    $display(\"%h %h\", mem[3], mem[4]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "aa bb\n");
  std::remove(path.c_str());
}

TEST(ReadmemFileLoadSim, FileAddressOutsideTaskRangeIsError) {
  SimFixture f;
  std::string path = WriteData("oob_addr", "@9\nAA\n");
  std::string out = RunCapture(
      "module t;\n"
      "  reg [7:0] mem [0:15];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem, 2, 5);\n"
          "    $display(\"%h\", mem[9]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "file address outside the range given by the task",
                            4, "21.4"));
  EXPECT_EQ(out, "xx\n");
  std::remove(path.c_str());
}

TEST(ReadmemFileLoadSim, WordCountMismatchWarnsAndLeavesGapUnmodified) {
  SimFixture f;
  std::string path = WriteData("mismatch", "AA\nBB\n");
  std::string out = RunCapture(
      "module t;\n"
      "  reg [7:0] mem [0:7];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem, 1, 4);\n"
          "    $display(\"%h %h %h %h\", mem[1], mem[2], mem[3], mem[4]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_GE(f.diag.WarningCount(), 1u);
  EXPECT_EQ(out, "aa bb xx xx\n");
  std::remove(path.c_str());
}

TEST(ReadmemFileLoadSim, MatchingWordCountDrawsNoWarning) {
  SimFixture f;
  std::string path = WriteData("match", "AA\nBB\nCC\nDD\n");
  std::string out = RunCapture(
      "module t;\n"
      "  reg [7:0] mem [0:7];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem, 1, 4);\n"
          "    $display(\"%h %h\", mem[1], mem[4]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
  EXPECT_EQ(out, "aa dd\n");
  std::remove(path.c_str());
}

TEST(ReadmemFileLoadSim, FilenameFromStringVariable) {
  SimFixture f;
  std::string path = WriteData("str_fn", "07\n");
  std::string out = RunCapture(
      "module t;\n"
      "  string s;\n"
      "  reg [7:0] mem [0:3];\n"
      "  initial begin\n"
      "    s = \"" +
          path +
          "\";\n"
          "    $readmemh(s, mem);\n"
          "    $display(\"%h\", mem[0]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "07\n");
  std::remove(path.c_str());
}

TEST(ReadmemFileLoadSim, FilenameFromIntegralValue) {
  SimFixture f;
  std::string path = WriteData("int_fn", "07\n");
  std::string out = RunCapture(
      "module t;\n"
      "  reg [255:0] fn;\n"
      "  reg [7:0] mem [0:3];\n"
      "  initial begin\n"
      "    fn = \"" +
          path +
          "\";\n"
          "    $readmemh(fn, mem);\n"
          "    $display(\"%h\", mem[0]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "07\n");
  std::remove(path.c_str());
}

TEST(ReadmemFileLoadSim, SliceMemoryNameConfinesLoad) {
  SimFixture f;
  std::string path = WriteData("slice", "AA\nBB\nCC\nDD\nEE\n");
  std::string out = RunCapture(
      "module t;\n"
      "  reg [7:0] mem [0:15];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem[4:7]);\n"
          "    $display(\"%h %h %h\", mem[4], mem[7], mem[8]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "aa dd xx\n");
  std::remove(path.c_str());
}

TEST(ReadmemFileLoadSim, SliceStartFinishWithinBoundsLoads) {
  SimFixture f;
  std::string path = WriteData("slice_win", "11\n22\n33\n44\n");
  std::string out = RunCapture(
      "module t;\n"
      "  reg [7:0] mem [0:15];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem[4:7], 7, 4);\n"
          "    $display(\"%h %h\", mem[7], mem[4]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(out, "11 44\n");
  std::remove(path.c_str());
}

TEST(ReadmemFileLoadSim, SliceStartOutsideBoundsIsError) {
  SimFixture f;
  std::string path = WriteData("slice_oob", "11\n22\n");
  std::string out = RunCapture(
      "module t;\n"
      "  reg [7:0] mem [0:15];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem[4:7], 2, 7);\n"
          "    $display(\"%h\", mem[4]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "start/finish address outside the slice bounds", 4,
                            "21.4"));
  EXPECT_EQ(out, "xx\n");
  std::remove(path.c_str());
}

TEST(ReadmemFileLoadSim, PartiallyIndexedMultiDimResolvesToOneDim) {
  SimFixture f;
  std::string path = WriteData("partial_1d", "AA\nBB\nCC\nDD\n");
  std::string out = RunCapture(
      "module t;\n"
      "  bit [7:0] mem [0:2][0:3];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem[1]);\n"
          "    $display(\"%h %h %h\", mem[1][0], mem[1][3], mem[0][0]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "aa dd 00\n");
  std::remove(path.c_str());
}

TEST(ReadmemFileLoadSim, PartiallyIndexedMultiDimWithLowestDimSlice) {
  SimFixture f;
  std::string path = WriteData("partial_slice", "AA\nBB\nCC\n");
  std::string out = RunCapture(
      "module t;\n"
      "  bit [7:0] mem [0:2][0:3];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem[1][1:2]);\n"
          "    $display(\"%h %h %h %h\", mem[1][0], mem[1][1], mem[1][2], "
          "mem[1][3]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "00 aa bb 00\n");
  std::remove(path.c_str());
}

TEST(ReadmemFileLoadSim, PartiallyIndexedThreeDimResolvesToTwoDim) {
  SimFixture f;
  std::string path = WriteData("partial_2d", "AA\nBB\nCC\nDD\nEE\nFF\n");
  std::string out = RunCapture(
      "module t;\n"
      "  bit [7:0] mem [0:1][0:1][0:2];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem[1]);\n"
          "    $display(\"%h %h %h\", mem[1][0][0], mem[1][1][2], "
          "mem[0][0][0]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "aa ff 00\n");
  std::remove(path.c_str());
}

TEST(ReadmemFileLoadSim, HigherOrderDimensionAsRangeIsError) {
  SimFixture f;
  std::string path = WriteData("hi_dim_range", "AA\nBB\n");
  std::string out = RunCapture(
      "module t;\n"
      "  bit [7:0] mem [0:2][0:3];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem[1:2][0]);\n"
          "    $display(\"%h\", mem[1][0]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a higher-order dimension must be indexed, not "
                            "sliced",
                            4, "21.4"));
  EXPECT_EQ(out, "00\n");
  std::remove(path.c_str());
}

TEST(ReadmemFileLoadSim, SliceOnNonLowestDimensionIsError) {
  SimFixture f;
  std::string path = WriteData("mid_dim_slice", "AA\nBB\n");
  std::string out = RunCapture(
      "module t;\n"
      "  bit [7:0] mem [0:1][0:2][0:2];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem[0][1:2]);\n"
          "    $display(\"%h\", mem[0][1][0]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a slice is allowed only on the lowest dimension",
                            4, "21.4"));
  EXPECT_EQ(out, "00\n");
  std::remove(path.c_str());
}

TEST(ReadmemFileLoadSim, FullyIndexedMemoryNameIsError) {
  SimFixture f;
  std::string path = WriteData("full_index", "AA\nBB\n");
  std::string out = RunCapture(
      "module t;\n"
      "  bit [7:0] mem [0:2][0:3];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem[1][2]);\n"
          "    $display(\"%h\", mem[1][2]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "memory_name resolves to a single element, not an "
                            "array",
                            4, "21.4"));
  EXPECT_EQ(out, "00\n");
  std::remove(path.c_str());
}

TEST(ReadmemFileLoadSim, HexNumberAcceptsLowercaseHexDigits) {
  SimFixture f;
  std::string path = WriteData("lower_hex", "ab\ncd\n");
  std::string out = RunCapture(
      "module t;\n"
      "  reg [7:0] mem [0:3];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem);\n"
          "    $display(\"%h %h\", mem[0], mem[1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "ab cd\n");
  std::remove(path.c_str());
}

TEST(ReadmemFileLoadSim, MissingFileWarnsAndLeavesMemoryUntouched) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  reg [7:0] mem [0:3];\n"
      "  initial begin\n"
      "    $readmemh(\"/tmp/deltahdl_t2104_absent.mem\", mem);\n"
      "    $display(\"%h\", mem[0]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_GE(f.diag.WarningCount(), 1u);
  EXPECT_EQ(out, "xx\n");
}

TEST(ReadmemFileLoadSim, AddressOutsideTheArrayRangeIsReportedAtTheCall) {
  SimFixture f;
  std::string inside = WriteData("addr_inside", "@0\n0A\n14\n1E\n28\n");
  std::string outside = WriteData("addr_outside", "@6\n0A\n");
  RunCapture(
      "module t;\n"
      "  reg [7:0] a [0:7];\n"
      "  reg [7:0] b [0:7];\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          inside +
          "\", a, 0, 3);\n"
          "    $readmemh(\"" +
          outside +
          "\", b, 0, 3);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "outside the range given by the task", 6, "21.4"));
  std::remove(inside.c_str());
  std::remove(outside.c_str());
}

TEST(ReadmemFileLoadSim, SliceBoundsErrorNames21_4) {
  SimFixture f;
  std::string path = WriteData("sub_slice", "31\n32\n");
  RunCapture(
      "module t;\n"
      "  reg [7:0] mem [0:15];\n"
      "  initial $readmemh(\"" +
          path +
          "\", mem[8:11], 1, 3);\n"
          "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "address outside the slice bounds", 3, "21.4"));
  std::remove(path.c_str());
}

TEST(ReadmemFileLoadSim, FileAddressOutsideTaskRangeNames21_4) {
  SimFixture f;
  std::string path = WriteData("sub_range", "@12\n41\n");
  RunCapture(
      "module t;\n"
      "  reg [7:0] mem [0:15];\n"
      "  initial $readmemh(\"" +
          path +
          "\", mem, 1, 4);\n"
          "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "outside the range given by the task", 3, "21.4"));
  std::remove(path.c_str());
}

TEST(ReadmemFileLoadSim, WordCountMismatchWarningNames21_4) {
  SimFixture f;
  std::string path = WriteData("sub_count", "51\n");
  RunCapture(
      "module t;\n"
      "  reg [7:0] mem [0:15];\n"
      "  initial $readmemh(\"" +
          path +
          "\", mem, 2, 6);\n"
          "endmodule\n",
      f);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "number of data words differs", 3, "21.4"));
  std::remove(path.c_str());
}

TEST(ReadmemFileLoadSim, MemoryNameShapeErrorNames21_4) {
  SimFixture f;
  std::string path = WriteData("sub_shape", "61\n");
  RunCapture(
      "module t;\n"
      "  bit [7:0] mem [0:2][0:3];\n"
      "  initial $readmemh(\"" +
          path +
          "\", mem[1][2]);\n"
          "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "memory_name resolves to a single element", 3,
                            "21.4"));
  std::remove(path.c_str());
}

TEST(ReadmemFileLoadSim, UnopenableFileStatesNoRuleOfTheStandard) {
  SimFixture f;
  RunCapture(
      "module t;\n"
      "  reg [7:0] mem [0:3];\n"
      "  initial $readmemh(\"/tmp/deltahdl_t2104_no_such.mem\", mem);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(), "cannot open file", 3, ""));
}

TEST(ReadmemFileLoadSim, LoadedElementReleasesAWaitOnIt) {
  SimFixture f;
  std::string path = WriteData("event_h", "AB\nCD\nEF\n");
  auto* var = RunAndFindVar(
      "module t;\n"
      "  reg [7:0] mem [0:7];\n"
      "  integer woke;\n"
      "  initial begin\n"
      "    woke = 0;\n"
      "    wait (mem[2] == 8'hEF);\n"
      "    woke = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    #1 $readmemh(\"" +
          path +
          "\", mem);\n"
          "    #1 $finish;\n"
          "  end\n"
          "endmodule\n",
      f, "woke");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
  std::remove(path.c_str());
}

TEST(ReadmemFileLoadSim, ArrayPropertyThroughAHandleIsLoaded) {
  SimFixture f;
  std::string path = WriteData("class_prop", "aa bb\n");
  std::string out = RunCapture(
      "module t;\n"
      "  class Mem;\n"
      "    logic [7:0] data[0:1];\n"
      "  endclass\n"
      "  logic [7:0] mm[0:1];\n"
      "  class Ld;\n"
      "    function void load; $readmemh(\"" +
          path +
          "\", mm); endfunction\n"
          "  endclass\n"
          "  Mem m = new;\n"
          "  Mem n = new;\n"
          "  Ld l = new;\n"
          "  initial begin\n"
          "    $readmemh(\"" +
          path +
          "\", m.data);\n"
          "    $display(\"%h %h\", m.data[0], m.data[1]);\n"
          "    l.load();\n"
          "    $display(\"%h %h\", mm[0], mm[1]);\n"
          "    $readmemh(\"" +
          path +
          "\", n.data[1:1]);\n"
          "    $display(\"%h %h\", n.data[0], n.data[1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "aa bb\naa bb\nxx aa\n");
  std::remove(path.c_str());
}

TEST(ReadmemFileLoadSim, HierarchicallyNamedArrayIsLoaded) {
  SimFixture f;
  std::string path = WriteData("hier", "12 34\n");
  std::string out = RunCapture(
      "module leaf; logic [7:0] mem[0:1]; endmodule\n"
      "module sub; leaf v(); logic [7:0] mem[0:1]; endmodule\n"
      "module t;\n"
      "  sub u();\n"
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", u.mem);\n"
          "    $readmemh(\"" +
          path +
          "\", u.v.mem[1:1]);\n"
          "    $display(\"%h %h %h %h\", u.mem[0], u.mem[1], u.v.mem[0],\n"
          "             u.v.mem[1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "12 34 xx 12\n");
  std::remove(path.c_str());
}

}  // namespace
