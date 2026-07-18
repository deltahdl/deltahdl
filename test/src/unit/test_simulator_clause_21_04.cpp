// §21.4 Loading memory array data from a file — the runtime behavior of the
// $readmemb / $readmemh system tasks.
//
// Every rule in §21.4 is a runtime rule whose behavior depends on how its
// inputs are produced: the destination memory's declared bounds, width, and
// dimensionality decide the load window and the row-major geometry; the file
// text decides the radix, the x/z/underscore handling, and the @-address
// repositioning; and the filename argument may be produced as a string literal,
// a string-typed variable, or a packed integral value. These tests therefore
// declare real memories and call the tasks from procedural source, driving each
// module through the full pipeline (parse -> elaborate -> lower -> run) and
// reading the loaded words back with $display — rather than hand-building a
// system-call node and a memory in an isolated evaluator. The data files are
// real scratch files written before each run.
#include <cstdio>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// Runs a single-module source through elaboration and simulation while
// capturing everything the run writes to stdout.
std::string RunCapture(const std::string& src, SimFixture& f) {
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  auto* design = ElaborateSrc(src, f);
  if (design != nullptr) LowerAndRun(design, f);
  std::cout.rdbuf(old_buf);
  return captured.str();
}

// Writes `data` to a scratch file tagged by `tag` and returns its path. The
// path contains no characters that need escaping inside a SystemVerilog string
// literal, so it can be embedded directly in the source under test.
std::string WriteData(const std::string& tag, const std::string& data) {
  std::string path = "/tmp/deltahdl_t2104_" + tag + ".mem";
  std::ofstream ofs(path);
  ofs << data;
  ofs.close();
  return path;
}

// §21.4: as the file is read, each unsized number is assigned to a successive
// word element of the memory; $readmemh reads the numbers as hexadecimal.
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

// §21.4: for $readmemb each number is binary rather than hexadecimal.
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

// §21.4: the file may contain only white space, comments (both the // and /* */
// forms), and numbers; white space and comments serve only to separate numbers.
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

// §21.4: within a $readmemh number the unknown value (x), the high-impedance
// value (z), and the underscore separator may appear. Underscores are dropped;
// x and z survive per hex digit.
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
  // "Ax": high nibble known A, low nibble unknown -> "ax"; "z5": high nibble
  // high-Z, low nibble 5 -> "z5"; "1_F": underscore vanishes -> "1f".
  EXPECT_EQ(out, "ax z5 1f\n");
  std::remove(path.c_str());
}

// §21.4: the same unknown / high-Z / underscore rules apply to $readmemb, one
// digit per bit.
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
  // "10x1": bit 1 unknown; "1_0_1": underscores drop, leaving 0b101.
  EXPECT_EQ(out, "00001x01 00000101\n");
  std::remove(path.c_str());
}

// §21.4: an @-address in the file (an '@' immediately followed by a hexadecimal
// index) repositions the load cursor; subsequent data loads from that address.
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
  EXPECT_EQ(out, "00 00 aa bb\n");
  std::remove(path.c_str());
}

// §21.4: the @-address digits may be upper- or lowercase hexadecimal.
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

// §21.4: as many @-address specifications as needed may appear; each one
// repositions the cursor independently.
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
  EXPECT_EQ(out, "aa 00 bb\n");  // mem[3] is not part of either run
  std::remove(path.c_str());
}

// §21.4: with no addressing in the task and none in the file, the default start
// address is the lowest address in the memory and loading proceeds upward.
TEST(ReadmemFileLoadSim, DefaultStartIsLowestAddressUpward) {
  SimFixture f;
  std::string path = WriteData("default", "01\n02\n");
  std::string out = RunCapture(
      "module t;\n"
      "  reg [7:0] mem [1:4];\n"  // lowest address is 1
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem);\n"
          "    $display(\"%h %h %h %h\", mem[1], mem[2], mem[3], mem[4]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "01 02 00 00\n");
  std::remove(path.c_str());
}

// §21.4: a start address supplied without a finish address makes loading begin
// there and continue upward toward the highest address.
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
  EXPECT_EQ(out, "00 aa bb\n");
  std::remove(path.c_str());
}

// §21.4: when the start address exceeds the finish address, the address is
// decremented between consecutive loads. A matching word count draws no
// warning.
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

// §21.4: the descending load direction set by start > finish continues to be
// followed even after an @-address in the file repositions the cursor.
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
  EXPECT_EQ(out, "aa bb\n");  // continued downward past the @-address
  std::remove(path.c_str());
}

// §21.4: the upward direction of a start-only load likewise persists after an
// @-address in the file.
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
  EXPECT_EQ(out, "aa bb\n");  // continued upward past the @-address
  std::remove(path.c_str());
}

// §21.4: when addressing is specified both in the task and in the file, a file
// address outside the task's range is an error, and the load is terminated.
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
  EXPECT_TRUE(f.diag.HasErrors());
  EXPECT_EQ(out, "00\n");  // the out-of-range load did not occur
  std::remove(path.c_str());
}

// §21.4: a warning is issued when the number of data words differs from the
// range implied by start through finish and no addresses appear in the file.
// The words present are loaded from the start address; uncovered addresses are
// left unmodified.
TEST(ReadmemFileLoadSim, WordCountMismatchWarnsAndLeavesGapUnmodified) {
  SimFixture f;
  std::string path = WriteData("mismatch", "AA\nBB\n");  // 2 words, window of 4
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
  EXPECT_EQ(out, "aa bb 00 00\n");  // mem[3], mem[4] unmodified
  std::remove(path.c_str());
}

// §21.4: when the word count matches the start-through-finish window exactly,
// no warning is issued.
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

// §21.4: the filename may be produced by a string-typed variable, not only a
// string literal.
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

// §21.4: the filename may also come from an integral value whose packed bytes
// spell the name (the third accepted filename form).
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

// §21.4: the memory_name may name the lowest dimension with slice syntax; the
// load is confined to the slice's bounds and defaults to the slice's low
// address.
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
  EXPECT_EQ(out, "aa dd 00\n");  // EE lies beyond the slice, so mem[8] stays 00
  std::remove(path.c_str());
}

// §21.4: start_addr / finish_addr within a slice's bounds drive the load (here
// downward) exactly as for a whole array.
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

// §21.4 (shall): a start_addr or finish_addr outside the slice's bounds is an
// error, and the load does not occur.
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
  EXPECT_TRUE(f.diag.HasErrors());
  EXPECT_EQ(out, "00\n");
  std::remove(path.c_str());
}

// §21.4: the memory_name may be a partially indexed multidimensional array that
// resolves to a lesser-dimensioned array. Indexing the highest dimension of a
// 2-D memory yields a single-dimension sub-array, filled in address order.
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
  // mem[1] fills across the lowest dimension; row [0] is untouched.
  EXPECT_EQ(out, "aa dd 00\n");
  std::remove(path.c_str());
}

// §21.4: a partially indexed memory_name may still name its lowest dimension
// with slice syntax, narrowing the resolved sub-array's load window.
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
  // Only [1] and [2] of row 1 are in the slice; CC lies beyond it.
  EXPECT_EQ(out, "00 aa bb 00\n");
  std::remove(path.c_str());
}

// §21.4 / §21.4.3: partially indexing a 3-D memory's highest dimension resolves
// to a 2-D sub-array, which is then filled in row-major order.
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
  // Row-major over the two remaining dimensions of mem[1]; mem[0] untouched.
  EXPECT_EQ(out, "aa ff 00\n");
  std::remove(path.c_str());
}

// §21.4 (shall, negative): a higher-order dimension of the memory_name must be
// selected with a single index, not a range. Writing a range there (a slice on
// a non-final subscript) is rejected and no data is loaded.
TEST(ReadmemFileLoadSim, HigherOrderDimensionAsRangeIsError) {
  SimFixture f;
  std::string path = WriteData("hi_dim_range", "AA\nBB\n");
  std::string out = RunCapture(
      "module t;\n"
      "  bit [7:0] mem [0:2][0:3];\n"
      "  initial begin\n"
      // mem[1:2] ranges the higher-order dimension 0, which is illegal.
      "    $readmemh(\"" +
          path +
          "\", mem[1:2][0]);\n"
          "    $display(\"%h\", mem[1][0]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
  EXPECT_EQ(out, "00\n");  // the malformed name loaded nothing
  std::remove(path.c_str());
}

// §21.4 (shall, negative): slice syntax is permitted only on the lowest
// dimension. Slicing a dimension that still encloses inner dimensions leaves
// the name resolving to more than one dimension through a range, which is
// rejected.
TEST(ReadmemFileLoadSim, SliceOnNonLowestDimensionIsError) {
  SimFixture f;
  std::string path = WriteData("mid_dim_slice", "AA\nBB\n");
  std::string out = RunCapture(
      "module t;\n"
      "  bit [7:0] mem [0:1][0:2][0:2];\n"
      "  initial begin\n"
      // Dimension 1 is sliced while dimension 2 (the lowest) is left open.
      "    $readmemh(\"" +
          path +
          "\", mem[0][1:2]);\n"
          "    $display(\"%h\", mem[0][1][0]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
  EXPECT_EQ(out, "00\n");
  std::remove(path.c_str());
}

// §21.4 (negative): a memory_name must resolve to an unpacked array. Fully
// indexing every dimension names a single element, not an array, and is
// rejected rather than loaded.
TEST(ReadmemFileLoadSim, FullyIndexedMemoryNameIsError) {
  SimFixture f;
  std::string path = WriteData("full_index", "AA\nBB\n");
  std::string out = RunCapture(
      "module t;\n"
      "  bit [7:0] mem [0:2][0:3];\n"
      "  initial begin\n"
      // Both dimensions are indexed, so the name is a single element.
      "    $readmemh(\"" +
          path +
          "\", mem[1][2]);\n"
          "    $display(\"%h\", mem[1][2]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
  EXPECT_EQ(out, "00\n");
  std::remove(path.c_str());
}

// §21.4: $readmemh numbers are hexadecimal, and their digits may be lowercase
// a-f as well as the uppercase A-F exercised above (a distinct decode path).
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

// §21.4: an unopenable file leaves the memory untouched and reports a warning
// rather than silently succeeding.
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
  EXPECT_EQ(out, "00\n");
}

}  // namespace
