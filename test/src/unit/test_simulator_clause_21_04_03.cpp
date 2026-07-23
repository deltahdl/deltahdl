// §21.4.3 File format considerations for multidimensional unpacked arrays —
// how $readmemb / $readmemh (and $writememb / $writememh) traverse a
// multidimensional unpacked array against the row-major file organization.
//
// Every rule here depends on how the destination is produced: the declaration's
// dimension count, each dimension's bounds and direction, and the element's
// packed shape decide the row-major geometry the load and dump must follow.
// These tests therefore declare real multidimensional memories in module
// source and drive each through the full pipeline (parse -> elaborate ->
// lower -> run), observing the loaded words with $display or reading back the
// dumped file — never hand-registering array metadata on a bare simulation
// context. The data files are real scratch files written before each run.
#include <cstdio>
#include <fstream>
#include <iostream>
#include <iterator>
#include <sstream>
#include <string>

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
// path contains no characters needing escapes inside a SystemVerilog string
// literal, so it can be embedded directly in the source under test.
std::string WriteData(const std::string& tag, const std::string& data) {
  std::string path = "/tmp/deltahdl_t21403_" + tag + ".mem";
  std::ofstream ofs(path);
  ofs << data;
  ofs.close();
  return path;
}

// Reads back the whole contents of a file a run dumped with $writemem.
std::string SlurpFile(const std::string& path) {
  std::ifstream ifs(path);
  return std::string((std::istreambuf_iterator<char>(ifs)),
                     std::istreambuf_iterator<char>());
}

// §21.4.3: the file is organized row-major with the lowest (rightmost-
// declared) dimension varying most rapidly, so a 2x2 array fills [0][0],
// [0][1], [1][0], [1][1] from successive file words.
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

// §21.4.3: the file data is hierarchical — each successive lower dimension is
// entirely enclosed within a higher-dimension word. A three-dimensional array
// with a nonzero innermost low bound (the LRM example's shape, scaled down)
// fills with the innermost subscript varying fastest, then the middle, then
// the outermost; every dimension's entries run from its low address upward.
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

// §21.4.3: the file layout is identical when one or more unpacked dimension
// declarations are reversed. The same file loaded into an ascending-declared
// array and into one with every dimension reversed lands the same word at the
// same (low-to-high) addresses.
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

// §21.4.3: the layout is unchanged when only some dimensions are reversed —
// the rule admits reversing one or more declarations, not just all of them.
// Here only the highest dimension flips; the words still land at the same
// low-to-high addresses.
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

// §21.4.3: $readmemb works with multidimensional unpacked arrays too, filling
// the same row-major sequence while reading each word as a binary number.
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

// §21.4.3: with no address entries and incomplete data, the read stops at the
// last initialized word and the remaining array words are left unchanged (a
// 2-state element stays at its 0 default).
TEST(ReadmemMultiDimSim, IncompleteFileLeavesRemainderUnchanged) {
  SimFixture f;
  std::string path = WriteData("incomplete", "11\n22\n33\n");  // 3 of 4 words
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

// §21.4.3: "left unchanged" observed through a 4-state element type — the
// subwords the incomplete file never reaches keep their declaration-time x
// rather than being zero-filled.
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

// §21.4.3: the row-major organization is backward compatible with
// one-dimensional memory arrays — at one dimension it degenerates to the
// traditional sequential layout, and an address entry names an element of the
// (only, hence highest) dimension directly.
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

// §21.4.3: as in the LRM's example file, several address entries may appear,
// each repositioning the load to another highest-dimension word — including
// backward — and each word's subwords then fill in row-major order.
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

// §21.4.3: an address entry names highest-dimension words by their declared
// addresses, so a highest dimension declared with a nonzero low bound is
// addressed at its own coordinates, not zero-based ones.
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

// §21.4.3: when a file with address entries holds too few words to completely
// fill the addressed highest-dimension word, the remaining subwords of that
// word are left unchanged.
TEST(ReadmemMultiDimSim, AddressedWordInsufficientDataLeavesSubwords) {
  SimFixture f;
  std::string path = WriteData("addr_partial", "@1\naa\n");  // 1 of 2 subwords
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

// §21.4.3: the addressed-word underfill rule observed through a 4-state
// element type — the subword the file never supplies keeps its x default,
// proving it was genuinely left unchanged rather than zero-filled.
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

// §21.4.3 (negative): since address entries name only highest-dimension words,
// an address beyond that dimension's range names no word; the load reports an
// error and assigns nothing.
TEST(ReadmemMultiDimSim, AddressBeyondHighestDimensionIsError) {
  SimFixture f;
  std::string path = WriteData("addr_oob", "@5\naa\n");
  std::string out = RunCapture(
      "module t;\n"
      "  bit [7:0] mem [0:1][0:1];\n"  // highest dimension is 0..1
      "  initial begin\n"
      "    $readmemh(\"" +
          path +
          "\", mem);\n"
          "    $display(\"%h %h\", mem[0][0], mem[1][1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
  EXPECT_EQ(out, "00 00\n");
  std::remove(path.c_str());
}

// §21.4.3: when the element carries multiple packed dimensions, each memory
// word in the pattern file is composed of the sum total of all packed bits
// (bit layout per §7.4.4). A [1:0][7:0] element therefore consumes one full
// 16-bit file word per element.
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

// §21.4.3: a partially indexed memory_name (§21.4) that still resolves to two
// or more dimensions is filled with the same row-major organization over the
// remaining dimensions, while the unindexed sibling words stay untouched.
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

// §21.4.3: $writememh works with multidimensional unpacked arrays, dumping the
// words in the same row-major, low-to-high-address organization the load side
// reads — so the file on disk lists [0][0], [0][1], [1][0], [1][1] in turn.
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

// §21.4.3: the dumped organization is what the matching read expects, so a
// $writememb dump of one multidimensional array reloads via $readmemb into
// another — even one declared with reversed dimension directions, since the
// file layout is direction-independent.
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

// §21.4.3: a three-dimensional dump walks every dimension low-to-high with the
// lowest varying fastest, mirroring the hierarchical read order.
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

}  // namespace
