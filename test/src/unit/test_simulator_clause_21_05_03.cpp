// §21.5.3 Writing addresses to output file — three rules govern whether a
// $writememb / $writememh dump carries @-address specifiers:
//   (1) shall not: a fixed unpacked array or a dynamic array is dumped as a
//       bare word sequence, with no @-addresses;
//   (2) shall: an associative array is dumped with an address specifier for
//       its entries, since sparse keys cannot be placed by a sequential read;
//   (3) legality: an associative array is a legal argument only when its
//       index type is integral (per §21.4.1) — a string-keyed array is
//       rejected.
//
// Every rule's behavior depends on how the memory operand is declared (fixed /
// dynamic / associative container, and the associative index type), so each
// test declares its array with real syntax and drives the module through the
// full pipeline, observing the dumped file text and — where the file must
// reload — the round trip through the matching §21.4 read task.
//
// Not exercised here: an inline `bit [15:0]` index type in the associative
// dimension — the declaration parser rejects the un-typedef'd vector index
// form (upstream §7.8 territory); the typedef'd spelling below covers the
// vector-index input form.
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

// Reads back the whole contents of a file a run dumped with $writemem.
std::string SlurpFile(const std::string& path) {
  std::ifstream ifs(path);
  return std::string((std::istreambuf_iterator<char>(ifs)),
                     std::istreambuf_iterator<char>());
}

// ---------------------------------------------------------------------------
// Rule 1 (shall not): unpacked and dynamic arrays are dumped without
// @-address specifiers.
// ---------------------------------------------------------------------------

// §21.5.3: a fixed unpacked array dumps as a bare word sequence — no '@'
// anywhere in the file — and the matching sequential $readmemh reloads it
// word for word.
TEST(WritememAddressSim, UnpackedArrayNoAddressSpecifiers) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210503_unp.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] mem [0:3];\n"
      "  logic [7:0] dst [0:3];\n"
      "  initial begin\n"
      "    mem[0] = 8'h11; mem[1] = 8'h22; mem[2] = 8'h33; mem[3] = 8'h44;\n"
      "    $writememh(\"" +
          path +
          "\", mem);\n"
          "    $readmemh(\"" +
          path +
          "\", dst);\n"
          "    $display(\"%h %h %h %h\", dst[0], dst[1], dst[2], dst[3]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "11 22 33 44\n");
  std::string contents = SlurpFile(path);
  EXPECT_EQ(contents, "11\n22\n33\n44\n");
  EXPECT_EQ(contents.find('@'), std::string::npos);
  std::remove(path.c_str());
}

// §21.5.3: the rule holds for both radices — $writememb dumps the same array
// as bare binary words with no address specifiers.
TEST(WritememAddressSim, UnpackedArrayBinaryDumpBare) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210503_unpb.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] mem [0:1];\n"
      "  initial begin\n"
      "    mem[0] = 8'h11; mem[1] = 8'h22;\n"
      "    $writememb(\"" +
          path +
          "\", mem);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "");
  std::string contents = SlurpFile(path);
  EXPECT_EQ(contents, "00010001\n00100010\n");
  EXPECT_EQ(contents.find('@'), std::string::npos);
  std::remove(path.c_str());
}

// §21.5.3: a descending unpacked dimension declaration changes nothing about
// the file form — still a bare ascending-address word sequence, no '@'.
TEST(WritememAddressSim, DescendingDeclArrayDumpedBare) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210503_desc.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] mem [3:0];\n"
      "  initial begin\n"
      "    mem[0] = 8'hA0; mem[1] = 8'hA1; mem[2] = 8'hA2; mem[3] = 8'hA3;\n"
      "    $writememh(\"" +
          path +
          "\", mem);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "");
  std::string contents = SlurpFile(path);
  EXPECT_EQ(contents, "a0\na1\na2\na3\n");
  EXPECT_EQ(contents.find('@'), std::string::npos);
  std::remove(path.c_str());
}

// §21.5.3: even a bounded dump (start_addr / finish_addr naming a sub-window)
// writes no @-addresses — the placement information is simply not recorded
// for a non-associative array.
TEST(WritememAddressSim, BoundedWindowStillNoAddressSpecifiers) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210503_win.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] mem [0:3];\n"
      "  initial begin\n"
      "    mem[0] = 8'h11; mem[1] = 8'h22; mem[2] = 8'h33; mem[3] = 8'h44;\n"
      "    $writememh(\"" +
          path +
          "\", mem, 1, 2);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "");
  std::string contents = SlurpFile(path);
  EXPECT_EQ(contents, "22\n33\n");
  EXPECT_EQ(contents.find('@'), std::string::npos);
  std::remove(path.c_str());
}

// §21.5.3: a dynamic array (sized by new[]) dumps exactly like a fixed
// unpacked array — bare words, no '@' — and reloads through $readmemh into a
// dynamic array of the same size.
TEST(WritememAddressSim, DynamicArrayNoAddressSpecifiers) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210503_dyn.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] d [];\n"
      "  logic [7:0] r [];\n"
      "  initial begin\n"
      "    d = new[2]; d[0] = 8'hAB; d[1] = 8'hCD;\n"
      "    $writememh(\"" +
          path +
          "\", d);\n"
          "    r = new[2];\n"
          "    $readmemh(\"" +
          path +
          "\", r);\n"
          "    $display(\"%h %h\", r[0], r[1]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "ab cd\n");
  std::string contents = SlurpFile(path);
  EXPECT_EQ(contents, "ab\ncd\n");
  EXPECT_EQ(contents.find('@'), std::string::npos);
  std::remove(path.c_str());
}

// §21.5.3: a queue is an unpacked-array kind and follows the same bare form —
// no address specifiers in the dump.
TEST(WritememAddressSim, QueueDumpedBare) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210503_q.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  byte q [$];\n"
      "  initial begin\n"
      "    q.push_back(8'h0F); q.push_back(8'hF0);\n"
      "    $writememb(\"" +
          path +
          "\", q);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "");
  std::string contents = SlurpFile(path);
  EXPECT_EQ(contents, "00001111\n11110000\n");
  EXPECT_EQ(contents.find('@'), std::string::npos);
  std::remove(path.c_str());
}

// §21.5.3: a multidimensional unpacked array is still an unpacked array —
// its row-major dump (one word per line, lowest dimension varying fastest)
// carries no @-address specifiers either.
TEST(WritememAddressSim, MultiDimUnpackedArrayDumpedBare) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210503_md.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] m [0:1][0:1];\n"
      "  initial begin\n"
      "    m[0][0] = 8'h11; m[0][1] = 8'h22;\n"
      "    m[1][0] = 8'h33; m[1][1] = 8'h44;\n"
      "    $writememh(\"" +
          path +
          "\", m);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "");
  std::string contents = SlurpFile(path);
  EXPECT_EQ(contents, "11\n22\n33\n44\n");
  EXPECT_EQ(contents.find('@'), std::string::npos);
  std::remove(path.c_str());
}

// ---------------------------------------------------------------------------
// Rule 2 (shall): associative arrays are dumped with address specifiers.
// ---------------------------------------------------------------------------

// §21.5.3: an int-keyed associative array writes an @-address ahead of every
// word. Keys appear in ascending order and are printed in hexadecimal — key
// 16 becomes "@10" — the form the §21.4.1 read side parses, so a $readmemh
// into a fresh associative array recreates the same sparse keys and values.
TEST(WritememAddressSim, AssocArrayAddressSpecifiersWritten) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210503_aa.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] aa [int];\n"
      "  logic [7:0] bb [int];\n"
      "  initial begin\n"
      "    aa[5] = 8'hAB; aa[16] = 8'hCD;\n"
      "    $writememh(\"" +
          path +
          "\", aa);\n"
          "    $readmemh(\"" +
          path +
          "\", bb);\n"
          "    $display(\"%0d %h %h\", bb.num(), bb[5], bb[16]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "2 ab cd\n");
  EXPECT_EQ(SlurpFile(path), "@5\nab\n@10\ncd\n");
  std::remove(path.c_str());
}

// §21.5.3: the address requirement is radix-independent — $writememb writes
// the same @-addresses with binary words.
TEST(WritememAddressSim, AssocArrayBinaryDumpHasAddresses) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210503_aab.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] aa [int];\n"
      "  initial begin\n"
      "    aa[5] = 8'hAB; aa[16] = 8'hCD;\n"
      "    $writememb(\"" +
          path +
          "\", aa);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "");
  EXPECT_EQ(SlurpFile(path), "@5\n10101011\n@10\n11001101\n");
  std::remove(path.c_str());
}

// §21.5.3: a typedef'd packed-vector index type is integral, so the array is
// a legal argument and its keys dump as @-addresses.
TEST(WritememAddressSim, AssocTypedefVectorIndexDumpsAddresses) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210503_vec.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  typedef bit [15:0] addr_t;\n"
      "  logic [7:0] aa [addr_t];\n"
      "  initial begin\n"
      "    aa[16'h20] = 8'h77;\n"
      "    $writememh(\"" +
          path +
          "\", aa);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "");
  EXPECT_EQ(SlurpFile(path), "@20\n77\n");
  std::remove(path.c_str());
}

// §21.5.3: the wildcard index [*] admits any integral key, so it satisfies
// the integral-index requirement and dumps with @-addresses like an
// int-indexed array.
TEST(WritememAddressSim, AssocWildcardIndexDumpsAddresses) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210503_wild.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] aa [*];\n"
      "  initial begin\n"
      "    aa[9] = 8'h99;\n"
      "    $writememh(\"" +
          path +
          "\", aa);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "");
  EXPECT_EQ(SlurpFile(path), "@9\n99\n");
  std::remove(path.c_str());
}

// §21.5.3: an enumerated index type is integral; each entry's @-address is
// the member's numeric value, so the file reloads through the §21.4.1
// enum-indexed read path.
TEST(WritememAddressSim, AssocEnumIndexNumericAddresses) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210503_enum.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  typedef enum {RED = 2, GREEN = 5} color_t;\n"
      "  logic [7:0] aa [color_t];\n"
      "  logic [7:0] bb [int];\n"
      "  initial begin\n"
      "    aa[RED] = 8'h41; aa[GREEN] = 8'h42;\n"
      "    $writememh(\"" +
          path +
          "\", aa);\n"
          "    $readmemh(\"" +
          path +
          "\", bb);\n"
          "    $display(\"%0d %h %h\", bb.num(), bb[2], bb[5]);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "2 41 42\n");
  EXPECT_EQ(SlurpFile(path), "@2\n41\n@5\n42\n");
  std::remove(path.c_str());
}

// §21.5.3: the address rule is independent of where the call appears — a
// $writememh issued from a task body dumps the associative array with the
// same @-address form as one issued directly in an initial block.
TEST(WritememAddressSim, TaskBodyCallWritesAddresses) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210503_task.mem";
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] aa [int];\n"
      "  task dump_aa;\n"
      "    $writememh(\"" +
          path +
          "\", aa);\n"
          "  endtask\n"
          "  initial begin\n"
          "    aa[5] = 8'hAB; aa[16] = 8'hCD;\n"
          "    dump_aa;\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_EQ(out, "");
  EXPECT_EQ(SlurpFile(path), "@5\nab\n@10\ncd\n");
  std::remove(path.c_str());
}

// ---------------------------------------------------------------------------
// Rule 3 (legality): an associative array argument shall have an integral
// index type; a string-keyed array is the closest rejected input.
// ---------------------------------------------------------------------------

// §21.5.3 (shall): a string-keyed associative array is not a legal $writememh
// argument. The call is rejected with an error and a pre-existing file at the
// target path is left untouched — no truncation, no partial dump.
TEST(WritememAddressSim, StringIndexRejectedFileUntouched) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210503_str.mem";
  {
    std::ofstream pre(path);
    pre << "KEEP\n";
  }
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] aa [string];\n"
      "  initial begin\n"
      "    $writememh(\"" +
          path +
          "\", aa);\n"
          "    $display(\"after\");\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
  EXPECT_EQ(out, "after\n");
  EXPECT_EQ(SlurpFile(path), "KEEP\n");
  std::remove(path.c_str());
}

// §21.5.3 (shall): the same rejection applies to $writememb — the error is
// raised and no output file is created at all.
TEST(WritememAddressSim, StringIndexRejectedWritememb) {
  SimFixture f;
  std::string path = "/tmp/deltahdl_t210503_strb.mem";
  std::remove(path.c_str());
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] aa [string];\n"
      "  initial begin\n"
      "    $writememb(\"" +
          path +
          "\", aa);\n"
          "  end\n"
          "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
  EXPECT_EQ(out, "");
  std::ifstream check(path);
  EXPECT_FALSE(check.good());
  std::remove(path.c_str());
}

}  // namespace
