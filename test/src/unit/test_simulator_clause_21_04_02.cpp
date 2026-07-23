// §21.4.2 Reading 2-state types — $readmemb / $readmemh accept destinations
// whose packed element type is 2-state (int and friends, bit vectors,
// enumerated types). Loading proceeds exactly as for a 4-state element, except
// that an x or z digit read from the file is converted to 0. For an enumerated
// element type the file numbers are the numeric values tied to the type's
// elements (§6.19); a number naming no element is out of range for the type,
// which raises an error and stops the load.
//
// Every rule here depends on how the destination is produced — its declared
// state-ness and, for the enum rules, the §6.19 declaration that fixes the
// member values. Each test therefore declares the memory with real source
// syntax and drives the module through the full pipeline (parse -> elaborate
// -> lower -> run), reading the loaded elements back with $display.
#include <cstdio>
#include <fstream>
#include <iostream>
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
// path contains no characters that need escaping inside a SystemVerilog
// string literal, so it can be embedded directly in the source under test.
std::string WriteData(const std::string& tag, const std::string& data) {
  std::string path = "/tmp/deltahdl_t210402_" + tag + ".mem";
  std::ofstream ofs(path);
  ofs << data;
  ofs.close();
  return path;
}

// ---------------------------------------------------------------------------
// 2-state integer types: reading proceeds as for a 4-state element, except an
// x or z digit from the file becomes 0.
// ---------------------------------------------------------------------------

// §21.4.2: a bit-vector element is 2-state, so the x and z digits of a binary
// word collapse to 0 while its 0/1 digits load unchanged: "1x0z" keeps only
// its leading 1.
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

// §21.4.2: an int element is a 2-state integer type; a hex digit of x or z
// clears all four of its bits, leaving the known digits in place.
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

// §21.4.2 (input forms): the conversion applies to uppercase X / Z digits the
// same as lowercase, and reading otherwise proceeds normally — an embedded
// underscore still separates digits without contributing a bit.
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

// §21.4.2 (input forms): shortint is another 2-state integer element type —
// x/z digits clear their four bits while the known digits load in place.
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

// §21.4.2 (input forms): longint fills one machine word exactly; x and z
// digits at the two extremes of the 64-bit value both clear, pinning the
// conversion at the word's edge bits.
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

// §21.4.2 (boundary): the x/z-to-0 conversion is keyed to 2-state element
// types only. The same binary word loaded into a 4-state logic element keeps
// its unknown and high-impedance digits.
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

// §21.4.2 (input forms): the rule follows the element type, not the container
// kind — a queue of int (its size fixed for the load, §21.4.1) converts x/z
// file digits to 0 in each loaded element.
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

// §21.4.2 (input forms): a dynamic array of a 2-state type (byte) sized with
// new[] gets the same conversion — the element type's state-ness survives the
// dynamic container.
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

// §21.4.2 (input forms): an associative array with 2-state elements (§21.4.1
// container) also converts x/z file digits to 0 — like the queue and dynamic
// cases, the element's state-ness must survive this container kind too.
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

// §21.4.2 (input forms): a packed 2-state element wider than 64 bits stores
// its value across several machine words; an x digit landing above bit 63
// must be cleared in the upper word, not just the first.
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

// ---------------------------------------------------------------------------
// Enumerated element types: file numbers are the values tied to the type's
// elements (§6.19).
// ---------------------------------------------------------------------------

// §21.4.2: with a default-valued enumeration (elements 0, 1, 2 by the §6.19
// increment rule), hex file numbers load as those element values, in any
// order, with no error.
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

// §21.4.2 (input forms): explicitly valued elements on a 2-state base type —
// the file numbers are those explicit values, not element positions.
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

// §21.4.2 (input forms): $readmemb reads enumerated destinations too — the
// binary file words are the element values in base 2.
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

// §21.4.2 (interlock): an enumeration's default base is 2-state, so an x file
// digit first collapses to 0 and then names the element whose value is 0 —
// the two rules of this subclause compose without an error.
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

// §21.4.2 (input forms): the enumerated type may be declared inline on the
// memory itself rather than through a typedef (§6.19 declaration position);
// the file numbers still address the members by their values.
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

// ---------------------------------------------------------------------------
// Out-of-range numeric value: an error shall be issued and no further reading
// shall take place.
// ---------------------------------------------------------------------------

// §21.4.2 (shall): the value 5 names no element of {0, 1, 2}. The word before
// it loads; the offending word is not stored; the in-range word after it is
// never read, so both later elements keep their 2-state default of 0.
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
  EXPECT_TRUE(f.diag.HasErrors());
  EXPECT_EQ(out, "1 0 0\n");
  std::remove(path.c_str());
}

// §21.4.2 (shall, edge): "out of range" means the number matches no element,
// not merely that it exceeds the largest one. With elements valued {1, 4},
// the value 2 lies inside the numeric span yet names no element, so it is
// rejected the same way — pinning the check to element membership rather
// than a bounds comparison. (EnumExplicitValuesLoadNumerically is the
// counterfactual: the member value 4 at this same first position loads with
// no error.)
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
  EXPECT_TRUE(f.diag.HasErrors());
  EXPECT_EQ(out, "0\n");
  std::remove(path.c_str());
}

}  // namespace
