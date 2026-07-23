#include <iostream>
#include <sstream>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// Runs a single-module source through elaboration and simulation while
// capturing everything the run writes to stdout. The §21.2.1.3 rules classify
// the unknown/high-impedance bits of a displayed expression, and how a value
// comes to hold such bits -- an x/z digit in a based literal (with its
// left-extension), an uninitialized 4-state declaration, an undriven net --
// is decided by the front end. These tests therefore build each operand from
// real source syntax and observe the display through the full pipeline.
std::string RunCapture(const std::string& src, SimFixture& f) {
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  auto* design = ElaborateSrc(src, f);
  if (design != nullptr) {
    LowerAndRun(design, f);
  }
  std::cout.rdbuf(old_buf);
  return captured.str();
}

// §21.2.1.3 (D1): a decimal value whose bits are all unknown shows a single
// lowercase x. The 4-bit operand's automatic field is two columns, so the
// status character arrives right-justified behind one space.
TEST(UnknownAndHighImpedance, DecimalAllUnknownIsLowercaseX) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  initial begin\n"
      "    v = 4'bxxxx;\n"
      "    $display(\":%d:\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, ": x:\n");
}

// §21.2.1.3 (D2): a decimal value whose bits are all high-impedance shows a
// single lowercase z.
TEST(UnknownAndHighImpedance, DecimalAllHighZIsLowercaseZ) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  initial begin\n"
      "    v = 4'bzzzz;\n"
      "    $display(\":%d:\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, ": z:\n");
}

// §21.2.1.3 (D3): with some but not all bits unknown, decimal shows uppercase
// X.
TEST(UnknownAndHighImpedance, DecimalSomeUnknownIsUppercaseX) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  initial begin\n"
      "    v = 4'b01x0;\n"
      "    $display(\":%d:\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, ": X:\n");
}

// §21.2.1.3 (D4): with some but not all bits high-impedance and none unknown,
// decimal shows uppercase Z.
TEST(UnknownAndHighImpedance, DecimalSomeHighZIsUppercaseZ) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  initial begin\n"
      "    v = 4'b01z0;\n"
      "    $display(\":%d:\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, ": Z:\n");
}

// §21.2.1.3 (D4 exception): high-impedance bits accompanied by any unknown bit
// fall back to uppercase X rather than Z.
TEST(UnknownAndHighImpedance, DecimalMixedHighZAndUnknownIsUppercaseX) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  initial begin\n"
      "    v = 4'bxz01;\n"
      "    $display(\":%d:\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, ": X:\n");
}

// §21.2.1.3 (D5): decimal output always sits right-justified in a fixed-width
// field, and a status character occupies that same field. A 12-bit operand's
// automatic field is four columns (§21.2.1.2), so its all-x rendering is three
// spaces and an x.
TEST(UnknownAndHighImpedance, DecimalStatusCharRightJustifiedInField) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [11:0] v;\n"
      "  initial begin\n"
      "    v = 12'bx;\n"
      "    $display(\":%d:\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, ":   x:\n");
}

// §21.2.1.3 (D1, worked example): $display("%d", 1'bx) shows a bare x -- the
// one-bit operand's field is a single column.
TEST(UnknownAndHighImpedance, DecimalLrmExampleSingleBitUnknown) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $display(\"%d\", 1'bx);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "x\n");
}

// §21.2.1.3 (H1/H2/H4, worked example): a 14-bit literal whose leading x digit
// left-extends groups into four hex digits -- two all-x groups (lowercase x),
// one partly-unknown group (uppercase X), and one known group (a). The
// x-extension is produced by the front end from the literal 14'bx01010.
TEST(UnknownAndHighImpedance, HexLrmExampleExtendedUnknown) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $display(\"%h\", 14'bx01010);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "xxXa\n");
}

// §21.2.1.3 (H1-H4, worked example): the same 12-bit value under hex and octal
// grouping. Hex sees three partly-unknown groups (XXX); octal's three-bit
// groups resolve to a known 1, an all-x group, a known 5, and a partly-unknown
// group (1x5X).
TEST(UnknownAndHighImpedance, HexOctalLrmExampleMixedGroups) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $display(\"%h %o\", 12'b001xxx101x01, 12'b001xxx101x01);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "XXX 1x5X\n");
}

// §21.2.1.3 (H3): a hex group that is entirely high-impedance shows a
// lowercase z for that digit.
TEST(UnknownAndHighImpedance, HexAllHighZGroupIsLowercaseZ) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  initial begin\n"
      "    v = 4'bzzzz;\n"
      "    $display(\"%h\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "z\n");
}

// §21.2.1.3 (H5): a hex group with some but not all bits high-impedance and no
// unknown bits shows uppercase Z.
TEST(UnknownAndHighImpedance, HexSomeHighZGroupIsUppercaseZ) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  initial begin\n"
      "    v = 4'b01z1;\n"
      "    $display(\"%h\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "Z\n");
}

// §21.2.1.3 (H5 exception): a hex group mixing high-impedance and unknown bits
// shows uppercase X.
TEST(UnknownAndHighImpedance, HexMixedHighZAndUnknownGroupIsUppercaseX) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  initial begin\n"
      "    v = 4'bx1z1;\n"
      "    $display(\"%h\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "X\n");
}

// §21.2.1.3 (H3/H5): the high-impedance ladder holds for octal's three-bit
// groups just as for hex -- an all-z group shows lowercase z, a partly-z group
// with no unknown bits shows uppercase Z, and a group mixing z with an unknown
// bit shows uppercase X.
TEST(UnknownAndHighImpedance, OctalHighZGroupLadder) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [8:0] v;\n"
      "  initial begin\n"
      "    v = 9'bzzz1z0xz1;\n"
      "    $display(\"%o\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "zZX\n");
}

// §21.2.1.3 (B1): binary prints every bit separately using 0, 1, x, and z --
// no grouping and no status-character collapse.
TEST(UnknownAndHighImpedance, BinaryPrintsEachBitWithXAndZ) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  initial begin\n"
      "    v = 4'b1x0z;\n"
      "    $display(\"%b\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1x0z\n");
}

// §21.2.1.3 boundary: the status-character rules apply only when unknown or
// high-impedance bits are present. A fully known value keeps its plain decimal
// numeral in the two-column field.
TEST(UnknownAndHighImpedance, DecimalKnownValueShowsNumeral) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  initial begin\n"
      "    v = 4'b1010;\n"
      "    $display(\":%d:\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, ":10:\n");
}

// §21.2.1.3 (H2) input form: an uninitialized 4-state variable starts all-x by
// declaration default, so both of its hex groups classify as all-unknown.
TEST(UnknownAndHighImpedance, UninitializedVariableDisplaysAllUnknown) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [7:0] v;\n"
      "  initial $display(\"%h\", v);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "xx\n");
}

// §21.2.1.3 (H3) input form: an undriven net floats at high impedance, so its
// single hex group classifies as all-z.
TEST(UnknownAndHighImpedance, UndrivenNetDisplaysHighZ) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  wire [3:0] w;\n"
      "  initial $display(\"%h\", w);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "z\n");
}

// §21.2.1.3 negative form: a 2-state operand can never hold unknown or
// high-impedance bits -- the x and z digits of the assigned literal collapse
// to 0 on conversion, so the display shows plain digits and no status
// character can ever appear.
TEST(UnknownAndHighImpedance, TwoStateOperandNeverShowsStatusChars) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  bit [3:0] b;\n"
      "  initial begin\n"
      "    b = 4'bx01z;\n"
      "    $display(\"%b\", b);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "0010\n");
}

// §21.2.1.3 (H4) edge: the grouping rules hold for values wider than one
// machine word. A 68-bit literal carries a lone unknown bit in its top hex
// group (some but not all unknown -> uppercase X) while the remaining sixteen
// groups are fully known.
TEST(UnknownAndHighImpedance, HexUnknownBitInUpperWordGroup) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [67:0] v;\n"
      "  initial begin\n"
      "    v = 68'b1x0000000000000000000000000000000000000000000000000000000"
      "0000001010;\n"
      "    $display(\"%h\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "X000000000000000a\n");
}

// §21.2.1.3 edge: an explicit field width (the §21.2.1.2 feature) must not
// collapse a value down through its integer bits, which would discard the x/z
// information. A partly high-impedance hex group keeps its uppercase Z status
// character and is then zero-padded to the requested width.
TEST(UnknownAndHighImpedance, HexStatusCharSurvivesFieldWidth) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  initial begin\n"
      "    v = 4'b01z1;\n"
      "    $display(\":%2h:\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, ":0Z:\n");
}

// §21.2.1.3 edge: the %0 minimum-width form of §21.2.1.2 likewise preserves
// the status character -- an all-x decimal renders as a bare x with no field
// padding.
TEST(UnknownAndHighImpedance, MinimumWidthKeepsStatusChar) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [11:0] v;\n"
      "  initial begin\n"
      "    v = 12'bx;\n"
      "    $display(\":%0d:\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, ":x:\n");
}

// §21.2.1.3 (D1) input form: the classified value can be the result of an
// expression, not just a stored variable -- ANDing 1 with an unknown bit
// yields an all-unknown one-bit result.
TEST(UnknownAndHighImpedance, ExpressionResultUnknownShowsStatusChar) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  initial $display(\"%d\", 1'b1 & 1'bx);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "x\n");
}

// §21.2.1.3 (D2) syntactic position: the classification rules govern the
// write task exactly as they do the display task -- the status character and
// its field are identical, only the trailing newline is absent.
TEST(UnknownAndHighImpedance, WriteTaskShowsDecimalStatusChar) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  initial begin\n"
      "    v = 4'bzzzz;\n"
      "    $write(\":%d:\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, ": z:");
}

// §21.2.1.3 (D1) syntactic position: a bare expression argument rendered
// under the default decimal format of §21.2.1.1 takes the same status
// character in the same right-justified field an explicit %d would.
TEST(UnknownAndHighImpedance, BareArgumentDefaultDecimalShowsStatusChar) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  initial begin\n"
      "    v = 4'bxxxx;\n"
      "    $display(v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, " x\n");
}

// §21.2.1.3 input form: Table 21-1 (§21.2.1.1) admits each specifier in either
// case, and the classification ladders apply identically under the uppercase
// spellings -- partial-x decimal, extended-x hex grouping, a partial-z octal
// group beside a known digit, and bit-for-bit binary.
TEST(UnknownAndHighImpedance, UppercaseSpecifiersFollowSameRules) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic [3:0] v;\n"
      "  initial begin\n"
      "    v = 4'b01x0;\n"
      "    $display(\":%D:\", v);\n"
      "    $display(\":%H:\", 14'bx01010);\n"
      "    $display(\":%O:\", 6'b01z101);\n"
      "    v = 4'b1x0z;\n"
      "    $display(\":%B:\", v);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, ": X:\n:xxXa:\n:Z5:\n:1x0z:\n");
}

// §21.2.1.3 (D1) operand type: the `integer` keyword type is a signed 32-bit
// 4-state operand, so its all-x status character sits right-justified in the
// eleven-column signed field of §21.2.1.2.
TEST(UnknownAndHighImpedance, SignedIntegerTypeStatusCharInSignedField) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    i = 32'bx;\n"
      "    $display(\":%d:\", i);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, ":          x:\n");
}

// §21.2.1.3 (D1) operand type: `time` is a 64-bit 4-state operand, so its
// all-x status character occupies the last column of the twenty-column field.
TEST(UnknownAndHighImpedance, TimeTypeStatusCharInWideField) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  time tm;\n"
      "  initial begin\n"
      "    tm = 64'bx;\n"
      "    $display(\":%d:\", tm);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, ":                   x:\n");
}

// §21.2.1.3 operand type: a packed structure is displayed through the same
// bit-level classification as a plain vector -- binary reproduces each bit's
// x/z state across the member boundary, and the single hex group mixing an
// unknown with a high-impedance bit shows uppercase X.
TEST(UnknownAndHighImpedance, PackedStructOperandClassifiesLikeVector) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  struct packed { logic [1:0] hi; logic [1:0] lo; } s;\n"
      "  initial begin\n"
      "    s = 4'b1z0x;\n"
      "    $display(\":%b: :%h:\", s, s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, ":1z0x: :X:\n");
}

}  // namespace
