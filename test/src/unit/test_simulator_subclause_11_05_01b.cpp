#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(DeclaredRangeSelect, BitSelectLowBoundIsLeastSignificantBit) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [8:1] d;\n"
      "  logic r;\n"
      "  initial begin d = 8'b0000_0001; r = d[1]; end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(DeclaredRangeSelect, BitSelectBelowLowBoundReadsX) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [8:1] d;\n"
      "  logic r;\n"
      "  initial begin d = 8'hFF; r = d[0]; end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_NE(var->value.words[0].bval & 1u, 0u);
}

TEST(DeclaredRangeSelect, PartSelectWriteLandsAtTheLowEndOfTheRange) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  bit [64:1] addr;\n"
      "  initial begin addr = 64'd0; addr[32:1] = 32'hFFFF_FFFF; end\n"
      "endmodule\n",
      f, "addr");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFFFFFFFFu);
}

TEST(DeclaredRangeSelect, PartSelectWhollyBelowTheRangeWritesNothing) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [15:8] v;\n"
      "  initial begin v = 8'hA5; v[3:0] = 4'hF; end\n"
      "endmodule\n",
      f, "v");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xA5u);
}

TEST(DeclaredRangeSelect, AscendingRangeStartsAtTheMostSignificantBit) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [0:7] d;\n"
      "  logic r;\n"
      "  initial begin d = 8'b1000_0000; r = d[0]; end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(DeclaredRangeSelect, AscendingRangePartSelectTakesTheLeadingBits) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [1:8] d;\n"
      "  logic [3:0] y;\n"
      "  initial begin d = 8'hA5; y = d[1:4]; end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAu);
}

TEST(DeclaredRangeSelect, IndexedPartSelectCountsAlongAnAscendingRange) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [0:31] b_vect;\n"
      "  logic [7:0] y;\n"
      "  initial begin b_vect = 32'hA5000000; y = b_vect[0 +: 8]; end\n"
      "endmodule\n",
      f, "y");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xA5u);
}

TEST(DeclaredRangeSelect, ArrayElementKeepsItsDeclaredRange) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [1:8] mem [1:2];\n"
      "  logic r;\n"
      "  initial begin mem[1] = 8'b1000_0000; r = mem[1][1]; end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(DeclaredRangeSelect, NetBitSelectLowBoundIsLeastSignificantBit) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  wire [8:1] w;\n"
      "  wire r;\n"
      "  assign w = 8'b0000_0001;\n"
      "  assign r = w[1];\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(DeclaredRangeSelect, NetAscendingRangeStartsAtTheMostSignificantBit) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  wire [1:8] w;\n"
      "  wire r;\n"
      "  assign w = 8'b1000_0000;\n"
      "  assign r = w[1];\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(DeclaredRangeSelect, NetPartSelectIsBoundedByTheDeclaredRange) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  wire [64:1] w;\n"
      "  wire [31:0] r;\n"
      "  assign w = 64'hFFFF_FFFF_0000_0000;\n"
      "  assign r = w[64:33];\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFFFFFFFFu);
}

TEST(DeclaredRangeSelect, ConcatLvalueSlicesTheRhsInItsDeclaredRange) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  wire [8:1] src;\n"
      "  wire [3:0] hi;\n"
      "  wire [3:0] lo;\n"
      "  assign src = 8'b1010_0101;\n"
      "  assign {hi, lo} = src;\n"
      "endmodule\n",
      f, "hi");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAu);
}

TEST(DeclaredRangeSelect, ConcatLvalueSlicesAnAscendingRhsFromItsLeftBound) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  wire [1:8] src;\n"
      "  wire [3:0] hi;\n"
      "  wire [3:0] lo;\n"
      "  assign src = 8'b1010_0101;\n"
      "  assign {hi, lo} = src;\n"
      "endmodule\n",
      f, "lo");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x5u);
}

TEST(DeclaredRangeSelect, InstanceArrayConnectionSlicesInTheDeclaredRange) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module leaf(input a, output y);\n"
      "  assign y = a;\n"
      "endmodule\n"
      "module t;\n"
      "  wire [4:1] src;\n"
      "  wire [3:0] out;\n"
      "  assign src = 4'b0110;\n"
      "  leaf u [3:0] (.a(src), .y(out));\n"
      "endmodule\n",
      f, "out");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x6u);
}

TEST(DeclaredRangeSelect, InstanceArrayConnectionSlicesAnAscendingRange) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module leaf(input a, output y);\n"
      "  assign y = a;\n"
      "endmodule\n"
      "module t;\n"
      "  wire [1:4] src;\n"
      "  wire [3:0] out;\n"
      "  assign src = 4'b0011;\n"
      "  leaf u [3:0] (.a(src), .y(out));\n"
      "endmodule\n",
      f, "out");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0x3u);
}

TEST(DeclaredRangeSelect, PortBitSelectLowBoundIsLeastSignificantBit) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module leaf(input [8:1] data, output y);\n"
      "  assign y = data[1];\n"
      "endmodule\n"
      "module t;\n"
      "  logic [7:0] src;\n"
      "  wire r;\n"
      "  leaf u (.data(src), .y(r));\n"
      "  initial src = 8'b0000_0001;\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(DeclaredRangeSelect, PortAscendingRangeStartsAtTheMostSignificantBit) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module leaf(input [1:8] data, output y);\n"
      "  assign y = data[1];\n"
      "endmodule\n"
      "module t;\n"
      "  logic [7:0] src;\n"
      "  wire r;\n"
      "  leaf u (.data(src), .y(r));\n"
      "  initial src = 8'b1000_0000;\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(DeclaredRangeSelect, PortPartSelectIsBoundedByTheDeclaredRange) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module leaf(input [64:1] w, output [31:0] q);\n"
      "  assign q = w[64:33];\n"
      "endmodule\n"
      "module t;\n"
      "  logic [63:0] src;\n"
      "  wire [31:0] r;\n"
      "  leaf u (.w(src), .q(r));\n"
      "  initial src = 64'hFFFF_FFFF_0000_0000;\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xFFFFFFFFu);
}

const char kDeclaredRangeLeaf[] =
    "module leaf;\n"
    "  logic [8:1] x;\n"
    "  logic r;\n"
    "  initial begin x = 8'b0000_0001; r = x[1]; end\n"
    "endmodule\n";

std::string DeclaredRangeLeafInstantiated() {
  return std::string(kDeclaredRangeLeaf) +
         "module t;\n"
         "  leaf u ();\n"
         "endmodule\n";
}

TEST(DeclaredRangeSelect, TopAndChildInstanceBodyVectorsSelectAlike) {
  SimFixture top_f;
  auto* top_r = RunAndFindVar(kDeclaredRangeLeaf, top_f, "r");
  SimFixture child_f;
  auto* child_r =
      RunAndFindVar(DeclaredRangeLeafInstantiated(), child_f, "u.r");
  ASSERT_NE(top_r, nullptr);
  ASSERT_NE(child_r, nullptr);
  EXPECT_EQ(child_r->value.ToUint64(), top_r->value.ToUint64());

  EXPECT_EQ(child_r->value.words[0].bval, top_r->value.words[0].bval);
}

TEST(DeclaredRangeSelect, ProcedureLocalKeepsItsDeclaredRange) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int r;\n"
      "  initial begin\n"
      "    bit [15:10] v;\n"
      "    v = 6'h2D;\n"
      "    r = v[13:10] * 100 + v[15:12];\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1311u);
}

TEST(DeclaredRangeSelect, SubroutineLocalKeepsItsDeclaredRange) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int r;\n"
      "  function int windows();\n"
      "    bit [15:10] v;\n"
      "    v = 6'h2D;\n"
      "    return v[13:10] * 100 + v[15:12];\n"
      "  endfunction\n"
      "  initial r = windows();\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1311u);
}

TEST(DeclaredRangeSelect, TypedefNameCarriesItsRangeToAModuleVariable) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef bit [15:10] value_t;\n"
      "  value_t v;\n"
      "  int r;\n"
      "  initial begin\n"
      "    v = 6'h2D;\n"
      "    r = v[13:10] * 100 + v[15:12];\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1311u);
}

TEST(DeclaredRangeSelect, TypedefNameCarriesItsRangeToAProcedureLocal) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  typedef bit [15:10] value_t;\n"
      "  int r;\n"
      "  initial begin\n"
      "    value_t v;\n"
      "    v = 6'h2D;\n"
      "    r = v[13:10] * 100 + v[15:12];\n"
      "  end\n"
      "endmodule\n",
      f, "r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1311u);
}

TEST(DeclaredRangeSelect, AnAscendingPropertysSelectsFollowItsDeclaration) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  class C; logic [0:31] bv = 32'h89AB_CDEF; endclass\n"
      "  C h;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    $display(\"%h %h %h %b\", h.bv[8:15], h.bv[8 +: 8], h.bv[16 -: 8],\n"
      "             h.bv[0]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "ab ab 57 1\n");
}

TEST(DeclaredRangeSelect, AWriteToAnAscendingPropertysSelectFollowsIt) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  class C; logic [0:31] bv = 0; endclass\n"
      "  C h;\n"
      "  initial begin\n"
      "    h = new;\n"
      "    h.bv[0:7] = 8'hFF; h.bv[31] = 1'b1;\n"
      "    $display(\"%h\", h.bv);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "ff000001\n");
}

TEST(DeclaredRangeSelect, BitsOfAnElementOfAnArrayPropertyAreWritten) {
  SimFixture f;
  auto out = RunCapture(
      "class C;\n"
      "  int ia[2];\n"
      "  logic [0:7] la[2];\n"
      "  static bit [7:0] sb[2];\n"
      "  int da[];\n"
      "  function void m(); ia[0] = 0; ia[0][1] = 1; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  C h;\n"
      "  initial begin\n"
      "    h = new; h.m();\n"
      "    h.ia[1] = 0; h.ia[1][3] = 1; h.ia[1][15:8] = 8'hAB;\n"
      "    h.la[0] = 8'h00; h.la[0][0] = 1;\n"
      "    C::sb[1] = 0; C::sb[1][7:4] = 4'hF;\n"
      "    h.da = new[1]; h.da[0] = 0; h.da[0][2] = 1;\n"
      "    $display(\"%0d %h %h %h %h\", h.ia[0], h.ia[1], h.la[0], C::sb[1],\n"
      "             h.da[0]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "2 0000ab08 80 f0 00000004\n");
}

}  // namespace
