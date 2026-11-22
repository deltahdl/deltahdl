#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <utility>
#include <vector>

#include "helpers_vpi_put_array_run.h"
#include "helpers_vpi_put_run.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

PLI_INT32 PutRawValue(const char* name, s_vpi_arrayvalue value,
                      const std::vector<int>& bytes, PLI_UINT32 num,
                      std::vector<PLI_INT32> index) {
  std::vector<PLI_BYTE8> raw;
  raw.reserve(bytes.size());
  for (const int kByte : bytes) raw.push_back(static_cast<PLI_BYTE8>(kByte));
  value.value.rawvals = raw.data();
  return PutArrayAt(HandleNamed(name), value, std::move(index), num);
}

PLI_INT32 PutRaw(const char* name, PLI_INT32 format,
                 const std::vector<int>& bytes, PLI_UINT32 num,
                 PLI_UINT32 flags = 0) {
  s_vpi_arrayvalue value = {};
  value.format = format;
  value.flags = flags;
  return PutRawValue(name, value, bytes, num, {0});
}

PLI_INT32 PutFourStateFrom(const char* name, const std::vector<int>& bytes,
                           PLI_UINT32 num, std::vector<PLI_INT32> index,
                           PLI_UINT32 flags) {
  s_vpi_arrayvalue value = {};
  value.format = vpiRawFourStateVal;
  value.flags = flags;
  return PutRawValue(name, value, bytes, num, std::move(index));
}

PLI_INT32 PutVectors(const char* name, std::vector<s_vpi_vecval> words,
                     PLI_UINT32 num, PLI_UINT32 flags = 0) {
  s_vpi_arrayvalue value = {};
  value.format = vpiVectorVal;
  value.flags = flags;
  value.value.vectors = words.data();
  return PutArrayAt(HandleNamed(name), value, {0}, num);
}

std::string Zeros(std::size_t count) { return std::string(count, '0'); }

class ArrayValuesOfARun : public ArrayPutsOfARun {
 protected:
  static void ExpectBits(const std::vector<const char*>& names,
                         const std::vector<std::string>& bits) {
    ASSERT_EQ(names.size(), bits.size());
    for (std::size_t i = 0; i < names.size(); ++i) {
      EXPECT_EQ(BitsNamed(names[i]), bits[i]) << names[i];
    }
  }
};

TEST_F(ArrayValuesOfARun, ATimeArrayTakesBothWordsOfEachTime) {
  Run("module top; time t [2]; initial $noop; endmodule\n");
  s_vpi_time times[2] = {{vpiSimTime, 1, 2, 0.0}, {vpiSimTime, 3, 4, 0.0}};
  s_vpi_arrayvalue value = {};
  value.format = vpiTimeVal;
  value.value.times = times;
  EXPECT_EQ(PutArrayAt(HandleNamed("top.t"), value, {0}, 2), 0);
  for (int i = 0; i < 2; ++i) {
    s_vpi_value read = {};
    read.format = vpiTimeVal;
    vpi_get_value(vpi_handle_by_index(HandleNamed("top.t"), i), &read);
    ASSERT_NE(read.value.time, nullptr);
    EXPECT_EQ(read.value.time->high, static_cast<PLI_UINT32>((2 * i) + 1));
    EXPECT_EQ(read.value.time->low, static_cast<PLI_UINT32>((2 * i) + 2));
  }
}

TEST_F(ArrayValuesOfARun, VectorsTakeTheirAvalAndBvalWordsPerElement) {
  Run("module top; logic [31:0] n [2]; logic [63:0] w [2]; initial $noop;\n"
      "endmodule\n");
  EXPECT_EQ(PutVectors("top.n", {{0xF, 0x3}, {0xF0, 0x30}}, 2), 0);
  EXPECT_EQ(PutVectors("top.w",
                       {{0x1, 0x2}, {0x4, 0x8}, {0x10, 0x20}, {0x40, 0x80}}, 2),
            0);
  ExpectBits({"top.n[0]", "top.n[1]", "top.w[0]", "top.w[1]"},
             {Zeros(28) + "11xx", Zeros(24) + "11xx0000",
              Zeros(28) + "z1" + Zeros(32) + "z1",
              Zeros(24) + "z1" + Zeros(32) + "z1" + Zeros(4)});
}

TEST_F(ArrayValuesOfARun, IndicesNameEachUnpackedDimensionFromTheLeft) {
  Run("module top; int m [2][3]; int a [5:8] = '{1, 2, 3, 4};\n"
      "  initial $noop;\n"
      "endmodule\n");
  EXPECT_EQ(PutInts("top.m", {1, 1}, {7, 8}), 0);
  EXPECT_EQ(
      IntsNamed({"top.m[1][0]", "top.m[1][1]", "top.m[1][2]", "top.m[0][1]"}),
      (std::vector<int>{0, 7, 8, 0}));
  EXPECT_EQ(PutInts("top.a", {6}, {7, 8}), 0);
  EXPECT_EQ(PutInts("top.a", {0}, {9}), vpiError);
  EXPECT_EQ(PutInts("top.a", {1}, {9}), vpiError);
  EXPECT_EQ(IntsNamed({"top.a[5]", "top.a[6]", "top.a[7]", "top.a[8]"}),
            (std::vector<int>{1, 7, 8, 4}));
}

TEST_F(ArrayValuesOfARun, ElementsRunFromTheStartTowardTheRightBound) {
  Run("module top; int a [3:0] = '{1, 1, 1, 1}; int m [1:0][0:2];\n"
      "  initial $noop;\n"
      "endmodule\n");
  EXPECT_EQ(PutInts("top.a", {2}, {7, 8, 9}), 0);
  EXPECT_EQ(IntsNamed({"top.a[3]", "top.a[2]", "top.a[1]", "top.a[0]"}),
            (std::vector<int>{1, 7, 8, 9}));
  EXPECT_EQ(PutInts("top.m", {1, 1}, {2, 3, 4, 5}), 0);
  EXPECT_EQ(IntsNamed({"top.m[1][0]", "top.m[1][1]", "top.m[1][2]",
                       "top.m[0][0]", "top.m[0][1]", "top.m[0][2]"}),
            (std::vector<int>{0, 2, 3, 4, 5, 0}));
}

TEST_F(ArrayValuesOfARun, ARawBvalByteOneIsBitEight) {
  Run("module top; logic [15:0] l [1]; initial $noop; endmodule\n");
  EXPECT_EQ(PutRaw("top.l", vpiRawFourStateVal, {0x01, 0x00, 0x01, 0x02}, 1),
            0);
  EXPECT_EQ(BitsNamed("top.l[0]"), "000000z00000000x");
}

TEST_F(ArrayValuesOfARun, RawFourStateElementsFollowEachOtherAvalThenBval) {
  Run("module top; logic [15:0] l [2]; initial $noop; endmodule\n");
  EXPECT_EQ(PutRaw("top.l", vpiRawFourStateVal,
                   {0x01, 0x00, 0x00, 0x00, 0x02, 0x00, 0x00, 0x80}, 2),
            0);
  ExpectBits({"top.l[0]", "top.l[1]"},
             {Zeros(15) + "1", "z" + Zeros(13) + "10"});
}

TEST_F(ArrayValuesOfARun, TheStandardsExampleWritesFiveFortyTwoBitElements) {
  Run("module top; logic [41:0] a [2:0][3:5]; initial $noop; endmodule\n");
  std::vector<int> bytes(60, 0);
  for (std::size_t n = 0; n < 4; ++n) {
    bytes[n * 12] = static_cast<int>(n) + 1;
    bytes[(n * 12) + 5] = 0xFC;
  }
  for (std::size_t i = 48; i < 60; ++i) bytes[i] = 0xFF;
  EXPECT_EQ(PutFourStateFrom("top.a", bytes, 5, {1, 4}, vpiPropagateOff), 0);
  ExpectBits({"top.a[1][4]", "top.a[1][5]", "top.a[0][3]", "top.a[0][4]",
              "top.a[0][5]", "top.a[1][3]"},
             {Zeros(41) + "1", Zeros(40) + "10", Zeros(40) + "11",
              Zeros(39) + "100", std::string(42, 'x'), std::string(42, 'x')});
}

TEST_F(ArrayValuesOfARun, RawFourStateKeepsBvalInEveryFourStateArray) {
  Run("module top;\n"
      "  typedef struct packed { logic [3:0] h; logic [3:0] l; } s_t;\n"
      "  typedef union packed { logic [7:0] a; logic [7:0] b; } u_t;\n"
      "  logic [7:0] l [1]; integer i [1]; time t [1]; s_t s [1]; u_t u [1];\n"
      "  initial $noop;\n"
      "endmodule\n");
  for (const char* name : {"top.l", "top.s", "top.u"}) {
    EXPECT_EQ(PutRaw(name, vpiRawFourStateVal, {0x05, 0x01}, 1), 0) << name;
  }
  std::vector<int> wide(16, 0);
  wide[0] = 0x05;
  wide[8] = 0x01;
  EXPECT_EQ(PutRaw("top.t", vpiRawFourStateVal, wide, 1), 0);
  wide.resize(8);
  wide[4] = 0x01;
  EXPECT_EQ(PutRaw("top.i", vpiRawFourStateVal, wide, 1), 0);
  ExpectBits({"top.l[0]", "top.s[0]", "top.u[0]", "top.i[0]", "top.t[0]"},
             {"0000010x", "0000010x", "0000010x", Zeros(29) + "10x",
              Zeros(61) + "10x"});
}

TEST_F(ArrayValuesOfARun, RawTwoStateTakesOnlyAvalInEveryTwoStateArray) {
  Run("module top;\n"
      "  typedef struct packed { bit [3:0] h; bit [3:0] l; } s_t;\n"
      "  typedef union packed { bit [7:0] a; byte b; } u_t;\n"
      "  bit [7:0] v [2]; byte b [2]; s_t s [2]; u_t u [2];\n"
      "  shortint h [2]; int i [2]; longint g [2];\n"
      "  initial $noop;\n"
      "endmodule\n");
  for (const char* name : {"top.v", "top.b", "top.s", "top.u"}) {
    EXPECT_EQ(PutRaw(name, vpiRawTwoStateVal, {0x05, 0x06}, 2), 0) << name;
  }
  EXPECT_EQ(PutRaw("top.h", vpiRawTwoStateVal, {0x05, 0, 0x06, 0}, 2), 0);
  std::vector<int> words(8, 0);
  words[0] = 0x05;
  words[4] = 0x06;
  EXPECT_EQ(PutRaw("top.i", vpiRawTwoStateVal, words, 2), 0);
  words.resize(16, 0);
  words[4] = 0;
  words[8] = 0x06;
  EXPECT_EQ(PutRaw("top.g", vpiRawTwoStateVal, words, 2), 0);
  ExpectBits({"top.v[1]", "top.b[1]", "top.s[1]", "top.u[1]", "top.h[1]",
              "top.i[1]", "top.g[1]", "top.g[0]"},
             {"00000110", "00000110", "00000110", "00000110", Zeros(13) + "110",
              Zeros(29) + "110", Zeros(61) + "110", Zeros(61) + "101"});
}

TEST_F(ArrayValuesOfARun, TheOtherRawFormIgnoresBvalOrTakesItAsZero) {
  Run("module top; bit [7:0] b [2]; logic [15:0] l [2]; initial $noop;\n"
      "endmodule\n");
  EXPECT_EQ(PutRaw("top.b", vpiRawFourStateVal, {0x05, 0x01, 0x06, 0xFF}, 2),
            0);
  EXPECT_EQ(PutRaw("top.l", vpiRawTwoStateVal, {0x05, 0x00, 0x06, 0x00}, 2), 0);
  ExpectBits({"top.b[0]", "top.b[1]", "top.l[0]", "top.l[1]"},
             {"00000101", "00000110", Zeros(13) + "101", Zeros(13) + "110"});
}

TEST_F(ArrayValuesOfARun, DISABLED_RawFourStateKeepsBvalInANetArray) {
  Run("module top; wire [7:0] w [1]; initial $noop; endmodule\n");
  EXPECT_EQ(PutRaw("top.w", vpiRawFourStateVal, {0x05, 0x01}, 1), 0);
  EXPECT_EQ(BitsNamed("top.w[0]"), "0000010x");
}

TEST_F(ArrayValuesOfARun, OneValueFillsTheRunFromItsFirstElementOnly) {
  Run("module top; logic [15:0] l [3]; logic [39:0] v [3]; initial $noop;\n"
      "endmodule\n");
  EXPECT_EQ(PutRaw("top.l", vpiRawFourStateVal, {0x34, 0x12, 0x00, 0x00}, 3,
                   vpiOneValue),
            0);
  EXPECT_EQ(PutVectors("top.v", {{0x11223344, 0}, {0x55, 0}}, 3, vpiOneValue),
            0);
  const std::string kL = "0001001000110100";
  const std::string kV = "0101010100010001001000100011001101000100";
  ExpectBits(
      {"top.l[0]", "top.l[1]", "top.l[2]", "top.v[0]", "top.v[1]", "top.v[2]"},
      {kL, kL, kL, kV, kV, kV});
}

TEST_F(ArrayValuesOfARun, PropagateOffWakesNoFanoutOfTheWrittenElements) {
  Putter() = [] {
    PutInts("top.a", {0}, {4, 5});
    PutInts("top.b", {0}, {4, 5}, vpiPropagateOff);
    PutOneInt("top.c", 6, 3, vpiPropagateOff);
  };
  Run("module top; int a [2], b [2], c [3]; int wa, wb, wc;\n"
      "  wire [31:0] ca = a[1], cb = b[1], cc = c[2]; int ka, kb, kc;\n"
      "  always @(a[1]) wa++; always @(b[1]) wb++; always @(c[2]) wc++;\n"
      "  initial begin #1 $put; #1 begin ka = ca; kb = cb; kc = cc; end end\n"
      "endmodule\n");
  EXPECT_EQ(
      IntsNamed({"top.wa", "top.ka", "top.wb", "top.kb", "top.wc", "top.kc"}),
      (std::vector<int>{1, 5, 0, 0, 0, 0}));
  EXPECT_EQ(IntsNamed({"top.b[1]", "top.c[0]", "top.c[1]", "top.c[2]"}),
            (std::vector<int>{5, 6, 6, 6}));
}

TEST_F(ArrayValuesOfARun, DISABLED_ANetArrayHoldsThePutUntilAnElementsDriver) {
  Putter() = [] { PutInts("top.w", {0}, {5, 6}); };
  Run("module top; logic [7:0] d0 = 1, d1 = 1; wire [7:0] w [2];\n"
      "  assign w[0] = d0; assign w[1] = d1; int k0, k1, j0, j1;\n"
      "  initial begin #1 $put; #1 begin k0 = w[0]; k1 = w[1]; end\n"
      "    #1 d0 = 3; #1 begin j0 = w[0]; j1 = w[1]; end end\n"
      "endmodule\n");
  EXPECT_EQ(IntsNamed({"top.k0", "top.k1", "top.j0", "top.j1"}),
            (std::vector<int>{5, 6, 3, 6}));
  EXPECT_EQ(IntsNamed({"top.w[0]", "top.w[1]"}), (std::vector<int>{3, 6}));
}

}  // namespace
}  // namespace delta
