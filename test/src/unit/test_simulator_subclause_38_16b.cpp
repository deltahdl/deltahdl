#include <gtest/gtest.h>

#include <cstddef>
#include <cstring>
#include <utility>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

using ArrayValueArms = decltype(s_vpi_arrayvalue::value);

constexpr unsigned char kGuard = 0xA5;

struct Section {
  std::vector<PLI_INT32> index;
  PLI_UINT32 num = 0;
};

template <typename T>
struct Reading {
  bool error = false;
  bool kept = false;
  std::vector<T> items;
};

template <typename T>
bool Untouched(const T& item) {
  const auto* bytes = reinterpret_cast<const unsigned char*>(&item);
  for (std::size_t k = 0; k < sizeof(T); ++k) {
    if (bytes[k] != kGuard) return false;
  }
  return true;
}

class ArrayReadsOfARun : public VpiDesignRun {
 protected:
  template <typename T>
  static Reading<T> ReadInto(const char* name, PLI_UINT32 format,
                             T* ArrayValueArms::* arm, Section section,
                             std::size_t count) {
    std::vector<T> buffer(count + 1);
    std::memset(static_cast<void*>(buffer.data()), kGuard,
                sizeof(T) * buffer.size());
    s_vpi_arrayvalue av = {};
    av.format = format;
    av.flags = vpiUserAllocFlag;
    av.value.*arm = buffer.data();
    vpi_get_value_array(By(name), &av, section.index.data(), section.num);
    s_vpi_error_info info = {};
    const PLI_INT32 kLevel = vpi_chk_error(&info);
    Reading<T> reading;
    reading.error = kLevel == vpiError;
    reading.kept = av.value.*arm == buffer.data();
    reading.items = buffer;
    return reading;
  }

  static std::vector<int> Bytes(const char* name, PLI_UINT32 format,
                                std::vector<PLI_INT32> index, PLI_UINT32 num,
                                std::size_t count) {
    const Reading<PLI_BYTE8> kRead = ReadInto(
        name, format, &ArrayValueArms::rawvals, {std::move(index), num}, count);
    std::vector<int> bytes;
    if (kRead.error || !kRead.kept) return bytes;
    for (std::size_t k = 0; k < count; ++k) {
      bytes.push_back(static_cast<unsigned char>(kRead.items[k]));
    }
    EXPECT_TRUE(Untouched(kRead.items[count])) << name;
    return bytes;
  }

  static std::vector<PLI_UINT32> Words(const char* name,
                                       std::vector<PLI_INT32> index,
                                       PLI_UINT32 num, std::size_t count) {
    const Reading<s_vpi_vecval> kRead =
        ReadInto(name, vpiVectorVal, &ArrayValueArms::vectors,
                 {std::move(index), num}, count);
    std::vector<PLI_UINT32> words;
    if (kRead.error || !kRead.kept) return words;
    for (std::size_t k = 0; k < count; ++k) {
      words.push_back(kRead.items[k].aval);
      words.push_back(kRead.items[k].bval);
    }
    EXPECT_TRUE(Untouched(kRead.items[count])) << name;
    return words;
  }

  static std::vector<PLI_INT32> Ints(const char* name,
                                     std::vector<PLI_INT32> index,
                                     PLI_UINT32 num) {
    Reading<PLI_INT32> read =
        ReadInto(name, vpiIntVal, &ArrayValueArms::integers,
                 {std::move(index), num}, num);
    if (read.error || !read.kept) return {};
    EXPECT_TRUE(Untouched(read.items[num])) << name;
    read.items.pop_back();
    return read.items;
  }

  template <typename T>
  static std::vector<T> Numbers(const char* name, PLI_UINT32 format,
                                T* ArrayValueArms::* arm) {
    Reading<T> read = ReadInto(name, format, arm, {{0}, 3}, 3);
    if (read.error || !read.kept) return {};
    EXPECT_TRUE(Untouched(read.items[3])) << name;
    read.items.pop_back();
    return read.items;
  }
};

TEST_F(ArrayReadsOfARun, EachNumericFormatWritesNumElementsAndNoMore) {
  Run("module top;\n"
      "  int ia[4] = '{1, 2, 3, 4}; shortint sa[4] = '{5, 6, 7, 8};\n"
      "  longint la[4] = '{9, 10, 11, 12};\n"
      "  real ra[4] = '{0.5, 1.5, 2.5, 3.5};\n"
      "  shortreal fa[4] = '{0.25, 0.75, 1.25, 1.75};\n"
      "  time ta[4] = '{10, 20, 30, 40};\n"
      "  initial $noop;\n"
      "endmodule\n");
  EXPECT_EQ(Numbers("top.ia", vpiIntVal, &ArrayValueArms::integers),
            (std::vector<PLI_INT32>{1, 2, 3}));
  EXPECT_EQ(Numbers("top.sa", vpiShortIntVal, &ArrayValueArms::shortints),
            (std::vector<PLI_INT16>{5, 6, 7}));
  EXPECT_EQ(Numbers("top.la", vpiLongIntVal, &ArrayValueArms::longints),
            (std::vector<PLI_INT64>{9, 10, 11}));
  EXPECT_EQ(Numbers("top.ra", vpiRealVal, &ArrayValueArms::reals),
            (std::vector<double>{0.5, 1.5, 2.5}));
  EXPECT_EQ(Numbers("top.fa", vpiShortRealVal, &ArrayValueArms::shortreals),
            (std::vector<float>{0.25f, 0.75f, 1.25f}));
  const Reading<s_vpi_time> kTimes =
      ReadInto("top.ta", vpiTimeVal, &ArrayValueArms::times, {{0}, 3}, 3);
  ASSERT_FALSE(kTimes.error);
  ASSERT_TRUE(kTimes.kept);
  EXPECT_EQ(kTimes.items[0].low, 10u);
  EXPECT_EQ(kTimes.items[1].low, 20u);
  EXPECT_EQ(kTimes.items[2].low, 30u);
  EXPECT_TRUE(Untouched(kTimes.items[3]));
}

TEST_F(ArrayReadsOfARun, RawAndVectorFormatsFillTheirFormulaAndNoMore) {
  Run("module top;\n"
      "  logic [11:0] w[3] = '{12'hABC, 12'h123, 12'h456};\n"
      "  logic [39:0] v[3] = '{40'h01_11111111, 40'h02_22222222,\n"
      "                        40'h03_33333333};\n"
      "  initial $noop;\n"
      "endmodule\n");
  EXPECT_EQ(Bytes("top.w", vpiRawFourStateVal, {0}, 2, 8),
            (std::vector<int>{0xBC, 0x0A, 0, 0, 0x23, 0x01, 0, 0}));
  EXPECT_EQ(Bytes("top.w", vpiRawTwoStateVal, {0}, 2, 4),
            (std::vector<int>{0xBC, 0x0A, 0x23, 0x01}));
  EXPECT_EQ(Words("top.v", {0}, 2, 4),
            (std::vector<PLI_UINT32>{0x11111111u, 0u, 0x01u, 0u, 0x22222222u,
                                     0u, 0x02u, 0u}));
}

TEST_F(ArrayReadsOfARun, RawFormatsPlaceEachByteGroupOfANarrowElement) {
  Run("module top;\n"
      "  logic [15:0] h[2] = '{16'b0000000z_00110100, 16'hBEEF};\n"
      "  logic [8:0] n[2] = '{9'h1A5, 9'bx_0000_0011};\n"
      "  initial $noop;\n"
      "endmodule\n");
  EXPECT_EQ(Bytes("top.h", vpiRawFourStateVal, {0}, 2, 8),
            (std::vector<int>{0x34, 0, 0, 0x01, 0xEF, 0xBE, 0, 0}));
  EXPECT_EQ(Bytes("top.n", vpiRawFourStateVal, {0}, 2, 8),
            (std::vector<int>{0xA5, 0x01, 0, 0, 0x03, 0x01, 0, 0x01}));
  EXPECT_EQ(Bytes("top.h", vpiRawTwoStateVal, {0}, 2, 4),
            (std::vector<int>{0x34, 0, 0xEF, 0xBE}));
  EXPECT_EQ(Bytes("top.n", vpiRawTwoStateVal, {0}, 2, 4),
            (std::vector<int>{0xA5, 0x01, 0x03, 0x01}));
}

TEST_F(ArrayReadsOfARun, VectorFormatTakesOneOrTwoWordsAtTheBoundaries) {
  Run("module top;\n"
      "  logic [31:0] a32[2] = '{32'h123456x8, 32'hCAFEF00D};\n"
      "  logic [63:0] a64[2] = '{64'h0000000z_11111111,\n"
      "                          64'h33333333_22222222};\n"
      "  initial $noop;\n"
      "endmodule\n");
  EXPECT_EQ(Words("top.a32", {0}, 2, 2),
            (std::vector<PLI_UINT32>{0x123456F8u, 0xF0u, 0xCAFEF00Du, 0u}));
  EXPECT_EQ(Words("top.a64", {0}, 2, 4),
            (std::vector<PLI_UINT32>{0x11111111u, 0u, 0u, 0xFu, 0x22222222u, 0u,
                                     0x33333333u, 0u}));
}

constexpr const char* kSection =
    "module top;\n"
    "  logic [7:0] a[2:0][3:5] = '{'{8'h23, 8'h24, 8'h25},\n"
    "                              '{8'h13, 8'h14, 8'h15},\n"
    "                              '{8'h03, 8'h0z, 8'h05}};\n"
    "  time t[2] = '{64'd5000000000, 64'd7};\n"
    "  initial $noop;\n"
    "endmodule\n";

TEST_F(ArrayReadsOfARun, TheRawFormatsFillTheApplicationsBuffer) {
  Run(kSection);
  EXPECT_EQ(Bytes("top.a", vpiRawFourStateVal, {1, 4}, 5, 10),
            (std::vector<int>{0x14, 0, 0x15, 0, 0x03, 0, 0, 0x0F, 0x05, 0}));
  EXPECT_EQ(Bytes("top.a", vpiRawTwoStateVal, {1, 4}, 5, 5),
            (std::vector<int>{0x14, 0x15, 0x03, 0, 0x05}));
}

TEST_F(ArrayReadsOfARun, TheVectorAndTimeFormatsFillTheApplicationsBuffer) {
  Run(kSection);
  EXPECT_EQ(Words("top.a", {1, 4}, 5, 5),
            (std::vector<PLI_UINT32>{0x14u, 0u, 0x15u, 0u, 0x03u, 0u, 0u, 0x0Fu,
                                     0x05u, 0u}));
  const Reading<s_vpi_time> kTimes =
      ReadInto("top.t", vpiTimeVal, &ArrayValueArms::times, {{0}, 2}, 2);
  ASSERT_FALSE(kTimes.error);
  ASSERT_TRUE(kTimes.kept);
  EXPECT_EQ(kTimes.items[0].high, 1u);
  EXPECT_EQ(kTimes.items[0].low, 705032704u);
  EXPECT_EQ(kTimes.items[1].high, 0u);
  EXPECT_EQ(kTimes.items[1].low, 7u);
  EXPECT_TRUE(Untouched(kTimes.items[2]));
}

TEST_F(ArrayReadsOfARun, AStartingIndexNamesEveryDimensionLeftToRight) {
  Run("module top;\n"
      "  int c[2][3][4];\n"
      "  initial foreach (c[i, j, k]) c[i][j][k] = i * 100 + j * 10 + k;\n"
      "endmodule\n");
  EXPECT_EQ(Ints("top.c", {0, 2, 3}, 3),
            (std::vector<PLI_INT32>{23, 100, 101}));
}

TEST_F(ArrayReadsOfARun,
       DISABLED_AnUnpackedTypedefOfTheElementAddsItsDimension) {
  Run("module top;\n"
      "  typedef logic [7:0] row_t [0:2]; row_t m [0:1];\n"
      "  typedef int t [2]; t q [3];\n"
      "  initial begin\n"
      "    foreach (m[i, j]) m[i][j] = i * 16 + j;\n"
      "    foreach (q[i, j]) q[i][j] = i * 10 + j;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(Ints("top.m", {1, 1}, 2), (std::vector<PLI_INT32>{0x11, 0x12}));
  EXPECT_EQ(Ints("top.q", {0, 0}, 6),
            (std::vector<PLI_INT32>{0, 1, 10, 11, 20, 21}));
  EXPECT_TRUE(
      ReadInto("top.q", vpiIntVal, &ArrayValueArms::integers, {{0}, 2}, 2)
          .error);
}

TEST_F(ArrayReadsOfARun, ADescendingRangeIsWalkedFromItsLeftBound) {
  Run("module top; int d[3:0] = '{40, 30, 20, 10}; initial $noop; "
      "endmodule\n");
  EXPECT_EQ(Ints("top.d", {3}, 3), (std::vector<PLI_INT32>{40, 30, 20}));
}

TEST_F(ArrayReadsOfARun, APackedStructElementReadsAsItsPackedValue) {
  Run("module top;\n"
      "  typedef struct packed { logic [7:0] hi, lo; } p_t;\n"
      "  p_t a[4] = '{16'h1234, 16'h5678, 16'h9ABC, 16'hDEF0};\n"
      "  initial $noop;\n"
      "endmodule\n");
  EXPECT_EQ(Ints("top.a", {0}, 4),
            (std::vector<PLI_INT32>{0x1234, 0x5678, 0x9ABC, 0xDEF0}));
}

TEST_F(ArrayReadsOfARun, EveryIntegralElementKindIsReadInEachRawOrVectorForm) {
  Run("module top;\n"
      "  typedef struct packed { logic [3:0] a, b; } s4_t;\n"
      "  typedef union packed { logic [7:0] a; logic [7:0] b; } u4_t;\n"
      "  typedef struct packed { bit [3:0] a, b; } s2_t;\n"
      "  typedef union packed { bit [7:0] a; bit [7:0] b; } u2_t;\n"
      "  integer ig[2] = '{32'h5A, 1}; time tm[2] = '{64'h5A, 1};\n"
      "  s4_t s4[2] = '{8'h5A, 1}; u4_t u4[2] = '{8'h5A, 1};\n"
      "  bit [7:0] bt[2] = '{8'h5A, 1}; byte by[2] = '{8'h5A, 1};\n"
      "  shortint sh[2] = '{16'h5A, 1}; int it[2] = '{32'h5A, 1};\n"
      "  longint lg[2] = '{64'h5A, 1};\n"
      "  s2_t s2[2] = '{8'h5A, 1}; u2_t u2[2] = '{8'h5A, 1};\n"
      "endmodule\n");
  for (const char* name :
       {"top.ig", "top.tm", "top.s4", "top.u4", "top.bt", "top.by", "top.sh",
        "top.it", "top.lg", "top.s2", "top.u2"}) {
    for (const PLI_UINT32 kFormat :
         {static_cast<PLI_UINT32>(vpiRawFourStateVal),
          static_cast<PLI_UINT32>(vpiRawTwoStateVal)}) {
      const Reading<PLI_BYTE8> kRead =
          ReadInto(name, kFormat, &ArrayValueArms::rawvals, {{0}, 1}, 16);
      EXPECT_FALSE(kRead.error) << name << " " << kFormat;
      EXPECT_EQ(static_cast<unsigned char>(kRead.items[0]), 0x5A)
          << name << " " << kFormat;
    }
    const Reading<s_vpi_vecval> kVector =
        ReadInto(name, vpiVectorVal, &ArrayValueArms::vectors, {{0}, 1}, 2);
    EXPECT_FALSE(kVector.error) << name;
    EXPECT_EQ(kVector.items[0].aval, 0x5Au) << name;
  }
}

TEST_F(ArrayReadsOfARun, DISABLED_ANetArrayIsReadInEachRawOrVectorForm) {
  Run("module top;\n"
      "  wire [7:0] nt[2]; assign nt[0] = 8'h5A; assign nt[1] = 8'h01;\n"
      "endmodule\n");
  EXPECT_EQ(Bytes("top.nt", vpiRawFourStateVal, {0}, 2, 4),
            (std::vector<int>{0x5A, 0, 0x01, 0}));
  EXPECT_EQ(Bytes("top.nt", vpiRawTwoStateVal, {0}, 2, 2),
            (std::vector<int>{0x5A, 0x01}));
  EXPECT_EQ(Words("top.nt", {0}, 2, 2),
            (std::vector<PLI_UINT32>{0x5Au, 0u, 0x01u, 0u}));
}

}  // namespace
}  // namespace delta
