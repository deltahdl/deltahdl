#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <type_traits>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_dpi_c_binding.h"
#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"
#include "simulator/dpi_runtime.h"
#include "simulator/svdpi.h"

using namespace delta;

namespace {

TEST(SvDpi, BitSelectBit) {
  svBitVecVal bv = 0x0A;
  EXPECT_EQ(svGetBitselBit(&bv, 0), 0u);
  EXPECT_EQ(svGetBitselBit(&bv, 1), 1u);
  EXPECT_EQ(svGetBitselBit(&bv, 2), 0u);
  EXPECT_EQ(svGetBitselBit(&bv, 3), 1u);
}

TEST(SvDpi, BitSelectLogic) {
  svLogicVecVal lv;
  lv.aval = 0x03;
  lv.bval = 0x02;

  EXPECT_EQ(svGetBitselLogic(&lv, 0), sv_1);

  EXPECT_EQ(svGetBitselLogic(&lv, 1), sv_x);
}

TEST(SvDpi, PutBitSelectBit) {
  svBitVecVal bv = 0;
  svPutBitselBit(&bv, 3, 1);
  EXPECT_EQ(bv, 8u);
  svPutBitselBit(&bv, 3, 0);
  EXPECT_EQ(bv, 0u);
}

TEST(SvDpi, PutBitSelectLogic) {
  svLogicVecVal lv = {0, 0};
  svPutBitselLogic(&lv, 0, sv_1);
  EXPECT_EQ(lv.aval, 1u);
  EXPECT_EQ(lv.bval, 0u);
  svPutBitselLogic(&lv, 2, sv_z);
  EXPECT_EQ(lv.aval & (1u << 2), 0u);
  EXPECT_EQ(lv.bval & (1u << 2), 4u);
}

TEST(SvDpi, PutPartSelectBit) {
  svBitVecVal dst = 0;
  svBitVecVal src = 0x0F;
  svPutPartselBit(&dst, src, 4, 8);
  EXPECT_EQ(dst, 0xF0u);
}

TEST(SvDpi, PutPartSelectBitPreservesSurrounding) {
  svBitVecVal dst = 0xFFFFFFFFu;
  svBitVecVal src = 0x00u;
  svPutPartselBit(&dst, src, 4, 8);
  EXPECT_EQ((dst >> 4) & 0xFFu, 0u);
  EXPECT_EQ(dst & 0xFu, 0xFu);
  EXPECT_EQ(dst >> 12, 0xFFFFFu);
}

TEST(SvDpi, PutPartSelectLogicPreservesSurrounding) {
  svLogicVecVal dst;
  dst.aval = 0xFFFFFFFFu;
  dst.bval = 0x00000000u;
  svLogicVecVal src;
  src.aval = 0x00u;
  src.bval = 0x00u;
  svPutPartselLogic(&dst, src, 4, 8);
  EXPECT_EQ((dst.aval >> 4) & 0xFFu, 0u);
  EXPECT_EQ(dst.aval & 0xFu, 0xFu);
  EXPECT_EQ(dst.aval >> 12, 0xFFFFFu);
  EXPECT_EQ(dst.bval, 0u);
}

TEST(SvDpi, GetPartSelectBitPreservesHighBits) {
  svBitVecVal src = 0xABCDEF12u;
  svBitVecVal dst = 0xFFFFFFFFu;
  svGetPartselBit(&dst, &src, 4, 8);
  EXPECT_EQ(dst & 0xFFu, (src >> 4) & 0xFFu);
  EXPECT_EQ(dst >> 8, 0xFFFFFFu);
}

TEST(SvDpi, GetPartSelectLogicPreservesHighBits) {
  svLogicVecVal src;
  src.aval = 0xABCDEF12u;
  src.bval = 0x00000000u;
  svLogicVecVal dst;
  dst.aval = 0xFFFFFFFFu;
  dst.bval = 0xFFFFFFFFu;
  svGetPartselLogic(&dst, &src, 4, 8);
  EXPECT_EQ(dst.aval & 0xFFu, (src.aval >> 4) & 0xFFu);
  EXPECT_EQ(dst.bval & 0xFFu, 0u);
  EXPECT_EQ(dst.aval >> 8, 0xFFFFFFu);
  EXPECT_EQ(dst.bval >> 8, 0xFFFFFFu);
}

TEST(SvDpi, BitSelectUpperWord) {
  svBitVecVal bv[3] = {0u, 0u, 0u};
  bv[2] = 1u << 2;
  EXPECT_EQ(svGetBitselBit(bv, 66), 1u);
  EXPECT_EQ(svGetBitselBit(bv, 65), 0u);

  svPutBitselBit(bv, 33, 1);
  EXPECT_EQ(bv[1], 1u << 1);
  svPutBitselBit(bv, 66, 0);
  EXPECT_EQ(bv[2], 0u);
}

TEST(SvDpi, BitSelectLogicUpperWord) {
  svLogicVecVal lv[3] = {{0, 0}, {0, 0}, {0, 0}};
  svPutBitselLogic(lv, 34, sv_z);
  EXPECT_EQ(lv[1].aval, 0u);
  EXPECT_EQ(lv[1].bval, 1u << 2);
  EXPECT_EQ(svGetBitselLogic(lv, 34), sv_z);
}

TEST(SvDpi, GetPartSelectBitAcrossWordBoundary) {
  svBitVecVal src[2] = {0x80000000u, 0x0000000Fu};
  svBitVecVal dst = 0xFFFFFFFFu;
  svGetPartselBit(&dst, src, 28, 8);
  EXPECT_EQ(dst & 0xFFu, 0xF8u);
  EXPECT_EQ(dst >> 8, 0xFFFFFFu);
}

TEST(SvDpi, GetPartSelectLogicAcrossWordBoundary) {
  svLogicVecVal src[2] = {{0x80000000u, 0u}, {0x0000000Fu, 0u}};
  svLogicVecVal dst = {0xFFFFFFFFu, 0xFFFFFFFFu};
  svGetPartselLogic(&dst, src, 28, 8);
  EXPECT_EQ(dst.aval & 0xFFu, 0xF8u);
  EXPECT_EQ(dst.bval & 0xFFu, 0u);
  EXPECT_EQ(dst.aval >> 8, 0xFFFFFFu);
  EXPECT_EQ(dst.bval >> 8, 0xFFFFFFu);
}

TEST(SvDpi, PutPartSelectBitAcrossWordBoundary) {
  svBitVecVal dst[2] = {0x0FFFFFFFu, 0xFFFFFFF0u};
  svPutPartselBit(dst, 0xFFu, 28, 8);
  EXPECT_EQ(dst[0], 0xFFFFFFFFu);
  EXPECT_EQ(dst[1], 0xFFFFFFFFu);
}

TEST(SvDpi, PutPartSelectLogicAcrossWordBoundary) {
  svLogicVecVal dst[2] = {{0u, 0u}, {0u, 0u}};
  svLogicVecVal src = {0xFFu, 0x00u};
  svPutPartselLogic(dst, src, 28, 8);
  EXPECT_EQ(dst[0].aval, 0xF0000000u);
  EXPECT_EQ(dst[1].aval, 0x0000000Fu);
  EXPECT_EQ(dst[0].bval, 0u);
  EXPECT_EQ(dst[1].bval, 0u);
}

TEST(SvDpi, PartSelectFullWidthWord) {
  svBitVecVal src = 0xDEADBEEFu;
  svBitVecVal getdst = 0x12345678u;
  svGetPartselBit(&getdst, &src, 0, 32);
  EXPECT_EQ(getdst, 0xDEADBEEFu);

  svBitVecVal putdst = 0u;
  svPutPartselBit(&putdst, 0xDEADBEEFu, 0, 32);
  EXPECT_EQ(putdst, 0xDEADBEEFu);
}

TEST(SvDpi, AWidthOutsideTheLimitIsIgnoredByChoice) {
  svBitVecVal src = 0xFFFFFFFFu;
  svBitVecVal getdst = 0x12345678u;
  svGetPartselBit(&getdst, &src, 0, 33);
  EXPECT_EQ(getdst, 0x12345678u);
  svGetPartselBit(&getdst, &src, 0, 0);
  EXPECT_EQ(getdst, 0x12345678u);

  svBitVecVal putdst = 0x12345678u;
  svPutPartselBit(&putdst, 0xFFu, 0, 33);
  EXPECT_EQ(putdst, 0x12345678u);
  svPutPartselBit(&putdst, 0xFFu, 0, 0);
  EXPECT_EQ(putdst, 0x12345678u);
}

delta::DpiArg PackedFormal(delta::DataTypeKind type, uint32_t width) {
  delta::DpiArg formal;
  formal.name = "a";
  formal.type = type;
  formal.direction = delta::Direction::kInput;
  formal.width = width;
  return formal;
}

TEST(DpiCanonicalUtilities, APartSelectIsASliceOfAPackedBitOrLogicArray) {
  using delta::DataTypeKind;
  EXPECT_TRUE(
      delta::DpiPartSelectAppliesTo(PackedFormal(DataTypeKind::kBit, 8)));
  EXPECT_TRUE(
      delta::DpiPartSelectAppliesTo(PackedFormal(DataTypeKind::kLogic, 18)));
  EXPECT_TRUE(
      delta::DpiPartSelectAppliesTo(PackedFormal(DataTypeKind::kReg, 2)));
  EXPECT_TRUE(
      delta::DpiPartSelectAppliesTo(PackedFormal(DataTypeKind::kInteger, 0)));
  EXPECT_TRUE(
      delta::DpiPartSelectAppliesTo(PackedFormal(DataTypeKind::kTime, 0)));
  EXPECT_FALSE(
      delta::DpiPartSelectAppliesTo(PackedFormal(DataTypeKind::kBit, 1)));
  EXPECT_FALSE(
      delta::DpiPartSelectAppliesTo(PackedFormal(DataTypeKind::kLogic, 1)));
  EXPECT_FALSE(
      delta::DpiPartSelectAppliesTo(PackedFormal(DataTypeKind::kInt, 0)));
  EXPECT_FALSE(
      delta::DpiPartSelectAppliesTo(PackedFormal(DataTypeKind::kReal, 0)));
  EXPECT_FALSE(
      delta::DpiPartSelectAppliesTo(PackedFormal(DataTypeKind::kString, 0)));
  EXPECT_FALSE(
      delta::DpiPartSelectAppliesTo(PackedFormal(DataTypeKind::kChandle, 0)));
  EXPECT_FALSE(
      delta::DpiPartSelectAppliesTo(PackedFormal(DataTypeKind::kStruct, 0)));
}

TEST(DpiCanonicalUtilities, APartSelectReachesAtMostThirtyTwoBits) {
  EXPECT_EQ(delta::kDpiPartSelectMaxWidth, 32);
  EXPECT_TRUE(delta::DpiPartSelectIsDetermined(64, 0, 32));
  EXPECT_TRUE(delta::DpiPartSelectIsDetermined(64, 32, 32));
  EXPECT_TRUE(delta::DpiPartSelectIsDetermined(64, 0, 1));
  EXPECT_FALSE(delta::DpiPartSelectIsDetermined(64, 0, 33));
  EXPECT_FALSE(delta::DpiPartSelectIsDetermined(64, 0, 0));
  EXPECT_FALSE(delta::DpiPartSelectIsDetermined(64, 0, -1));
}

TEST(DpiCanonicalUtilities,
     APartSelectOutsideTheNormalizedRangeIsUndetermined) {
  EXPECT_TRUE(delta::DpiPartSelectIsDetermined(40, 8, 32));
  EXPECT_FALSE(delta::DpiPartSelectIsDetermined(40, 9, 32));
  EXPECT_TRUE(delta::DpiPartSelectIsDetermined(40, 39, 1));
  EXPECT_FALSE(delta::DpiPartSelectIsDetermined(40, 40, 1));
  EXPECT_FALSE(delta::DpiPartSelectIsDetermined(40, -1, 8));
  EXPECT_FALSE(delta::DpiPartSelectIsDetermined(18, 0, 32));
  EXPECT_TRUE(delta::DpiPartSelectIsDetermined(18, 0, 18));
}

TEST(DpiCanonicalUtilities, TheUtilitiesIndexTheNormalizedRange) {
  const delta::SvActualDimension kAscending{4, 7};
  EXPECT_EQ(delta::DpiNormalizedBitIndex(kAscending, 7), 0);
  EXPECT_EQ(delta::DpiNormalizedBitIndex(kAscending, 6), 1);
  EXPECT_EQ(delta::DpiNormalizedBitIndex(kAscending, 4), 3);
  const delta::SvActualDimension kDescending{17, 0};
  EXPECT_EQ(delta::DpiNormalizedBitIndex(kDescending, 0), 0);
  EXPECT_EQ(delta::DpiNormalizedBitIndex(kDescending, 17), 17);
  const delta::SvActualDimension kNegative{-1, -8};
  EXPECT_EQ(delta::DpiNormalizedBitIndex(kNegative, -8), 0);
  EXPECT_EQ(delta::DpiNormalizedBitIndex(kNegative, -1), 7);
  const svBitVecVal kA = 0x0Au;
  EXPECT_EQ(svGetBitselBit(&kA, delta::DpiNormalizedBitIndex(kAscending, 7)),
            0U);
  EXPECT_EQ(svGetBitselBit(&kA, delta::DpiNormalizedBitIndex(kAscending, 6)),
            1U);
  EXPECT_EQ(svGetBitselBit(&kA, delta::DpiNormalizedBitIndex(kAscending, 4)),
            1U);
}

TEST(SvDpi, PutBitSelectLogicReplacesWhateverTheBitHeld) {
  svLogicVecVal v = {0xAAAAAAAAU, 0xCCCCCCCCU};
  svPutBitselLogic(&v, 1, sv_0);
  svPutBitselLogic(&v, 2, sv_0);
  svPutBitselLogic(&v, 3, sv_0);
  EXPECT_EQ(v.aval, 0xAAAAAAA0U);
  EXPECT_EQ(v.bval, 0xCCCCCCC0U);
  svPutBitselLogic(&v, 4, sv_x);
  svPutBitselLogic(&v, 5, sv_x);
  svPutBitselLogic(&v, 6, sv_x);
  EXPECT_EQ(v.aval, 0xAAAAAAF0U);
  EXPECT_EQ(v.bval, 0xCCCCCCF0U);
  svPutBitselLogic(&v, 9, sv_z);
  svPutBitselLogic(&v, 11, sv_z);
  svPutBitselLogic(&v, 14, sv_1);
  svPutBitselLogic(&v, 15, sv_1);
  EXPECT_EQ(v.aval, 0xAAAAE0F0U);
  EXPECT_EQ(v.bval, 0xCCCC0EF0U);
}

TEST(SvDpi, TheSelectUtilitiesHaveTheirPrototypes) {
  EXPECT_TRUE((std::is_same_v<decltype(svGetBitselBit),
                              svBit(const svBitVecVal*, int)>));
  EXPECT_TRUE((std::is_same_v<decltype(svGetBitselLogic),
                              svLogic(const svLogicVecVal*, int)>));
  EXPECT_TRUE((std::is_same_v<decltype(svPutBitselBit),
                              void(svBitVecVal*, int, svBit)>));
  EXPECT_TRUE((std::is_same_v<decltype(svPutBitselLogic),
                              void(svLogicVecVal*, int, svLogic)>));
  EXPECT_TRUE(
      (std::is_same_v<decltype(svGetPartselBit),
                      void(svBitVecVal*, const svBitVecVal*, int, int)>));
  EXPECT_TRUE(
      (std::is_same_v<decltype(svGetPartselLogic),
                      void(svLogicVecVal*, const svLogicVecVal*, int, int)>));
  EXPECT_TRUE((std::is_same_v<decltype(svPutPartselBit),
                              void(svBitVecVal*, svBitVecVal, int, int)>));
  EXPECT_TRUE((std::is_same_v<decltype(svPutPartselLogic),
                              void(svLogicVecVal*, svLogicVecVal, int, int)>));
}

TEST(SvDpi, GetPartSelectLogicCarriesUnknownBits) {
  const svLogicVecVal kSrc = {0x00000530U, 0x00000630U};
  svLogicVecVal dst = {0x5A5A5AFFU, 0xA5A5A500U};
  svGetPartselLogic(&dst, &kSrc, 4, 8);
  EXPECT_EQ(dst.aval, 0x5A5A5A53U);
  EXPECT_EQ(dst.bval, 0xA5A5A563U);
}

TEST(SvDpi, GetPartSelectLogicCarriesUnknownBitsAcrossWords) {
  const svLogicVecVal kSrc[2] = {{0x50000000U, 0x60000000U}, {0x3U, 0x9U}};
  svLogicVecVal dst = {0x5A5A5AFFU, 0xA5A5A500U};
  svGetPartselLogic(&dst, kSrc, 28, 8);
  EXPECT_EQ(dst.aval, 0x5A5A5A35U);
  EXPECT_EQ(dst.bval, 0xA5A5A596U);
}

TEST(SvDpi, GetPartSelectLogicReplacesTheWholeWordAtFullWidth) {
  const svLogicVecVal kSrc[2] = {{0x12345678U, 0x9ABCDEF0U},
                                 {0x0000000FU, 0x00000003U}};
  svLogicVecVal dst = {0x00FF00FFU, 0xFF00FF00U};
  svGetPartselLogic(&dst, kSrc, 4, 32);
  EXPECT_EQ(dst.aval, 0xF1234567U);
  EXPECT_EQ(dst.bval, 0x39ABCDEFU);
  svGetPartselLogic(&dst, kSrc, 0, 32);
  EXPECT_EQ(dst.aval, 0x12345678U);
  EXPECT_EQ(dst.bval, 0x9ABCDEF0U);
}

TEST(SvDpi, GetPartSelectBitReplacesTheWholeWordAtFullWidthUnaligned) {
  const svBitVecVal kSrc[2] = {0x12345678U, 0x0000000FU};
  svBitVecVal dst = 0x00FF00FFU;
  svGetPartselBit(&dst, kSrc, 4, 32);
  EXPECT_EQ(dst, 0xF1234567U);
}

TEST(SvDpi, PutPartSelectTakesOnlyTheLowBitsOfItsSource) {
  svBitVecVal bits = 0;
  svPutPartselBit(&bits, 0xFFFFU, 4, 8);
  EXPECT_EQ(bits, 0xFF0U);
  svLogicVecVal logic = {0, 0};
  svPutPartselLogic(&logic, svLogicVecVal{0xFF0FU, 0xFFF0U}, 4, 8);
  EXPECT_EQ(logic.aval, 0x0F0U);
  EXPECT_EQ(logic.bval, 0xF00U);
}

TEST(SvDpi, PutPartSelectTakesOnlyTheLowBitsOfItsSourceAcrossWords) {
  svBitVecVal bits[2] = {0, 0};
  svPutPartselBit(bits, 0xFFFFU, 28, 8);
  EXPECT_EQ(bits[0], 0xF0000000U);
  EXPECT_EQ(bits[1], 0xFU);
  svLogicVecVal logic[2] = {{0, 0}, {0, 0}};
  svPutPartselLogic(logic, svLogicVecVal{0xFF5FU, 0xFFA3U}, 28, 8);
  EXPECT_EQ(logic[0].aval, 0xF0000000U);
  EXPECT_EQ(logic[0].bval, 0x30000000U);
  EXPECT_EQ(logic[1].aval, 0x5U);
  EXPECT_EQ(logic[1].bval, 0xAU);
}

TEST(SvDpi, PutPartSelectLogicCarriesUnknownBitsAndKeepsThoseAround) {
  svLogicVecVal dst = {0xAAAAAAAAU, 0xFFFFFFFFU};
  svPutPartselLogic(&dst, svLogicVecVal{0x0FU, 0x3CU}, 4, 8);
  EXPECT_EQ(dst.aval, 0xAAAAA0FAU);
  EXPECT_EQ(dst.bval, 0xFFFFF3CFU);
}

TEST(SvDpi, PutPartSelectAcrossWordsKeepsTheBitsOnBothSides) {
  svBitVecVal bits[2] = {0xFFFFFFFFU, 0xFFFFFFFFU};
  svPutPartselBit(bits, 0, 28, 8);
  EXPECT_EQ(bits[0], 0x0FFFFFFFU);
  EXPECT_EQ(bits[1], 0xFFFFFFF0U);
  svLogicVecVal logic[2] = {{0xFFFFFFFFU, 0xFFFFFFFFU},
                            {0xFFFFFFFFU, 0xFFFFFFFFU}};
  svPutPartselLogic(logic, svLogicVecVal{0, 0}, 28, 8);
  EXPECT_EQ(logic[0].aval, 0x0FFFFFFFU);
  EXPECT_EQ(logic[0].bval, 0x0FFFFFFFU);
  EXPECT_EQ(logic[1].aval, 0xFFFFFFF0U);
  EXPECT_EQ(logic[1].bval, 0xFFFFFFF0U);
}

TEST(SvDpi, PutPartSelectOfAWholeWordReplacesIt) {
  svLogicVecVal one = {0xFFFFFFFFU, 0x0F0F0F0FU};
  svPutPartselLogic(&one, svLogicVecVal{0x12345678U, 0x9ABCDEF0U}, 0, 32);
  EXPECT_EQ(one.aval, 0x12345678U);
  EXPECT_EQ(one.bval, 0x9ABCDEF0U);
  svLogicVecVal two[2] = {{0xFFFFFFFFU, 0}, {0, 0xFFFFFFFFU}};
  svPutPartselLogic(two, svLogicVecVal{0x12345678U, 0x9ABCDEF0U}, 16, 32);
  EXPECT_EQ(two[0].aval, 0x5678FFFFU);
  EXPECT_EQ(two[0].bval, 0xDEF00000U);
  EXPECT_EQ(two[1].aval, 0x00001234U);
  EXPECT_EQ(two[1].bval, 0xFFFF9ABCU);
  svBitVecVal bits[2] = {0xFFFFFFFFU, 0xFFFFFFFFU};
  svPutPartselBit(bits, 0x12345678U, 16, 32);
  EXPECT_EQ(bits[0], 0x5678FFFFU);
  EXPECT_EQ(bits[1], 0xFFFF1234U);
}

void SeeNothing() {}

bool PartSelectAppliesToFormal(const char* declarations, const char* formal,
                               const char* dir_name) {
  SimFixture f;
  RunModuleWithC(std::string(declarations) +
                     "  import \"DPI-C\" function void f(" + formal + ");\n" +
                     "  initial f(v);\n",
                 f, {{"f", CAddress(&SeeNothing)}}, dir_name);
  const DpiRtFunction* import = f.ctx.GetDpiRuntime()->FindImport("f");
  if (import == nullptr) return false;
  return DpiPartSelectAppliesTo(import->args[0]);
}

TEST(DpiCanonicalUtilities, DISABLED_AnUnpackedArrayHasNoPartSelect) {
  EXPECT_FALSE(PartSelectAppliesToFormal(
      "  bit [7:0] v [4];\n", "input bit [7:0] a [4]", "annex_h_11_05_sized"));
  EXPECT_FALSE(PartSelectAppliesToFormal("  logic [7:0] v [4];\n",
                                         "input logic [7:0] a []",
                                         "annex_h_11_05_open"));
}

TEST(DpiCanonicalUtilities, APackedFormalOfADesignHasPartSelects) {
  EXPECT_TRUE(PartSelectAppliesToFormal("  bit [7:0] v;\n", "input bit [7:0] a",
                                        "annex_h_11_05_packed"));
}

TEST(DpiCanonicalUtilities, APackedAggregateHasPartSelectsAnUnpackedOneNot) {
  EXPECT_TRUE(PartSelectAppliesToFormal(
      "  typedef struct packed { bit [3:0] a; logic [3:0] b; } ps;\n"
      "  ps v;\n",
      "input ps a", "annex_h_11_05_struct"));
  EXPECT_TRUE(PartSelectAppliesToFormal(
      "  typedef union packed { bit [3:0] a; bit [3:0] b; } pu;\n"
      "  pu v;\n",
      "input pu a", "annex_h_11_05_union"));
  EXPECT_FALSE(PartSelectAppliesToFormal(
      "  typedef struct { bit [3:0] a; logic [3:0] b; } us;\n"
      "  us v;\n",
      "input us a", "annex_h_11_05_unpacked"));
}

void SwapFieldsOfAPackedStruct(svLogicVecVal* v) {
  svLogicVecVal field = {0xFFFFFF00U, 0};
  svGetPartselLogic(&field, v, 4, 8);
  SeeInC({field.aval, field.bval});
  svPutPartselLogic(v, svLogicVecVal{0x3U, 0x2U}, 12, 2);
  svPutBitselLogic(v, 0, sv_z);
}

TEST(DpiCanonicalUtilities, TheUtilitiesWorkOnAPackedStructOfADesign) {
  SimFixture f;
  RunModuleWithC(
      "  typedef struct packed { logic [3:0] hi; logic [7:0] mid;\n"
      "                          logic [3:0] lo; } ps;\n"
      "  import \"DPI-C\" function void swap(inout ps v);\n"
      "  ps v;\n"
      "  bit ok;\n"
      "  initial begin\n"
      "    v = 16'b0000_1x0z_0110_1111;\n"
      "    swap(v);\n"
      "    ok = v === 16'b00x1_1x0z_0110_111z;\n"
      "  end\n",
      f, {{"swap", CAddress(&SwapFieldsOfAPackedStruct)}},
      "annex_h_11_05_swap");
  EXPECT_EQ(SeenInC(), (std::vector<long long>{0xFFFFFFC6, 0x50}));
  EXPECT_EQ(DesignValue(f, "ok"), 1U);
}

}  // namespace
