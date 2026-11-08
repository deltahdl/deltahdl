#include <gtest/gtest.h>

#include <bit>
#include <cstdint>
#include <vector>

#include "fixture_vpi_run.h"
#include "helpers_vpi_value_array.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

using VpiGetValueArraySim = VpiValueArraySimBase;

TEST_F(VpiGetValueArraySim, NonStaticArrayIsError) {
  VpiHandle arr = MakeArray("d", {{0, 1}}, 2, 32, {vpiDynamicArray});
  SetElem(0, 7);
  SetElem(1, 8);

  PLI_INT32 sentinel[2] = {0, 0};
  s_vpi_arrayvalue av = {};
  av.format = vpiIntVal;
  av.value.integers = sentinel;
  PLI_INT32 index[1] = {0};
  vpi_get_value_array(VpiHandleOf(arr), &av, index, 2);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
  EXPECT_EQ(av.value.integers, nullptr);
}

TEST_F(VpiGetValueArraySim, MultiDimensionReadFollowsFastestVaryingIndex) {
  VpiHandle arr = MakeArray("m", {{2, 1, 0}, {3, 4, 5}}, 9, 8);
  for (int i = 0; i < 9; ++i) SetElem(i, static_cast<uint64_t>(i));

  s_vpi_arrayvalue av = {};
  av.format = vpiIntVal;
  PLI_INT32 index[2] = {1, 4};
  vpi_get_value_array(VpiHandleOf(arr), &av, index, 5);

  ASSERT_NE(av.value.integers, nullptr);
  EXPECT_EQ(av.value.integers[0], 4);
  EXPECT_EQ(av.value.integers[1], 5);
  EXPECT_EQ(av.value.integers[2], 6);
  EXPECT_EQ(av.value.integers[3], 7);
  EXPECT_EQ(av.value.integers[4], 8);
}

TEST_F(VpiGetValueArraySim, RawFourStateValEncodesAvalAndBval) {
  VpiHandle arr = MakeArray("r", {{0, 1}}, 2, 8);
  SetElem(0, 0xA5, 0x0F);
  SetElem(1, 0x3C, 0x00);

  s_vpi_arrayvalue av = {};
  av.format = vpiRawFourStateVal;
  PLI_INT32 index[1] = {0};
  vpi_get_value_array(VpiHandleOf(arr), &av, index, 2);

  ASSERT_NE(av.value.rawvals, nullptr);
  const auto* raw = reinterpret_cast<const unsigned char*>(av.value.rawvals);
  EXPECT_EQ(raw[0], 0xA5u);
  EXPECT_EQ(raw[1], 0x0Fu);
  EXPECT_EQ(raw[2], 0x3Cu);
  EXPECT_EQ(raw[3], 0x00u);
}

TEST_F(VpiGetValueArraySim, RawFourStateValZeroesBvalForTwoStateArray) {
  VpiHandle arr = MakeArray("t", {{0}}, 1, 8, {vpiStaticArray, false});
  SetElem(0, 0xF0, 0xFF);

  s_vpi_arrayvalue av = {};
  av.format = vpiRawFourStateVal;
  PLI_INT32 index[1] = {0};
  vpi_get_value_array(VpiHandleOf(arr), &av, index, 1);

  ASSERT_NE(av.value.rawvals, nullptr);
  const auto* raw = reinterpret_cast<const unsigned char*>(av.value.rawvals);
  EXPECT_EQ(raw[0], 0xF0u);
  EXPECT_EQ(raw[1], 0x00u);
}

TEST_F(VpiGetValueArraySim, RawTwoStateValOmitsBvalGroup) {
  VpiHandle arr = MakeArray("w", {{0, 1}}, 2, 8);
  SetElem(0, 0x55, 0xFF);
  SetElem(1, 0xAA, 0xFF);

  s_vpi_arrayvalue av = {};
  av.format = vpiRawTwoStateVal;
  PLI_INT32 index[1] = {0};
  vpi_get_value_array(VpiHandleOf(arr), &av, index, 2);

  ASSERT_NE(av.value.rawvals, nullptr);
  const auto* raw = reinterpret_cast<const unsigned char*>(av.value.rawvals);
  EXPECT_EQ(raw[0], 0x55u);
  EXPECT_EQ(raw[1], 0xAAu);
}

TEST_F(VpiGetValueArraySim, RawFourStateValStoresBytesLeastSignificantFirst) {
  VpiHandle arr = MakeArray("b", {{0}}, 1, 16);
  SetElem(0, 0x1234, 0x0000);

  s_vpi_arrayvalue av = {};
  av.format = vpiRawFourStateVal;
  PLI_INT32 index[1] = {0};
  vpi_get_value_array(VpiHandleOf(arr), &av, index, 1);

  ASSERT_NE(av.value.rawvals, nullptr);
  const auto* raw = reinterpret_cast<const unsigned char*>(av.value.rawvals);
  EXPECT_EQ(raw[0], 0x34u);
  EXPECT_EQ(raw[1], 0x12u);
  EXPECT_EQ(raw[2], 0x00u);
  EXPECT_EQ(raw[3], 0x00u);
}

TEST_F(VpiGetValueArraySim, UnsupportedFormatIsErrorAndNullsValuePointer) {
  VpiHandle arr = MakeArray("u", {{0, 1}}, 2, 32);
  SetElem(0, 1);
  SetElem(1, 2);

  PLI_BYTE8 sentinel[8] = {};
  s_vpi_arrayvalue av = {};
  av.format = vpiBinStrVal;
  av.value.rawvals = sentinel;
  PLI_INT32 index[1] = {0};
  vpi_get_value_array(VpiHandleOf(arr), &av, index, 2);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
  EXPECT_EQ(av.value.rawvals, nullptr);
}

TEST_F(VpiGetValueArraySim, UserAllocFlagFillsCallerBuffer) {
  VpiHandle arr = MakeArray("ua", {{0, 1}}, 2, 32);
  SetElem(0, 41);
  SetElem(1, 42);

  PLI_INT32 buffer[2] = {0, 0};
  s_vpi_arrayvalue av = {};
  av.format = vpiIntVal;
  av.flags = vpiUserAllocFlag;
  av.value.integers = buffer;
  PLI_INT32 index[1] = {0};
  vpi_get_value_array(VpiHandleOf(arr), &av, index, 2);

  EXPECT_EQ(av.value.integers, buffer);
  EXPECT_EQ(buffer[0], 41);
  EXPECT_EQ(buffer[1], 42);
}

TEST_F(VpiGetValueArraySim, VectorValReturnsAvalAndBvalGroups) {
  VpiHandle arr = MakeArray("vv", {{0}}, 1, 16);
  SetElem(0, 0xABCD, 0x00F0);

  s_vpi_arrayvalue av = {};
  av.format = vpiVectorVal;
  PLI_INT32 index[1] = {0};
  vpi_get_value_array(VpiHandleOf(arr), &av, index, 1);

  ASSERT_NE(av.value.vectors, nullptr);
  EXPECT_EQ(av.value.vectors[0].aval, 0xABCDu);
  EXPECT_EQ(av.value.vectors[0].bval, 0x00F0u);
}

TEST_F(VpiGetValueArraySim, LongIntValReturnsSixtyFourBitElements) {
  VpiHandle arr = MakeArray("li", {{0}}, 1, 64);
  arr->children[0]->type = vpiLongIntVar;
  SetElem(0, 0x1122334455667788ull);

  s_vpi_arrayvalue av = {};
  av.format = vpiLongIntVal;
  PLI_INT32 index[1] = {0};
  vpi_get_value_array(VpiHandleOf(arr), &av, index, 1);

  ASSERT_NE(av.value.longints, nullptr);
  EXPECT_EQ(av.value.longints[0], 0x1122334455667788ll);
}

TEST_F(VpiGetValueArraySim, ShortIntValReturnsShortsPerElement) {
  VpiHandle arr = MakeArray("si", {{0, 1}}, 2, 16);
  for (auto* elem : arr->children) elem->type = vpiShortIntVar;
  SetElem(0, 0x0102);
  SetElem(1, 0x0304);

  s_vpi_arrayvalue av = {};
  av.format = vpiShortIntVal;
  PLI_INT32 index[1] = {0};
  vpi_get_value_array(VpiHandleOf(arr), &av, index, 2);

  ASSERT_NE(av.value.shortints, nullptr);
  EXPECT_EQ(av.value.shortints[0], 0x0102);
  EXPECT_EQ(av.value.shortints[1], 0x0304);
}

TEST_F(VpiGetValueArraySim, ShortRealValReturnsFloatsPerElement) {
  VpiHandle arr = MakeArray("sr", {{0, 1}}, 2, 32);
  for (auto* elem : arr->children) elem->type = vpiShortRealVar;
  SetElem(0, std::bit_cast<uint32_t>(42.0f));
  SetElem(1, std::bit_cast<uint32_t>(7.0f));

  s_vpi_arrayvalue av = {};
  av.format = vpiShortRealVal;
  PLI_INT32 index[1] = {0};
  vpi_get_value_array(VpiHandleOf(arr), &av, index, 2);

  ASSERT_NE(av.value.shortreals, nullptr);
  EXPECT_FLOAT_EQ(av.value.shortreals[0], 42.0f);
  EXPECT_FLOAT_EQ(av.value.shortreals[1], 7.0f);
}

TEST_F(VpiGetValueArraySim, RealValReturnsDoublesPerElement) {
  VpiHandle arr = MakeArray("re", {{0, 1}}, 2, 64);
  SetElem(0, 123);
  SetElem(1, 9);

  s_vpi_arrayvalue av = {};
  av.format = vpiRealVal;
  PLI_INT32 index[1] = {0};
  vpi_get_value_array(VpiHandleOf(arr), &av, index, 2);

  ASSERT_NE(av.value.reals, nullptr);
  EXPECT_DOUBLE_EQ(av.value.reals[0], 123.0);
  EXPECT_DOUBLE_EQ(av.value.reals[1], 9.0);
}

TEST_F(VpiGetValueArraySim, MissingStartingIndexIsError) {
  VpiHandle arr = MakeArray("ni", {{0, 1}}, 2, 32);
  SetElem(0, 3);
  SetElem(1, 4);

  PLI_INT32 sentinel[2] = {0, 0};
  s_vpi_arrayvalue av = {};
  av.format = vpiIntVal;
  av.value.integers = sentinel;
  vpi_get_value_array(VpiHandleOf(arr), &av, nullptr, 2);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
  EXPECT_EQ(av.value.integers, nullptr);
}

TEST_F(VpiGetValueArraySim, OutOfRangeStartingIndexIsError) {
  VpiHandle arr = MakeArray("oor", {{0, 1}}, 2, 32);
  SetElem(0, 3);
  SetElem(1, 4);

  PLI_INT32 sentinel[2] = {0, 0};
  s_vpi_arrayvalue av = {};
  av.format = vpiIntVal;
  av.value.integers = sentinel;
  PLI_INT32 index[1] = {5};
  vpi_get_value_array(VpiHandleOf(arr), &av, index, 2);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
  EXPECT_EQ(av.value.integers, nullptr);
}

TEST_F(VpiGetValueArraySim, TimeValReturnsTimeWordsPerElement) {
  VpiHandle arr = MakeArray("tm", {{0}}, 1, 64);
  SetElem(0, (uint64_t{2} << 32) | 5u);

  s_vpi_arrayvalue av = {};
  av.format = vpiTimeVal;
  PLI_INT32 index[1] = {0};
  vpi_get_value_array(VpiHandleOf(arr), &av, index, 1);

  ASSERT_NE(av.value.times, nullptr);
  EXPECT_EQ(av.value.times[0].high, 2u);
  EXPECT_EQ(av.value.times[0].low, 5u);
}

TEST_F(VpiGetValueArraySim, AFormatTheElementTypeDoesNotSupportIsAnError) {
  for (int format : {vpiShortIntVal, vpiLongIntVal, vpiShortRealVal}) {
    VpiHandle arr = MakeArray("w", {{0, 1}}, 2, 32);
    SetElem(0, 1);
    SetElem(1, 2);

    PLI_INT32 sentinel[2] = {0, 0};
    s_vpi_arrayvalue av = {};
    av.format = static_cast<PLI_UINT32>(format);
    av.value.integers = sentinel;
    PLI_INT32 index[1] = {0};
    vpi_get_value_array(VpiHandleOf(arr), &av, index, 2);

    s_vpi_error_info info = {};
    EXPECT_EQ(vpi_chk_error(&info), vpiError) << "format " << format;
    EXPECT_EQ(av.value.integers, nullptr) << "format " << format;
  }
}

TEST_F(VpiGetValueArraySim, TheRawAndVectorFormatsSuitEveryElementType) {
  for (int format : {vpiRawFourStateVal, vpiRawTwoStateVal, vpiVectorVal}) {
    VpiHandle arr = MakeArray("a", {{0}}, 1, 8);
    arr->children[0]->type = vpiShortRealVar;
    SetElem(0, 0x5A);

    s_vpi_arrayvalue av = {};
    av.format = static_cast<PLI_UINT32>(format);
    PLI_INT32 index[1] = {0};
    vpi_get_value_array(VpiHandleOf(arr), &av, index, 1);

    s_vpi_error_info info = {};
    EXPECT_EQ(vpi_chk_error(&info), 0) << "format " << format;
    if (format == vpiVectorVal) {
      EXPECT_NE(av.value.vectors, nullptr) << "format " << format;
    } else {
      EXPECT_NE(av.value.rawvals, nullptr) << "format " << format;
    }
  }
}

TEST_F(VpiGetValueArraySim, ANullHandleOrValueReadsNothing) {
  VpiHandle arr = MakeArray("nh", {{0}}, 1, 32);
  SetElem(0, 3);
  PLI_INT32 sentinel[1] = {0};
  s_vpi_arrayvalue av = {};
  av.format = vpiIntVal;
  av.value.integers = sentinel;
  PLI_INT32 index[1] = {0};
  vpi_get_value_array(nullptr, &av, index, 1);
  vpi_get_value_array(VpiHandleOf(arr), nullptr, index, 1);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), 0);
  EXPECT_EQ(av.value.integers, sentinel);
  EXPECT_EQ(sentinel[0], 0);
}

TEST_F(VpiGetValueArraySim, AHandleToNoArrayIsError) {
  VpiHandle arr = MakeArray("na", {{0}}, 1, 32);
  arr->type = vpiReg;
  PLI_INT32 sentinel[1] = {0};
  s_vpi_arrayvalue av = {};
  av.format = vpiIntVal;
  av.value.integers = sentinel;
  PLI_INT32 index[1] = {0};
  vpi_get_value_array(VpiHandleOf(arr), &av, index, 1);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
  EXPECT_EQ(av.value.integers, nullptr);
}

TEST_F(VpiGetValueArraySim, AnArrayWithNoDimensionToIndexIsError) {
  VpiHandle arr = MakeArray("ud", {}, 1, 32);
  PLI_INT32 sentinel[1] = {0};
  s_vpi_arrayvalue av = {};
  av.format = vpiIntVal;
  av.value.integers = sentinel;
  PLI_INT32 index[1] = {0};
  vpi_get_value_array(VpiHandleOf(arr), &av, index, 1);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
  EXPECT_EQ(av.value.integers, nullptr);
}

TEST_F(VpiGetValueArraySim, PositionsWithNothingToReadReadZero) {
  Variable* stored = sim_ctx_.CreateVariable("ps1", 32);
  stored->value.words[0].aval = 9;
  stored->value.words[0].bval = 0;
  VpiHandle arr = vpi_ctx_.CreateRegArray("ps", vpiStaticArray, {{0, 1, 2}},
                                          {nullptr, stored});
  PLI_INT32 buf[3] = {-1, -1, -1};
  s_vpi_arrayvalue av = {};
  av.format = vpiIntVal;
  av.flags = vpiUserAllocFlag;
  av.value.integers = buf;
  PLI_INT32 index[1] = {0};
  vpi_get_value_array(VpiHandleOf(arr), &av, index, 3);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), 0);
  EXPECT_EQ(buf[0], 0);
  EXPECT_EQ(buf[1], 9);
  EXPECT_EQ(buf[2], 0);
}

TEST_F(VpiGetValueArraySim, ASectionHoldingNoStorageReadsZero) {
  VpiHandle arr =
      vpi_ctx_.CreateRegArray("nn", vpiStaticArray, {{0, 1}}, {nullptr});
  PLI_INT32 buf[2] = {-1, -1};
  s_vpi_arrayvalue av = {};
  av.format = vpiIntVal;
  av.flags = vpiUserAllocFlag;
  av.value.integers = buf;
  PLI_INT32 index[1] = {0};
  vpi_get_value_array(VpiHandleOf(arr), &av, index, 2);

  EXPECT_EQ(buf[0], 0);
  EXPECT_EQ(buf[1], 0);
}

TEST_F(VpiGetValueArraySim, VectorValOfATwoStateArrayReportsKnownBits) {
  VpiHandle arr = MakeArray("v2", {{0}}, 1, 16, {vpiStaticArray, false});
  SetElem(0, 0x1234, 0x00FF);
  s_vpi_arrayvalue av = {};
  av.format = vpiVectorVal;
  PLI_INT32 index[1] = {0};
  vpi_get_value_array(VpiHandleOf(arr), &av, index, 1);

  ASSERT_NE(av.value.vectors, nullptr);
  EXPECT_EQ(av.value.vectors[0].aval, 0x1234u);
  EXPECT_EQ(av.value.vectors[0].bval, 0u);
}

TEST_F(VpiGetValueArraySim, TheShortAndLongFormatsSuitByteAndShortIntElements) {
  const int kPairs[3][2] = {{vpiShortIntVal, vpiByteVar},
                            {vpiLongIntVal, vpiShortIntVar},
                            {vpiLongIntVal, vpiByteVar}};
  for (const auto& pair : kPairs) {
    VpiHandle arr = MakeArray("p", {{0}}, 1, 8);
    arr->children[0]->type = pair[1];
    SetElem(0, 5);
    s_vpi_arrayvalue av = {};
    av.format = static_cast<PLI_UINT32>(pair[0]);
    PLI_INT32 index[1] = {0};
    vpi_get_value_array(VpiHandleOf(arr), &av, index, 1);

    s_vpi_error_info info = {};
    EXPECT_EQ(vpi_chk_error(&info), 0) << "format " << pair[0];
    EXPECT_NE(av.value.rawvals, nullptr) << "format " << pair[0];
  }
}

TEST_F(VpiGetValueArraySim, RawFormatsCarryAnElementWiderThan64Bits) {
  VpiHandle arr = MakeArray("w", {{0}}, 1, 72);
  SetElem(0, 0x0807060504030201u);
  elems_[0]->value.words[1].aval = 0x09;
  elems_[0]->value.words[1].bval = 0x80;
  PLI_INT32 index[1] = {0};

  s_vpi_arrayvalue four = {};
  four.format = vpiRawFourStateVal;
  vpi_get_value_array(VpiHandleOf(arr), &four, index, 1);
  ASSERT_NE(four.value.rawvals, nullptr);
  EXPECT_EQ(four.value.rawvals[0], 0x01);
  EXPECT_EQ(four.value.rawvals[8], 0x09);
  EXPECT_EQ(four.value.rawvals[9], 0x00);
  EXPECT_EQ(four.value.rawvals[17], static_cast<PLI_BYTE8>(0x80));

  s_vpi_arrayvalue two = {};
  two.format = vpiRawTwoStateVal;
  vpi_get_value_array(VpiHandleOf(arr), &two, index, 1);
  ASSERT_NE(two.value.rawvals, nullptr);
  EXPECT_EQ(two.value.rawvals[8], 0x09);
}

TEST_F(VpiGetValueArraySim, VectorValCarriesAnElementWiderThan32Bits) {
  VpiHandle arr = MakeArray("v40", {{0, 1}}, 2, 40);
  SetElem(0, 0xAB11111111u, 0x0100000000u);
  SetElem(1, 0xCD22222222u);
  s_vpi_arrayvalue av = {};
  av.format = vpiVectorVal;
  PLI_INT32 index[1] = {0};
  vpi_get_value_array(VpiHandleOf(arr), &av, index, 2);

  ASSERT_NE(av.value.vectors, nullptr);
  EXPECT_EQ(av.value.vectors[0].aval, 0x11111111u);
  EXPECT_EQ(av.value.vectors[1].aval, 0xABu);
  EXPECT_EQ(av.value.vectors[1].bval, 0x01u);
  EXPECT_EQ(av.value.vectors[2].aval, 0x22222222u);
  EXPECT_EQ(av.value.vectors[3].aval, 0xCDu);
}

TEST_F(VpiGetValueArraySim, ANetArrayIsReadElementByElement) {
  VpiHandle arr = MakeArray("na", {{0, 1}}, 2, 32);
  arr->type = vpiNetArray;
  SetElem(0, 21);
  SetElem(1, 22);
  s_vpi_arrayvalue av = {};
  av.format = vpiIntVal;
  PLI_INT32 index[1] = {0};
  vpi_get_value_array(VpiHandleOf(arr), &av, index, 2);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), 0);
  ASSERT_NE(av.value.integers, nullptr);
  EXPECT_EQ(av.value.integers[0], 21);
  EXPECT_EQ(av.value.integers[1], 22);
}

std::vector<PLI_INT32>& ArrayRead() {
  static std::vector<PLI_INT32> read;
  return read;
}

PLI_INT32 ReadThenWriteArray(PLI_BYTE8*) {
  vpiHandle arr = vpi_handle_by_name(VpiText("top.arr"), nullptr);
  PLI_INT32 buf[4] = {0, 0, 0, 0};
  PLI_INT32 index = 0;
  s_vpi_arrayvalue av = {};
  av.format = vpiIntVal;
  av.flags = vpiUserAllocFlag;
  av.value.integers = buf;
  vpi_get_value_array(arr, &av, &index, 4);
  ArrayRead().assign(buf, buf + 4);
  for (int i = 0; i < 4; ++i) buf[i] = 50 + i;
  av.flags = 0;
  vpi_put_value_array(arr, &av, &index, 4);
  return 0;
}

class ValueArraysOfARun : public VpiDesignRun {};

TEST_F(ValueArraysOfARun, ARunsArrayIsReadAndWrittenWhole) {
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$array_io");
  data.calltf = &ReadThenWriteArray;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
  Run("module top; int arr[4] = '{1, 2, 3, 4}; int seen;\n"
      "  initial begin #1 $array_io; seen = arr[2]; end\n"
      "endmodule\n");
  EXPECT_EQ(ArrayRead(), (std::vector<PLI_INT32>{1, 2, 3, 4}));
  s_vpi_value value = {};
  value.format = vpiIntVal;
  vpi_get_value(By("top.seen"), &value);
  EXPECT_EQ(value.value.integer, 52);
}

std::vector<PLI_INT32>& MatrixRead() {
  static std::vector<PLI_INT32> read;
  return read;
}

PLI_INT32 ReadMatrix(PLI_BYTE8*) {
  vpiHandle m = vpi_handle_by_name(VpiText("top.m"), nullptr);
  PLI_INT32 buf[4] = {0, 0, 0, 0};
  PLI_INT32 index[2] = {0, 1};
  s_vpi_arrayvalue av = {};
  av.format = vpiIntVal;
  av.flags = vpiUserAllocFlag;
  av.value.integers = buf;
  vpi_get_value_array(m, &av, index, 4);
  MatrixRead().assign(buf, buf + 4);
  return 0;
}

TEST_F(ValueArraysOfARun, ARunsTwoDimensionalArrayIsReadAcrossItsSubarrays) {
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$matrix_read");
  data.calltf = &ReadMatrix;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
  Run("module top; typedef logic [7:0] b_t;\n"
      "  b_t m [0:1][0:2] = '{'{1, 2, 3}, '{4, 5, 6}};\n"
      "  initial #1 $matrix_read;\n"
      "endmodule\n");
  EXPECT_EQ(MatrixRead(), (std::vector<PLI_INT32>{2, 3, 4, 5}));
}

bool& StringArrayRefused() {
  static bool refused = false;
  return refused;
}

PLI_INT32 ReadStringArray(PLI_BYTE8*) {
  vpiHandle s = vpi_handle_by_name(VpiText("top.s"), nullptr);
  PLI_INT32 sentinel[2] = {0, 0};
  PLI_INT32 index = 0;
  s_vpi_arrayvalue av = {};
  av.format = vpiIntVal;
  av.value.integers = sentinel;
  vpi_get_value_array(s, &av, &index, 2);
  s_vpi_error_info info = {};
  StringArrayRefused() =
      vpi_chk_error(&info) == vpiError && av.value.integers == nullptr;
  return 0;
}

TEST_F(ValueArraysOfARun, ARunsArrayOfStringsIsRefused) {
  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$string_array_read");
  data.calltf = &ReadStringArray;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
  Run("module top; string s [2] = '{\"a\", \"bc\"};\n"
      "  initial #1 $string_array_read;\n"
      "endmodule\n");
  EXPECT_TRUE(StringArrayRefused());
}

using ArrayValueArms = decltype(s_vpi_arrayvalue::value);

class ElementValuesOfARun : public VpiDesignRun {
 protected:
  template <typename T>
  static std::vector<T> ReadTwo(const char* name, int format,
                                T* ArrayValueArms::* arm) {
    T buf[2] = {};
    PLI_INT32 index = 0;
    s_vpi_arrayvalue av = {};
    av.format = format;
    av.flags = vpiUserAllocFlag;
    av.value.*arm = buf;
    vpi_get_value_array(By(name), &av, &index, 2);
    return {buf[0], buf[1]};
  }
};

TEST_F(ElementValuesOfARun, ARealElementIsReadAsItsValue) {
  Run("module top;\n"
      "  real r[2];\n"
      "  shortreal s[2];\n"
      "  initial begin\n"
      "    r[0] = 1.0; r[1] = 2.5; s[0] = 1.0; s[1] = 2.5; $noop;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(ReadTwo("top.r", vpiRealVal, &ArrayValueArms::reals),
            (std::vector<double>{1.0, 2.5}));
  EXPECT_EQ(ReadTwo("top.s", vpiShortRealVal, &ArrayValueArms::shortreals),
            (std::vector<float>{1.0f, 2.5f}));
}

TEST_F(ElementValuesOfARun, ASignedElementKeepsItsSign) {
  Run("module top;\n"
      "  byte b[2] = '{-1, -2};\n"
      "  shortint h[2] = '{-1, -2};\n"
      "  initial $noop;\n"
      "endmodule\n");
  EXPECT_EQ(ReadTwo("top.b", vpiShortIntVal, &ArrayValueArms::shortints),
            (std::vector<PLI_INT16>{-1, -2}));
  EXPECT_EQ(ReadTwo("top.b", vpiIntVal, &ArrayValueArms::integers),
            (std::vector<PLI_INT32>{-1, -2}));
  EXPECT_EQ(ReadTwo("top.b", vpiLongIntVal, &ArrayValueArms::longints),
            (std::vector<PLI_INT64>{-1, -2}));
  EXPECT_EQ(ReadTwo("top.h", vpiLongIntVal, &ArrayValueArms::longints),
            (std::vector<PLI_INT64>{-1, -2}));
}

TEST_F(ElementValuesOfARun, AnUnknownBitOfAnElementReadsAsZero) {
  Run("module top;\n"
      "  logic [3:0] a[2] = '{4'b10x1, 4'bxxxx};\n"
      "  initial $noop;\n"
      "endmodule\n");
  EXPECT_EQ(ReadTwo("top.a", vpiIntVal, &ArrayValueArms::integers),
            (std::vector<PLI_INT32>{9, 0}));
}

TEST_F(VpiGetValueArraySim, ASignedElementHoldingAnUnsignedValueReadsSigned) {
  VpiHandle arr = MakeArray("b", {{0, 1}}, 2, 8);
  for (Variable* elem : elems_) elem->is_signed = true;
  SetElem(0, 0xF0);
  SetElem(1, 0x01);

  s_vpi_arrayvalue av = {};
  av.format = vpiIntVal;
  PLI_INT32 first[1] = {0};
  vpi_get_value_array(VpiHandleOf(arr), &av, first, 2);

  ASSERT_NE(av.value.integers, nullptr);
  EXPECT_EQ(av.value.integers[0], -16);
  EXPECT_EQ(av.value.integers[1], 1);
}

}  // namespace
}  // namespace delta
