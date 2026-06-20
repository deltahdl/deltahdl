#include <gtest/gtest.h>

#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

class VpiGetValueArraySim : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  // Build a static unpacked array with `count` freshly created element
  // variables and retain the variable pointers so a test can install known
  // element values that vpi_get_value_array() then reads back.
  VpiHandle MakeArray(std::string_view name,
                      const std::vector<std::vector<int>>& dims, int count,
                      uint32_t elem_width, int array_type = vpiStaticArray,
                      bool four_state = true) {
    elems_.clear();
    name_pool_.reserve(name_pool_.size() + count);
    for (int i = 0; i < count; ++i) {
      auto* v = sim_ctx_.CreateVariable(
          name_pool_.emplace_back(std::string(name) + std::to_string(i)),
          elem_width);
      v->is_4state = four_state;
      elems_.push_back(v);
    }
    return vpi_ctx_.CreateRegArray(name, array_type, dims, elems_);
  }

  // Install a known (aval, bval) into one element's first value word.
  void SetElem(int i, uint64_t aval, uint64_t bval = 0) {
    elems_[i]->value.words[0].aval = aval;
    elems_[i]->value.words[0].bval = bval;
  }

  SourceManager mgr_;
  Arena arena_;
  Scheduler scheduler_{arena_};
  DiagEngine diag_{mgr_};
  SimContext sim_ctx_{scheduler_, arena_, diag_};
  VpiContext vpi_ctx_;
  std::vector<Variable*> elems_;
  std::vector<std::string> name_pool_;
};

// §38.16: the routine retrieves values only from static unpacked arrays
// (vpiArrayType vpiStaticArray). A non-static array is rejected, an error is
// recorded, and the value arm is set to NULL.
TEST_F(VpiGetValueArraySim, NonStaticArrayIsError) {
  VpiHandle arr = MakeArray("d", {{0, 1}}, 2, 32, vpiDynamicArray);
  SetElem(0, 7);
  SetElem(1, 8);

  PLI_INT32 sentinel[2] = {0, 0};
  s_vpi_arrayvalue av = {};
  av.format = vpiIntVal;
  av.value.integers = sentinel;  // non-NULL going in
  PLI_INT32 index[1] = {0};
  vpi_get_value_array(arr, &av, index, 2);

  SVpiErrorInfo info = {};
  EXPECT_EQ(VpiChkErrorC(&info), vpiError);
  EXPECT_EQ(av.value.integers, nullptr);  // value arm overwritten to NULL
}

// §38.16: index_p carries one starting index per unpacked dimension, and the
// elements are read with the rightmost dimension varying fastest. For
// a[2:0][3:5] started at a[1][4] the order is a[1][4], a[1][5], a[0][3],
// a[0][4], a[0][5] - the example the standard gives. Flat ordinals 4..8. The
// value arm is left NULL on entry, so this also exercises the default case
// where VPI allocates the storage and points the arm at the filled values.
TEST_F(VpiGetValueArraySim, MultiDimensionReadFollowsFastestVaryingIndex) {
  VpiHandle arr = MakeArray("m", {{2, 1, 0}, {3, 4, 5}}, 9, 8);
  for (int i = 0; i < 9; ++i) SetElem(i, static_cast<uint64_t>(i));

  s_vpi_arrayvalue av = {};
  av.format = vpiIntVal;  // value arm starts NULL (no application buffer)
  PLI_INT32 index[2] = {1, 4};
  vpi_get_value_array(arr, &av, index, 5);

  ASSERT_NE(av.value.integers, nullptr);  // VPI allocated the storage
  EXPECT_EQ(av.value.integers[0], 4);     // a[1][4]
  EXPECT_EQ(av.value.integers[1], 5);     // a[1][5]
  EXPECT_EQ(av.value.integers[2], 6);     // a[0][3]
  EXPECT_EQ(av.value.integers[3], 7);     // a[0][4]
  EXPECT_EQ(av.value.integers[4], 8);     // a[0][5]
}

// §38.16: in vpiRawFourStateVal format each element occupies ngroups*2 bytes -
// an aval byte group followed by a bval byte group - stored least-significant
// byte first.
TEST_F(VpiGetValueArraySim, RawFourStateValEncodesAvalAndBval) {
  VpiHandle arr = MakeArray("r", {{0, 1}}, 2, 8);  // ngroups = 1
  SetElem(0, 0xA5, 0x0F);
  SetElem(1, 0x3C, 0x00);

  s_vpi_arrayvalue av = {};
  av.format = vpiRawFourStateVal;
  PLI_INT32 index[1] = {0};
  vpi_get_value_array(arr, &av, index, 2);

  ASSERT_NE(av.value.rawvals, nullptr);
  const auto* raw = reinterpret_cast<const unsigned char*>(av.value.rawvals);
  EXPECT_EQ(raw[0], 0xA5u);  // element 0 aval group
  EXPECT_EQ(raw[1], 0x0Fu);  // element 0 bval group
  EXPECT_EQ(raw[2], 0x3Cu);  // element 1 aval group
  EXPECT_EQ(raw[3], 0x00u);  // element 1 bval group
}

// §38.16: the 4-state raw format may also be requested of a 2-state array. A
// 2-state element has no unknown/high-impedance bits, so the bval group comes
// back all zero even if such bits happen to sit in the element's storage.
TEST_F(VpiGetValueArraySim, RawFourStateValZeroesBvalForTwoStateArray) {
  VpiHandle arr =
      MakeArray("t", {{0}}, 1, 8, vpiStaticArray, /*four_state=*/false);
  SetElem(0, 0xF0, 0xFF);  // a stray bval in storage

  s_vpi_arrayvalue av = {};
  av.format = vpiRawFourStateVal;
  PLI_INT32 index[1] = {0};
  vpi_get_value_array(arr, &av, index, 1);

  ASSERT_NE(av.value.rawvals, nullptr);
  const auto* raw = reinterpret_cast<const unsigned char*>(av.value.rawvals);
  EXPECT_EQ(raw[0], 0xF0u);  // aval group
  EXPECT_EQ(raw[1], 0x00u);  // bval group zeroed for the 2-state element
}

// §38.16: in vpiRawTwoStateVal format the bval group is omitted, so each
// element occupies just ngroups bytes (only the aval bits are returned).
TEST_F(VpiGetValueArraySim, RawTwoStateValOmitsBvalGroup) {
  VpiHandle arr = MakeArray("w", {{0, 1}}, 2, 8);  // ngroups = 1
  SetElem(0, 0x55, 0xFF);  // bval present in the element...
  SetElem(1, 0xAA, 0xFF);

  s_vpi_arrayvalue av = {};
  av.format = vpiRawTwoStateVal;
  PLI_INT32 index[1] = {0};
  vpi_get_value_array(arr, &av, index, 2);

  ASSERT_NE(av.value.rawvals, nullptr);
  const auto* raw = reinterpret_cast<const unsigned char*>(av.value.rawvals);
  // ...but the two-state format carries only one (aval) byte per element.
  EXPECT_EQ(raw[0], 0x55u);
  EXPECT_EQ(raw[1], 0xAAu);
}

// §38.16: the vpiRawFourStateVal raw groups span ngroups = (elemBits + 7)/8
// bytes, loaded least-significant byte first. A 16-bit element spans two bytes
// per group, so the high byte must land in the second byte.
TEST_F(VpiGetValueArraySim, RawFourStateValStoresBytesLeastSignificantFirst) {
  VpiHandle arr = MakeArray("b", {{0}}, 1, 16);  // ngroups = 2
  SetElem(0, 0x1234, 0x0000);

  s_vpi_arrayvalue av = {};
  av.format = vpiRawFourStateVal;
  PLI_INT32 index[1] = {0};
  vpi_get_value_array(arr, &av, index, 1);

  ASSERT_NE(av.value.rawvals, nullptr);
  const auto* raw = reinterpret_cast<const unsigned char*>(av.value.rawvals);
  EXPECT_EQ(raw[0], 0x34u);  // aval low byte
  EXPECT_EQ(raw[1], 0x12u);  // aval high byte
  EXPECT_EQ(raw[2], 0x00u);  // bval low byte
  EXPECT_EQ(raw[3], 0x00u);  // bval high byte
}

// §38.16: a format outside the supported set is an error if requested, and the
// value arm is overwritten to NULL to signal the VPI error.
TEST_F(VpiGetValueArraySim, UnsupportedFormatIsErrorAndNullsValuePointer) {
  VpiHandle arr = MakeArray("u", {{0, 1}}, 2, 32);
  SetElem(0, 1);
  SetElem(1, 2);

  PLI_BYTE8 sentinel[8] = {};
  s_vpi_arrayvalue av = {};
  av.format = vpiBinStrVal;  // a get-only string format, not supported here
  av.value.rawvals = sentinel;
  PLI_INT32 index[1] = {0};
  vpi_get_value_array(arr, &av, index, 2);

  SVpiErrorInfo info = {};
  EXPECT_EQ(VpiChkErrorC(&info), vpiError);
  EXPECT_EQ(av.value.rawvals, nullptr);  // value pointer overwritten to NULL
}

// §38.16: with vpiUserAllocFlag set, the application has pointed the value arm
// at its own buffer, and the routine fills that buffer rather than allocating
// VPI-owned storage.
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
  vpi_get_value_array(arr, &av, index, 2);

  EXPECT_EQ(av.value.integers, buffer);  // still the caller's own buffer
  EXPECT_EQ(buffer[0], 41);
  EXPECT_EQ(buffer[1], 42);
}

// §38.16: the vpiVectorVal format returns one aval/bval word group per element.
// The bval bits carry the unknown/high-impedance state of a 4-state element.
TEST_F(VpiGetValueArraySim, VectorValReturnsAvalAndBvalGroups) {
  VpiHandle arr = MakeArray("vv", {{0}}, 1, 16);
  SetElem(0, 0xABCD, 0x00F0);

  s_vpi_arrayvalue av = {};
  av.format = vpiVectorVal;
  PLI_INT32 index[1] = {0};
  vpi_get_value_array(arr, &av, index, 1);

  ASSERT_NE(av.value.vectors, nullptr);
  EXPECT_EQ(av.value.vectors[0].aval, 0xABCDu);
  EXPECT_EQ(av.value.vectors[0].bval, 0x00F0u);
}

// §38.16: the vpiLongIntVal format returns one 64-bit long per element through
// the *longints arm, retrieving the full width of an element wider than 32
// bits.
TEST_F(VpiGetValueArraySim, LongIntValReturnsSixtyFourBitElements) {
  VpiHandle arr = MakeArray("li", {{0}}, 1, 64);
  SetElem(0, 0x1122334455667788ull);

  s_vpi_arrayvalue av = {};
  av.format = vpiLongIntVal;
  PLI_INT32 index[1] = {0};
  vpi_get_value_array(arr, &av, index, 1);

  ASSERT_NE(av.value.longints, nullptr);
  EXPECT_EQ(av.value.longints[0], 0x1122334455667788ll);
}

// §38.16: the vpiShortIntVal format returns one short (16-bit) per element
// through the *shortints arm.
TEST_F(VpiGetValueArraySim, ShortIntValReturnsShortsPerElement) {
  VpiHandle arr = MakeArray("si", {{0, 1}}, 2, 16);
  SetElem(0, 0x0102);
  SetElem(1, 0x0304);

  s_vpi_arrayvalue av = {};
  av.format = vpiShortIntVal;
  PLI_INT32 index[1] = {0};
  vpi_get_value_array(arr, &av, index, 2);

  ASSERT_NE(av.value.shortints, nullptr);
  EXPECT_EQ(av.value.shortints[0], 0x0102);
  EXPECT_EQ(av.value.shortints[1], 0x0304);
}

// §38.16: the vpiShortRealVal format returns one float per element through the
// *shortreals arm; the element value is delivered as its floating-point form.
TEST_F(VpiGetValueArraySim, ShortRealValReturnsFloatsPerElement) {
  VpiHandle arr = MakeArray("sr", {{0, 1}}, 2, 32);
  SetElem(0, 42);
  SetElem(1, 7);

  s_vpi_arrayvalue av = {};
  av.format = vpiShortRealVal;
  PLI_INT32 index[1] = {0};
  vpi_get_value_array(arr, &av, index, 2);

  ASSERT_NE(av.value.shortreals, nullptr);
  EXPECT_FLOAT_EQ(av.value.shortreals[0], 42.0f);
  EXPECT_FLOAT_EQ(av.value.shortreals[1], 7.0f);
}

// §38.16: the vpiRealVal format (a get-value format reused for arrays) returns
// one double per element through the *reals arm.
TEST_F(VpiGetValueArraySim, RealValReturnsDoublesPerElement) {
  VpiHandle arr = MakeArray("re", {{0, 1}}, 2, 64);
  SetElem(0, 123);
  SetElem(1, 9);

  s_vpi_arrayvalue av = {};
  av.format = vpiRealVal;
  PLI_INT32 index[1] = {0};
  vpi_get_value_array(arr, &av, index, 2);

  ASSERT_NE(av.value.reals, nullptr);
  EXPECT_DOUBLE_EQ(av.value.reals[0], 123.0);
  EXPECT_DOUBLE_EQ(av.value.reals[1], 9.0);
}

// §38.16: index_p supplies the starting element's coordinate, one entry per
// unpacked dimension. With no index array there is no element to start from, so
// the routine records a VPI error and overwrites the value arm to NULL.
TEST_F(VpiGetValueArraySim, MissingStartingIndexIsError) {
  VpiHandle arr = MakeArray("ni", {{0, 1}}, 2, 32);
  SetElem(0, 3);
  SetElem(1, 4);

  PLI_INT32 sentinel[2] = {0, 0};
  s_vpi_arrayvalue av = {};
  av.format = vpiIntVal;
  av.value.integers = sentinel;  // non-NULL going in
  vpi_get_value_array(arr, &av, /*index_p=*/nullptr, 2);

  SVpiErrorInfo info = {};
  EXPECT_EQ(VpiChkErrorC(&info), vpiError);
  EXPECT_EQ(av.value.integers, nullptr);  // value arm overwritten to NULL
}

// §38.16: a starting coordinate must name a declared element of the array. An
// index value outside the array's declared range is not a legal element
// reference, so the routine errors and nulls the value arm.
TEST_F(VpiGetValueArraySim, OutOfRangeStartingIndexIsError) {
  VpiHandle arr = MakeArray("oor", {{0, 1}}, 2, 32);
  SetElem(0, 3);
  SetElem(1, 4);

  PLI_INT32 sentinel[2] = {0, 0};
  s_vpi_arrayvalue av = {};
  av.format = vpiIntVal;
  av.value.integers = sentinel;  // non-NULL going in
  PLI_INT32 index[1] = {5};      // no element with declared index 5 exists
  vpi_get_value_array(arr, &av, index, 2);

  SVpiErrorInfo info = {};
  EXPECT_EQ(VpiChkErrorC(&info), vpiError);
  EXPECT_EQ(av.value.integers, nullptr);  // value arm overwritten to NULL
}

// §38.16: the vpiTimeVal format returns one time structure per element through
// the *times arm; the element value splits into the high and low time words.
TEST_F(VpiGetValueArraySim, TimeValReturnsTimeWordsPerElement) {
  VpiHandle arr = MakeArray("tm", {{0}}, 1, 64);
  SetElem(0, (uint64_t{2} << 32) | 5u);

  s_vpi_arrayvalue av = {};
  av.format = vpiTimeVal;
  PLI_INT32 index[1] = {0};
  vpi_get_value_array(arr, &av, index, 1);

  ASSERT_NE(av.value.times, nullptr);
  EXPECT_EQ(av.value.times[0].high, 2u);
  EXPECT_EQ(av.value.times[0].low, 5u);
}

}  // namespace
}  // namespace delta
