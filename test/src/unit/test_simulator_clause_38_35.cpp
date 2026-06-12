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

class VpiPutValueArraySim : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  // Build a static unpacked array with `count` freshly created element
  // variables (all bits initialized to x), retaining the variable pointers so a
  // test can read back what vpi_put_value_array() wrote.
  VpiHandle MakeArray(std::string_view name,
                      const std::vector<std::vector<int>>& dims, int count,
                      uint32_t elem_width, int array_type = vpiStaticArray,
                      bool four_state = true) {
    elems_.clear();
    name_pool_.reserve(name_pool_.size() + count);
    for (int i = 0; i < count; ++i) {
      auto* v = sim_ctx_.CreateVariable(name_pool_.emplace_back(
                                            std::string(name) + std::to_string(i)),
                                        elem_width);
      v->is_4state = four_state;
      elems_.push_back(v);
    }
    return vpi_ctx_.CreateRegArray(name, array_type, dims, elems_);
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

// §38.35: index_p carries one starting index per unpacked dimension, and the
// elements are filled with the rightmost dimension varying fastest. For
// a[2:0][3:5] started at a[1][4] the fill order is a[1][4], a[1][5], a[0][3],
// a[0][4], a[0][5] - the example the standard gives.
TEST_F(VpiPutValueArraySim, MultiDimensionFillFollowsFastestVaryingIndex) {
  // Flat ordinals (rightmost fastest): a[1][4]=4, a[1][5]=5, a[0][3]=6,
  // a[0][4]=7, a[0][5]=8.
  VpiHandle arr = MakeArray("m", {{2, 1, 0}, {3, 4, 5}}, 9, 8);

  PLI_INT32 ints[5] = {11, 12, 13, 14, 15};
  s_vpi_arrayvalue av = {};
  av.format = vpiIntVal;
  av.value.integers = ints;
  PLI_INT32 index[2] = {1, 4};
  vpi_put_value_array(arr, &av, index, 5);

  EXPECT_EQ(elems_[4]->value.words[0].aval, 11u);  // a[1][4]
  EXPECT_EQ(elems_[5]->value.words[0].aval, 12u);  // a[1][5]
  EXPECT_EQ(elems_[6]->value.words[0].aval, 13u);  // a[0][3]
  EXPECT_EQ(elems_[7]->value.words[0].aval, 14u);  // a[0][4]
  EXPECT_EQ(elems_[8]->value.words[0].aval, 15u);  // a[0][5]
  // The earlier ordinals were never in the section.
  EXPECT_EQ(elems_[0]->value.words[0].bval, ~uint64_t{0});
  EXPECT_EQ(elems_[3]->value.words[0].bval, ~uint64_t{0});
}

// §38.35: in vpiRawFourStateVal format each element occupies ngroups*2 bytes -
// an aval byte group followed by a bval byte group - and the bytes are loaded
// least-significant first into the element's value.
TEST_F(VpiPutValueArraySim, RawFourStateValDecodesAvalAndBval) {
  VpiHandle arr = MakeArray("r", {{0, 1}}, 2, 8);  // ngroups = 1

  // element 0: aval 0xA5, bval 0x0F; element 1: aval 0x3C, bval 0x00.
  PLI_BYTE8 raw[4] = {static_cast<PLI_BYTE8>(0xA5), static_cast<PLI_BYTE8>(0x0F),
                      static_cast<PLI_BYTE8>(0x3C), static_cast<PLI_BYTE8>(0x00)};
  s_vpi_arrayvalue av = {};
  av.format = vpiRawFourStateVal;
  av.value.rawvals = raw;
  PLI_INT32 index[1] = {0};
  vpi_put_value_array(arr, &av, index, 2);

  EXPECT_EQ(elems_[0]->value.words[0].aval, 0xA5u);
  EXPECT_EQ(elems_[0]->value.words[0].bval, 0x0Fu);
  EXPECT_EQ(elems_[1]->value.words[0].aval, 0x3Cu);
  EXPECT_EQ(elems_[1]->value.words[0].bval, 0x00u);
}

// §38.35: if the vpiRawFourStateVal format is set for a 2-state array type, the
// bvalbits group is ignored - the element keeps a known (bval 0) value.
TEST_F(VpiPutValueArraySim, RawFourStateValIgnoresBvalForTwoStateArray) {
  VpiHandle arr = MakeArray("t", {{0}}, 1, 8, vpiStaticArray, /*four_state=*/false);

  PLI_BYTE8 raw[2] = {static_cast<PLI_BYTE8>(0xF0),
                      static_cast<PLI_BYTE8>(0xFF)};  // bval group all ones
  s_vpi_arrayvalue av = {};
  av.format = vpiRawFourStateVal;
  av.value.rawvals = raw;
  PLI_INT32 index[1] = {0};
  vpi_put_value_array(arr, &av, index, 1);

  EXPECT_EQ(elems_[0]->value.words[0].aval, 0xF0u);
  EXPECT_EQ(elems_[0]->value.words[0].bval, 0x00u);  // bvalbits ignored
}

// §38.35: in vpiRawTwoStateVal format the bvalbits group is omitted (storage is
// ngroups bytes per element). For a 4-state array the missing bval bits are
// assumed to be 0.
TEST_F(VpiPutValueArraySim, RawTwoStateValAssumesBvalZeroForFourStateArray) {
  VpiHandle arr = MakeArray("w", {{0, 1}}, 2, 8);  // 4-state, ngroups = 1

  PLI_BYTE8 raw[2] = {static_cast<PLI_BYTE8>(0x55),
                      static_cast<PLI_BYTE8>(0xAA)};
  s_vpi_arrayvalue av = {};
  av.format = vpiRawTwoStateVal;
  av.value.rawvals = raw;
  PLI_INT32 index[1] = {0};
  vpi_put_value_array(arr, &av, index, 2);

  EXPECT_EQ(elems_[0]->value.words[0].aval, 0x55u);
  EXPECT_EQ(elems_[0]->value.words[0].bval, 0x00u);
  EXPECT_EQ(elems_[1]->value.words[0].aval, 0xAAu);
  EXPECT_EQ(elems_[1]->value.words[0].bval, 0x00u);
}

// §38.35: the vpiOneValue flag applies a single supplied element value to the
// whole selected section, so only one element's data need be provided.
TEST_F(VpiPutValueArraySim, OneValueBroadcastsSingleElement) {
  VpiHandle arr = MakeArray("o", {{0, 1, 2}}, 3, 32);

  PLI_INT32 ints[1] = {99};
  s_vpi_arrayvalue av = {};
  av.format = vpiIntVal;
  av.flags = vpiOneValue;
  av.value.integers = ints;
  PLI_INT32 index[1] = {0};
  vpi_put_value_array(arr, &av, index, 3);

  EXPECT_EQ(elems_[0]->value.words[0].aval, 99u);
  EXPECT_EQ(elems_[1]->value.words[0].aval, 99u);
  EXPECT_EQ(elems_[2]->value.words[0].aval, 99u);
}

// §38.35: vpiPropagateOff is one of the flags the routine permits, so a put
// carrying it succeeds and records no error.
TEST_F(VpiPutValueArraySim, PropagateOffFlagIsAccepted) {
  VpiHandle arr = MakeArray("p", {{0, 1}}, 2, 32);

  PLI_INT32 ints[2] = {5, 6};
  s_vpi_arrayvalue av = {};
  av.format = vpiIntVal;
  av.flags = vpiPropagateOff;
  av.value.integers = ints;
  PLI_INT32 index[1] = {0};
  vpi_put_value_array(arr, &av, index, 2);

  SVpiErrorInfo info = {};
  EXPECT_EQ(VpiChkErrorC(&info), 0);
  EXPECT_EQ(elems_[0]->value.words[0].aval, 5u);
  EXPECT_EQ(elems_[1]->value.words[0].aval, 6u);
}

// §38.35: every format outside the supported set is unsupported and is an error
// if specified; the array is left untouched.
TEST_F(VpiPutValueArraySim, UnsupportedFormatIsError) {
  VpiHandle arr = MakeArray("u", {{0, 1}}, 2, 32);

  s_vpi_arrayvalue av = {};
  av.format = vpiBinStrVal;  // a get-only string format, not allowed here
  PLI_INT32 index[1] = {0};
  vpi_put_value_array(arr, &av, index, 2);

  SVpiErrorInfo info = {};
  EXPECT_EQ(VpiChkErrorC(&info), vpiError);
  EXPECT_EQ(elems_[0]->value.words[0].bval, ~uint64_t{0});  // unchanged
}

// §38.35: only vpiOneValue, vpiPropagateOff, and vpiNoDelay (the default) are
// allowed. Any other flag bit makes the call an error and writes nothing.
TEST_F(VpiPutValueArraySim, IllegalFlagIsError) {
  VpiHandle arr = MakeArray("f", {{0, 1}}, 2, 32);

  PLI_INT32 ints[2] = {1, 2};
  s_vpi_arrayvalue av = {};
  av.format = vpiIntVal;
  av.flags = vpiUserAllocFlag;  // not one of the permitted flags
  av.value.integers = ints;
  PLI_INT32 index[1] = {0};
  vpi_put_value_array(arr, &av, index, 2);

  SVpiErrorInfo info = {};
  EXPECT_EQ(VpiChkErrorC(&info), vpiError);
  EXPECT_EQ(elems_[0]->value.words[0].bval, ~uint64_t{0});  // unchanged
}

// §38.35: the routine modifies only static unpacked arrays (vpiArrayType
// vpiStaticArray). A non-static array is rejected and the array is unchanged.
TEST_F(VpiPutValueArraySim, NonStaticArrayIsError) {
  VpiHandle arr = MakeArray("d", {{0, 1}}, 2, 32, vpiDynamicArray);

  PLI_INT32 ints[2] = {1, 2};
  s_vpi_arrayvalue av = {};
  av.format = vpiIntVal;
  av.value.integers = ints;
  PLI_INT32 index[1] = {0};
  vpi_put_value_array(arr, &av, index, 2);

  SVpiErrorInfo info = {};
  EXPECT_EQ(VpiChkErrorC(&info), vpiError);
  EXPECT_EQ(elems_[0]->value.words[0].bval, ~uint64_t{0});  // unchanged
}

// §38.35: in the raw formats an element occupies ngroups = (elemBits + 7)/8
// bytes per aval/bval group, and the bytes are loaded least-significant first -
// byte 0 holds bits 0..7, byte 1 holds bits 8..15, and so on. A 16-bit element
// spans two bytes per group, so the second byte must land in the high half.
TEST_F(VpiPutValueArraySim, RawFourStateValLoadsBytesLeastSignificantFirst) {
  VpiHandle arr = MakeArray("b", {{0}}, 1, 16);  // ngroups = 2

  // aval group {0x34, 0x12} -> 0x1234; bval group {0x00, 0x00} -> 0.
  PLI_BYTE8 raw[4] = {static_cast<PLI_BYTE8>(0x34), static_cast<PLI_BYTE8>(0x12),
                      static_cast<PLI_BYTE8>(0x00),
                      static_cast<PLI_BYTE8>(0x00)};
  s_vpi_arrayvalue av = {};
  av.format = vpiRawFourStateVal;
  av.value.rawvals = raw;
  PLI_INT32 index[1] = {0};
  vpi_put_value_array(arr, &av, index, 1);

  EXPECT_EQ(elems_[0]->value.words[0].aval, 0x1234u);
  EXPECT_EQ(elems_[0]->value.words[0].bval, 0x0000u);
}

// §38.35: when the object is a vpiArrayNet, the supplied values override the
// resolved values of the named array net elements. The override write lands in
// the element values just as it does for a reg array. (The persistence of the
// override until a driver next changes is a property of net resolution, outside
// this routine.)
TEST_F(VpiPutValueArraySim, NetArrayTargetOverridesElementValues) {
  VpiHandle arr = MakeArray("n", {{0, 1, 2}}, 3, 32);
  arr->type = vpiNetArray;  // present the array as a net array

  PLI_INT32 ints[2] = {44, 55};
  s_vpi_arrayvalue av = {};
  av.format = vpiIntVal;
  av.value.integers = ints;
  PLI_INT32 index[1] = {1};
  vpi_put_value_array(arr, &av, index, 2);

  SVpiErrorInfo info = {};
  EXPECT_EQ(VpiChkErrorC(&info), 0);
  EXPECT_EQ(elems_[1]->value.words[0].aval, 44u);
  EXPECT_EQ(elems_[2]->value.words[0].aval, 55u);
  EXPECT_EQ(elems_[0]->value.words[0].bval, ~uint64_t{0});  // outside section
}

// §38.35: the vpiShortIntVal format supplies one short per element through the
// *shortints arm - appropriate for short/int/long-int element types.
TEST_F(VpiPutValueArraySim, ShortIntValWritesShortsToElements) {
  VpiHandle arr = MakeArray("si", {{0, 1}}, 2, 16);

  PLI_INT16 shorts[2] = {0x0102, 0x0304};
  s_vpi_arrayvalue av = {};
  av.format = vpiShortIntVal;
  av.value.shortints = shorts;
  PLI_INT32 index[1] = {0};
  vpi_put_value_array(arr, &av, index, 2);

  EXPECT_EQ(elems_[0]->value.words[0].aval, 0x0102u);
  EXPECT_EQ(elems_[1]->value.words[0].aval, 0x0304u);
}

// §38.35: the vpiLongIntVal format supplies one long (64-bit) per element
// through the *longints arm - appropriate for long-int element types.
TEST_F(VpiPutValueArraySim, LongIntValWritesLongsToElements) {
  VpiHandle arr = MakeArray("li", {{0}}, 1, 64);

  PLI_INT64 longs[1] = {0x1122334455667788LL};
  s_vpi_arrayvalue av = {};
  av.format = vpiLongIntVal;
  av.value.longints = longs;
  PLI_INT32 index[1] = {0};
  vpi_put_value_array(arr, &av, index, 1);

  EXPECT_EQ(elems_[0]->value.words[0].aval, 0x1122334455667788ull);
}

// §38.35: the vpiShortRealVal format supplies one float per element through the
// *shortreals arm - appropriate for shortreal element types.
TEST_F(VpiPutValueArraySim, ShortRealValWritesFloatsToElements) {
  VpiHandle arr = MakeArray("sr", {{0, 1}}, 2, 32);

  float shortreals[2] = {42.0f, 7.0f};
  s_vpi_arrayvalue av = {};
  av.format = vpiShortRealVal;
  av.value.shortreals = shortreals;
  PLI_INT32 index[1] = {0};
  vpi_put_value_array(arr, &av, index, 2);

  EXPECT_EQ(elems_[0]->value.words[0].aval, 42u);
  EXPECT_EQ(elems_[1]->value.words[0].aval, 7u);
}

// §38.35: the vpiRealVal format (a get-value format reused here for arrays)
// supplies one double per element through the *reals arm.
TEST_F(VpiPutValueArraySim, RealValWritesRealsToElements) {
  VpiHandle arr = MakeArray("re", {{0, 1}}, 2, 64);

  double reals[2] = {123.0, 9.0};
  s_vpi_arrayvalue av = {};
  av.format = vpiRealVal;
  av.value.reals = reals;
  PLI_INT32 index[1] = {0};
  vpi_put_value_array(arr, &av, index, 2);

  EXPECT_EQ(elems_[0]->value.words[0].aval, 123u);
  EXPECT_EQ(elems_[1]->value.words[0].aval, 9u);
}

// §38.35: the vpiTimeVal format supplies one time structure per element through
// the *times arm; the high and low words combine into the element value.
TEST_F(VpiPutValueArraySim, TimeValWritesTimeWordsToElements) {
  VpiHandle arr = MakeArray("tm", {{0}}, 1, 64);

  s_vpi_time times[1] = {};
  times[0].high = 2;
  times[0].low = 5;
  s_vpi_arrayvalue av = {};
  av.format = vpiTimeVal;
  av.value.times = times;
  PLI_INT32 index[1] = {0};
  vpi_put_value_array(arr, &av, index, 1);

  EXPECT_EQ(elems_[0]->value.words[0].aval, (uint64_t{2} << 32) | 5u);
}

// §38.35: the vpiVectorVal format supplies aval/bval word groups per element
// through the *vectors arm. On a 4-state element the bval bits are kept.
TEST_F(VpiPutValueArraySim, VectorValWritesVecvalGroupsToElements) {
  VpiHandle arr = MakeArray("vv", {{0}}, 1, 16);

  s_vpi_vecval vecs[1] = {};
  vecs[0].aval = 0xABCD;
  vecs[0].bval = 0x00F0;
  s_vpi_arrayvalue av = {};
  av.format = vpiVectorVal;
  av.value.vectors = vecs;
  PLI_INT32 index[1] = {0};
  vpi_put_value_array(arr, &av, index, 1);

  EXPECT_EQ(elems_[0]->value.words[0].aval, 0xABCDu);
  EXPECT_EQ(elems_[0]->value.words[0].bval, 0x00F0u);
}

}
}
