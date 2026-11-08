#include <gtest/gtest.h>

#include <cstdint>

#include "fixture_vpi_run.h"
#include "helpers_vpi_value_array.h"
#include "simulator/sim_context.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/variable.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

using VpiPutValueArraySim = VpiValueArraySimBase;

TEST_F(VpiPutValueArraySim, MultiDimensionFillFollowsFastestVaryingIndex) {
  VpiHandle arr = MakeArray("m", {{2, 1, 0}, {3, 4, 5}}, 9, 8);

  PLI_INT32 ints[5] = {11, 12, 13, 14, 15};
  s_vpi_arrayvalue av = {};
  av.format = vpiIntVal;
  av.value.integers = ints;
  PLI_INT32 index[2] = {1, 4};
  vpi_put_value_array(VpiHandleOf(arr), &av, index, 5);

  EXPECT_EQ(elems_[4]->value.words[0].aval, 11u);
  EXPECT_EQ(elems_[5]->value.words[0].aval, 12u);
  EXPECT_EQ(elems_[6]->value.words[0].aval, 13u);
  EXPECT_EQ(elems_[7]->value.words[0].aval, 14u);
  EXPECT_EQ(elems_[8]->value.words[0].aval, 15u);
  EXPECT_EQ(elems_[0]->value.words[0].bval, 0xFFu);
  EXPECT_EQ(elems_[3]->value.words[0].bval, 0xFFu);
}

TEST_F(VpiPutValueArraySim, RawFourStateValDecodesAvalAndBval) {
  VpiHandle arr = MakeArray("r", {{0, 1}}, 2, 8);

  PLI_BYTE8 raw[4] = {
      static_cast<PLI_BYTE8>(0xA5), static_cast<PLI_BYTE8>(0x0F),
      static_cast<PLI_BYTE8>(0x3C), static_cast<PLI_BYTE8>(0x00)};
  s_vpi_arrayvalue av = {};
  av.format = vpiRawFourStateVal;
  av.value.rawvals = raw;
  PLI_INT32 index[1] = {0};
  vpi_put_value_array(VpiHandleOf(arr), &av, index, 2);

  EXPECT_EQ(elems_[0]->value.words[0].aval, 0xA5u);
  EXPECT_EQ(elems_[0]->value.words[0].bval, 0x0Fu);
  EXPECT_EQ(elems_[1]->value.words[0].aval, 0x3Cu);
  EXPECT_EQ(elems_[1]->value.words[0].bval, 0x00u);
}

TEST_F(VpiPutValueArraySim, RawFourStateValIgnoresBvalForTwoStateArray) {
  VpiHandle arr = MakeArray("t", {{0}}, 1, 8, {vpiStaticArray, false});

  PLI_BYTE8 raw[2] = {static_cast<PLI_BYTE8>(0xF0),
                      static_cast<PLI_BYTE8>(0xFF)};
  s_vpi_arrayvalue av = {};
  av.format = vpiRawFourStateVal;
  av.value.rawvals = raw;
  PLI_INT32 index[1] = {0};
  vpi_put_value_array(VpiHandleOf(arr), &av, index, 1);

  EXPECT_EQ(elems_[0]->value.words[0].aval, 0xF0u);
  EXPECT_EQ(elems_[0]->value.words[0].bval, 0x00u);
}

TEST_F(VpiPutValueArraySim, RawTwoStateValAssumesBvalZeroForFourStateArray) {
  VpiHandle arr = MakeArray("w", {{0, 1}}, 2, 8);

  PLI_BYTE8 raw[2] = {static_cast<PLI_BYTE8>(0x55),
                      static_cast<PLI_BYTE8>(0xAA)};
  s_vpi_arrayvalue av = {};
  av.format = vpiRawTwoStateVal;
  av.value.rawvals = raw;
  PLI_INT32 index[1] = {0};
  vpi_put_value_array(VpiHandleOf(arr), &av, index, 2);

  EXPECT_EQ(elems_[0]->value.words[0].aval, 0x55u);
  EXPECT_EQ(elems_[0]->value.words[0].bval, 0x00u);
  EXPECT_EQ(elems_[1]->value.words[0].aval, 0xAAu);
  EXPECT_EQ(elems_[1]->value.words[0].bval, 0x00u);
}

TEST_F(VpiPutValueArraySim, OneValueBroadcastsSingleElement) {
  VpiHandle arr = MakeArray("o", {{0, 1, 2}}, 3, 32);

  PLI_INT32 ints[1] = {99};
  s_vpi_arrayvalue av = {};
  av.format = vpiIntVal;
  av.flags = vpiOneValue;
  av.value.integers = ints;
  PLI_INT32 index[1] = {0};
  vpi_put_value_array(VpiHandleOf(arr), &av, index, 3);

  EXPECT_EQ(elems_[0]->value.words[0].aval, 99u);
  EXPECT_EQ(elems_[1]->value.words[0].aval, 99u);
  EXPECT_EQ(elems_[2]->value.words[0].aval, 99u);
}

TEST_F(VpiPutValueArraySim, PropagateOffFlagIsAccepted) {
  VpiHandle arr = MakeArray("p", {{0, 1}}, 2, 32);

  PLI_INT32 ints[2] = {5, 6};
  s_vpi_arrayvalue av = {};
  av.format = vpiIntVal;
  av.flags = vpiPropagateOff;
  av.value.integers = ints;
  PLI_INT32 index[1] = {0};
  vpi_put_value_array(VpiHandleOf(arr), &av, index, 2);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), 0);
  EXPECT_EQ(elems_[0]->value.words[0].aval, 5u);
  EXPECT_EQ(elems_[1]->value.words[0].aval, 6u);
}

TEST_F(VpiPutValueArraySim, FanoutsOfTheWrittenElementsAreToldValuesChanged) {
  VpiHandle arr = MakeArray("n", {{0, 1, 2}}, 3, 32);
  int notified[3] = {0, 0, 0};
  for (int i = 0; i < 3; ++i) {
    elems_[i]->AddWatcher([&notified, i]() {
      ++notified[i];
      return true;
    });
  }

  PLI_INT32 ints[2] = {7, 8};
  s_vpi_arrayvalue av = {};
  av.format = vpiIntVal;
  av.value.integers = ints;
  PLI_INT32 index[1] = {0};
  vpi_put_value_array(VpiHandleOf(arr), &av, index, 2);

  EXPECT_EQ(notified[0], 1);
  EXPECT_EQ(notified[1], 1);
  EXPECT_EQ(notified[2], 0);
}

TEST_F(VpiPutValueArraySim, PropagateOffWithholdsThatNotificationFromThem) {
  VpiHandle arr = MakeArray("q", {{0, 1, 2}}, 3, 32);
  int notified = 0;
  for (int i = 0; i < 3; ++i) {
    elems_[i]->AddWatcher([&notified]() {
      ++notified;
      return true;
    });
  }

  PLI_INT32 ints[3] = {1, 2, 3};
  s_vpi_arrayvalue av = {};
  av.format = vpiIntVal;
  av.flags = vpiPropagateOff;
  av.value.integers = ints;
  PLI_INT32 index[1] = {0};
  vpi_put_value_array(VpiHandleOf(arr), &av, index, 3);

  EXPECT_EQ(notified, 0);
  EXPECT_EQ(elems_[0]->value.words[0].aval, 1u);
  EXPECT_EQ(elems_[2]->value.words[0].aval, 3u);
}

TEST_F(VpiPutValueArraySim, UnsupportedFormatIsError) {
  VpiHandle arr = MakeArray("u", {{0, 1}}, 2, 32);

  s_vpi_arrayvalue av = {};
  av.format = vpiBinStrVal;
  PLI_INT32 index[1] = {0};
  vpi_put_value_array(VpiHandleOf(arr), &av, index, 2);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
  EXPECT_EQ(elems_[0]->value.words[0].bval, 0xFFFFFFFFu);
}

TEST_F(VpiPutValueArraySim, IllegalFlagIsError) {
  VpiHandle arr = MakeArray("f", {{0, 1}}, 2, 32);

  PLI_INT32 ints[2] = {1, 2};
  s_vpi_arrayvalue av = {};
  av.format = vpiIntVal;
  av.flags = vpiUserAllocFlag;
  av.value.integers = ints;
  PLI_INT32 index[1] = {0};
  vpi_put_value_array(VpiHandleOf(arr), &av, index, 2);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
  EXPECT_EQ(elems_[0]->value.words[0].bval, 0xFFFFFFFFu);
}

TEST_F(VpiPutValueArraySim, NonStaticArrayIsError) {
  VpiHandle arr = MakeArray("d", {{0, 1}}, 2, 32, {vpiDynamicArray});

  PLI_INT32 ints[2] = {1, 2};
  s_vpi_arrayvalue av = {};
  av.format = vpiIntVal;
  av.value.integers = ints;
  PLI_INT32 index[1] = {0};
  vpi_put_value_array(VpiHandleOf(arr), &av, index, 2);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
  EXPECT_EQ(elems_[0]->value.words[0].bval, 0xFFFFFFFFu);
}

TEST_F(VpiPutValueArraySim, RawFourStateValLoadsBytesLeastSignificantFirst) {
  VpiHandle arr = MakeArray("b", {{0}}, 1, 16);

  PLI_BYTE8 raw[4] = {
      static_cast<PLI_BYTE8>(0x34), static_cast<PLI_BYTE8>(0x12),
      static_cast<PLI_BYTE8>(0x00), static_cast<PLI_BYTE8>(0x00)};
  s_vpi_arrayvalue av = {};
  av.format = vpiRawFourStateVal;
  av.value.rawvals = raw;
  PLI_INT32 index[1] = {0};
  vpi_put_value_array(VpiHandleOf(arr), &av, index, 1);

  EXPECT_EQ(elems_[0]->value.words[0].aval, 0x1234u);
  EXPECT_EQ(elems_[0]->value.words[0].bval, 0x0000u);
}

TEST_F(VpiPutValueArraySim, NetArrayTargetOverridesElementValues) {
  VpiHandle arr = MakeArray("n", {{0, 1, 2}}, 3, 32);
  arr->type = vpiNetArray;

  PLI_INT32 ints[2] = {44, 55};
  s_vpi_arrayvalue av = {};
  av.format = vpiIntVal;
  av.value.integers = ints;
  PLI_INT32 index[1] = {1};
  vpi_put_value_array(VpiHandleOf(arr), &av, index, 2);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), 0);
  EXPECT_EQ(elems_[1]->value.words[0].aval, 44u);
  EXPECT_EQ(elems_[2]->value.words[0].aval, 55u);
  EXPECT_EQ(elems_[0]->value.words[0].bval, 0xFFFFFFFFu);
}

TEST_F(VpiPutValueArraySim, ShortIntValWritesShortsToElements) {
  VpiHandle arr = MakeArray("si", {{0, 1}}, 2, 16);

  PLI_INT16 shorts[2] = {0x0102, 0x0304};
  s_vpi_arrayvalue av = {};
  av.format = vpiShortIntVal;
  av.value.shortints = shorts;
  PLI_INT32 index[1] = {0};
  vpi_put_value_array(VpiHandleOf(arr), &av, index, 2);

  EXPECT_EQ(elems_[0]->value.words[0].aval, 0x0102u);
  EXPECT_EQ(elems_[1]->value.words[0].aval, 0x0304u);
}

TEST_F(VpiPutValueArraySim, LongIntValWritesLongsToElements) {
  VpiHandle arr = MakeArray("li", {{0}}, 1, 64);

  PLI_INT64 longs[1] = {0x1122334455667788LL};
  s_vpi_arrayvalue av = {};
  av.format = vpiLongIntVal;
  av.value.longints = longs;
  PLI_INT32 index[1] = {0};
  vpi_put_value_array(VpiHandleOf(arr), &av, index, 1);

  EXPECT_EQ(elems_[0]->value.words[0].aval, 0x1122334455667788ull);
}

TEST_F(VpiPutValueArraySim, ShortRealValWritesFloatsToElements) {
  VpiHandle arr = MakeArray("sr", {{0, 1}}, 2, 32);

  float shortreals[2] = {42.0f, 7.0f};
  s_vpi_arrayvalue av = {};
  av.format = vpiShortRealVal;
  av.value.shortreals = shortreals;
  PLI_INT32 index[1] = {0};
  vpi_put_value_array(VpiHandleOf(arr), &av, index, 2);

  EXPECT_EQ(elems_[0]->value.words[0].aval, 42u);
  EXPECT_EQ(elems_[1]->value.words[0].aval, 7u);
}

TEST_F(VpiPutValueArraySim, RealValWritesRealsToElements) {
  VpiHandle arr = MakeArray("re", {{0, 1}}, 2, 64);

  double reals[2] = {123.0, 9.0};
  s_vpi_arrayvalue av = {};
  av.format = vpiRealVal;
  av.value.reals = reals;
  PLI_INT32 index[1] = {0};
  vpi_put_value_array(VpiHandleOf(arr), &av, index, 2);

  EXPECT_EQ(elems_[0]->value.words[0].aval, 123u);
  EXPECT_EQ(elems_[1]->value.words[0].aval, 9u);
}

TEST_F(VpiPutValueArraySim, TimeValWritesTimeWordsToElements) {
  VpiHandle arr = MakeArray("tm", {{0}}, 1, 64);

  s_vpi_time times[1] = {};
  times[0].high = 2;
  times[0].low = 5;
  s_vpi_arrayvalue av = {};
  av.format = vpiTimeVal;
  av.value.times = times;
  PLI_INT32 index[1] = {0};
  vpi_put_value_array(VpiHandleOf(arr), &av, index, 1);

  EXPECT_EQ(elems_[0]->value.words[0].aval, (uint64_t{2} << 32) | 5u);
}

TEST_F(VpiPutValueArraySim, VectorValWritesVecvalGroupsToElements) {
  VpiHandle arr = MakeArray("vv", {{0}}, 1, 16);

  s_vpi_vecval vecs[1] = {};
  vecs[0].aval = 0xABCD;
  vecs[0].bval = 0x00F0;
  s_vpi_arrayvalue av = {};
  av.format = vpiVectorVal;
  av.value.vectors = vecs;
  PLI_INT32 index[1] = {0};
  vpi_put_value_array(VpiHandleOf(arr), &av, index, 1);

  EXPECT_EQ(elems_[0]->value.words[0].aval, 0xABCDu);
  EXPECT_EQ(elems_[0]->value.words[0].bval, 0x00F0u);
}

TEST_F(VpiPutValueArraySim, ANullHandleOrValueWritesNothing) {
  VpiHandle arr = MakeArray("nh", {{0}}, 1, 32);
  PLI_INT32 ints[1] = {7};
  s_vpi_arrayvalue av = {};
  av.format = vpiIntVal;
  av.value.integers = ints;
  PLI_INT32 index[1] = {0};
  vpi_put_value_array(nullptr, &av, index, 1);
  vpi_put_value_array(VpiHandleOf(arr), nullptr, index, 1);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), 0);
  EXPECT_EQ(elems_[0]->value.words[0].bval, 0xFFFFFFFFu);
}

TEST_F(VpiPutValueArraySim, NoValueIsWrittenFromAReadOnlySynchCallback) {
  VpiHandle arr = MakeArray("ro", {{0}}, 1, 32);
  vpi_ctx_.SetAtReadOnlySynchTime(true);
  PLI_INT32 ints[1] = {7};
  s_vpi_arrayvalue av = {};
  av.format = vpiIntVal;
  av.value.integers = ints;
  PLI_INT32 index[1] = {0};
  vpi_put_value_array(VpiHandleOf(arr), &av, index, 1);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
  EXPECT_EQ(elems_[0]->value.words[0].bval, 0xFFFFFFFFu);
}

TEST_F(VpiPutValueArraySim, AHandleToNoArrayIsError) {
  VpiHandle arr = MakeArray("na", {{0}}, 1, 32);
  arr->type = vpiReg;
  PLI_INT32 ints[1] = {7};
  s_vpi_arrayvalue av = {};
  av.format = vpiIntVal;
  av.value.integers = ints;
  PLI_INT32 index[1] = {0};
  vpi_put_value_array(VpiHandleOf(arr), &av, index, 1);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
  EXPECT_EQ(elems_[0]->value.words[0].bval, 0xFFFFFFFFu);
}

TEST_F(VpiPutValueArraySim, NoStartingIndexIsError) {
  PLI_INT32 ints[1] = {7};
  s_vpi_arrayvalue av = {};
  av.format = vpiIntVal;
  av.value.integers = ints;
  s_vpi_error_info info = {};

  VpiHandle arr = MakeArray("mi", {{0}}, 1, 32);
  vpi_put_value_array(VpiHandleOf(arr), &av, nullptr, 1);
  EXPECT_EQ(vpi_chk_error(&info), vpiError);

  VpiHandle undimensioned = MakeArray("ud", {}, 1, 32);
  PLI_INT32 index[1] = {0};
  vpi_put_value_array(VpiHandleOf(undimensioned), &av, index, 1);
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
  EXPECT_EQ(elems_[0]->value.words[0].bval, 0xFFFFFFFFu);
}

TEST_F(VpiPutValueArraySim, OutOfRangeStartingIndexIsError) {
  VpiHandle arr = MakeArray("oo", {{0, 1}}, 2, 32);
  PLI_INT32 ints[1] = {7};
  s_vpi_arrayvalue av = {};
  av.format = vpiIntVal;
  av.value.integers = ints;
  PLI_INT32 index[1] = {5};
  vpi_put_value_array(VpiHandleOf(arr), &av, index, 1);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
  EXPECT_EQ(elems_[0]->value.words[0].bval, 0xFFFFFFFFu);
  EXPECT_EQ(elems_[1]->value.words[0].bval, 0xFFFFFFFFu);
}

TEST_F(VpiPutValueArraySim, PositionsWithNothingToWriteArePassedOver) {
  Variable* stored = sim_ctx_.CreateVariable("ps1", 32);
  VpiHandle arr = vpi_ctx_.CreateRegArray("ps", vpiStaticArray, {{0, 1, 2}},
                                          {nullptr, stored});
  PLI_INT32 ints[3] = {5, 6, 7};
  s_vpi_arrayvalue av = {};
  av.format = vpiIntVal;
  av.value.integers = ints;
  PLI_INT32 index[1] = {0};
  vpi_put_value_array(VpiHandleOf(arr), &av, index, 3);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), 0);
  EXPECT_EQ(stored->value.words[0].aval, 6u);
  EXPECT_EQ(stored->value.words[0].bval, 0u);
}

TEST_F(VpiPutValueArraySim, VectorValOnATwoStateArrayDropsTheBvalBits) {
  VpiHandle arr = MakeArray("v2", {{0}}, 1, 16, {vpiStaticArray, false});
  s_vpi_vecval vecs[1] = {};
  vecs[0].aval = 0x1234;
  vecs[0].bval = 0x00FF;
  s_vpi_arrayvalue av = {};
  av.format = vpiVectorVal;
  av.value.vectors = vecs;
  PLI_INT32 index[1] = {0};
  vpi_put_value_array(VpiHandleOf(arr), &av, index, 1);

  EXPECT_EQ(elems_[0]->value.words[0].aval, 0x1234u);
  EXPECT_EQ(elems_[0]->value.words[0].bval, 0u);
}

TEST_F(VpiPutValueArraySim, RawFormatsCarryAnElementWiderThan64Bits) {
  PLI_BYTE8 four[18] = {1, 2, 3, 4, 5, 6, 7, 8, 9,
                        0, 0, 0, 0, 0, 0, 0, 0, static_cast<PLI_BYTE8>(0x80)};
  s_vpi_arrayvalue av = {};
  av.format = vpiRawFourStateVal;
  av.value.rawvals = four;
  PLI_INT32 index[1] = {0};
  VpiHandle arr = MakeArray("w4", {{0}}, 1, 72);
  vpi_put_value_array(VpiHandleOf(arr), &av, index, 1);
  EXPECT_EQ(elems_[0]->value.words[0].aval, 0x0807060504030201u);
  EXPECT_EQ(elems_[0]->value.words[0].bval, 0u);
  EXPECT_EQ(elems_[0]->value.words[1].aval, 0x09u);
  EXPECT_EQ(elems_[0]->value.words[1].bval, 0x80u);

  PLI_BYTE8 two[9] = {1, 2, 3, 4, 5, 6, 7, 8, 0x0A};
  av.format = vpiRawTwoStateVal;
  av.value.rawvals = two;
  arr = MakeArray("w2", {{0}}, 1, 72);
  vpi_put_value_array(VpiHandleOf(arr), &av, index, 1);
  EXPECT_EQ(elems_[0]->value.words[1].aval, 0x0Au);
  EXPECT_EQ(elems_[0]->value.words[1].bval, 0u);
}

TEST_F(VpiPutValueArraySim, VectorValCarriesAnElementWiderThan32Bits) {
  VpiHandle arr = MakeArray("v40", {{0, 1}}, 2, 40);
  s_vpi_vecval vecs[4] = {
      {0x11111111, 0}, {0xAB, 0x01}, {0x22222222, 0}, {0xCD, 0}};
  s_vpi_arrayvalue av = {};
  av.format = vpiVectorVal;
  av.value.vectors = vecs;
  PLI_INT32 index[1] = {0};
  vpi_put_value_array(VpiHandleOf(arr), &av, index, 2);

  EXPECT_EQ(elems_[0]->value.words[0].aval, 0xAB11111111u);
  EXPECT_EQ(elems_[0]->value.words[0].bval, 0x0100000000u);
  EXPECT_EQ(elems_[1]->value.words[0].aval, 0xCD22222222u);
  EXPECT_EQ(elems_[1]->value.words[0].bval, 0u);
}

TEST_F(VpiPutValueArraySim, AnArrayOfStringsIsRefused) {
  VpiHandle arr = MakeArray("st", {{0, 1}}, 2, 8);
  elems_[0]->is_string = true;
  PLI_INT32 ints[2] = {1, 2};
  s_vpi_arrayvalue av = {};
  av.format = vpiIntVal;
  av.value.integers = ints;
  PLI_INT32 index[1] = {0};
  vpi_put_value_array(VpiHandleOf(arr), &av, index, 2);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
  EXPECT_EQ(elems_[1]->value.words[0].bval, 0xFFu);
}

class ElementPutsOfARun : public VpiDesignRun {
 protected:
  template <typename T>
  static void PutTwo(const char* name, int format,
                     T* decltype(s_vpi_arrayvalue::value)::* arm, T first,
                     T second) {
    T values[2] = {first, second};
    PLI_INT32 index = 0;
    s_vpi_arrayvalue av = {};
    av.format = format;
    av.value.*arm = values;
    vpi_put_value_array(By(name), &av, &index, 2);
  }

  static s_vpi_value Element(const char* name, int index, int format) {
    s_vpi_value value = {};
    value.format = format;
    vpi_get_value(vpi_handle_by_index(By(name), index), &value);
    return value;
  }
};

TEST_F(ElementPutsOfARun, ARealElementHoldsTheValuePut) {
  Run("module top; real r[2]; shortreal s[2]; initial $noop; endmodule\n");
  using Arms = decltype(s_vpi_arrayvalue::value);
  PutTwo("top.r", vpiRealVal, &Arms::reals, 1.0, 2.5);
  PutTwo("top.s", vpiShortRealVal, &Arms::shortreals, 1.0f, 2.5f);
  for (const char* name : {"top.r", "top.s"}) {
    EXPECT_DOUBLE_EQ(Element(name, 0, vpiRealVal).value.real, 1.0) << name;
    EXPECT_DOUBLE_EQ(Element(name, 1, vpiRealVal).value.real, 2.5) << name;
  }
}

TEST_F(ElementPutsOfARun, ANegativeValueKeepsItsSignInAWiderElement) {
  Run("module top; int i[2]; longint l[2]; initial $noop; endmodule\n");
  using Arms = decltype(s_vpi_arrayvalue::value);
  PutTwo<PLI_INT16>("top.i", vpiShortIntVal, &Arms::shortints, -1, -2);
  PutTwo<PLI_INT32>("top.l", vpiIntVal, &Arms::integers, -1, -2);
  EXPECT_EQ(Element("top.i", 0, vpiIntVal).value.integer, -1);
  EXPECT_EQ(Element("top.i", 1, vpiIntVal).value.integer, -2);
  EXPECT_STREQ(Element("top.l", 0, vpiDecStrVal).value.str, "-1");
  EXPECT_STREQ(Element("top.l", 1, vpiDecStrVal).value.str, "-2");
}

}  // namespace
}  // namespace delta
