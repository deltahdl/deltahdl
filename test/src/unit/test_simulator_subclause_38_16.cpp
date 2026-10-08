#include <gtest/gtest.h>

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

// The vpi_get_value_array() tests read back element values that the routine
// retrieves from a static unpacked array built by the shared base fixture.
using VpiGetValueArraySim = VpiValueArraySimBase;

// §38.16: the routine retrieves values only from static unpacked arrays
// (vpiArrayType vpiStaticArray). A non-static array is rejected, an error is
// recorded, and the value arm is set to NULL.
TEST_F(VpiGetValueArraySim, NonStaticArrayIsError) {
  VpiHandle arr = MakeArray("d", {{0, 1}}, 2, 32, {vpiDynamicArray});
  SetElem(0, 7);
  SetElem(1, 8);

  PLI_INT32 sentinel[2] = {0, 0};
  s_vpi_arrayvalue av = {};
  av.format = vpiIntVal;
  av.value.integers = sentinel;  // non-NULL going in
  PLI_INT32 index[1] = {0};
  vpi_get_value_array(VpiHandleOf(arr), &av, index, 2);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
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
  vpi_get_value_array(VpiHandleOf(arr), &av, index, 5);

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
  vpi_get_value_array(VpiHandleOf(arr), &av, index, 2);

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
      MakeArray("t", {{0}}, 1, 8, {vpiStaticArray, /*four_state=*/false});
  SetElem(0, 0xF0, 0xFF);  // a stray bval in storage

  s_vpi_arrayvalue av = {};
  av.format = vpiRawFourStateVal;
  PLI_INT32 index[1] = {0};
  vpi_get_value_array(VpiHandleOf(arr), &av, index, 1);

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
  vpi_get_value_array(VpiHandleOf(arr), &av, index, 2);

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
  vpi_get_value_array(VpiHandleOf(arr), &av, index, 1);

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
  vpi_get_value_array(VpiHandleOf(arr), &av, index, 2);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
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
  vpi_get_value_array(VpiHandleOf(arr), &av, index, 2);

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
  vpi_get_value_array(VpiHandleOf(arr), &av, index, 1);

  ASSERT_NE(av.value.vectors, nullptr);
  EXPECT_EQ(av.value.vectors[0].aval, 0xABCDu);
  EXPECT_EQ(av.value.vectors[0].bval, 0x00F0u);
}

// §38.16: the vpiLongIntVal format returns one 64-bit long per element through
// the *longints arm, retrieving the full width of an element wider than 32
// bits.
TEST_F(VpiGetValueArraySim, LongIntValReturnsSixtyFourBitElements) {
  VpiHandle arr = MakeArray("li", {{0}}, 1, 64);
  arr->children[0]->type = vpiLongIntVar;  // a kind §38.16 names for the format
  SetElem(0, 0x1122334455667788ull);

  s_vpi_arrayvalue av = {};
  av.format = vpiLongIntVal;
  PLI_INT32 index[1] = {0};
  vpi_get_value_array(VpiHandleOf(arr), &av, index, 1);

  ASSERT_NE(av.value.longints, nullptr);
  EXPECT_EQ(av.value.longints[0], 0x1122334455667788ll);
}

// §38.16: the vpiShortIntVal format returns one short (16-bit) per element
// through the *shortints arm.
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

// §38.16: the vpiShortRealVal format returns one float per element through the
// *shortreals arm; the element value is delivered as its floating-point form.
TEST_F(VpiGetValueArraySim, ShortRealValReturnsFloatsPerElement) {
  VpiHandle arr = MakeArray("sr", {{0, 1}}, 2, 32);
  for (auto* elem : arr->children) elem->type = vpiShortRealVar;
  SetElem(0, 42);
  SetElem(1, 7);

  s_vpi_arrayvalue av = {};
  av.format = vpiShortRealVal;
  PLI_INT32 index[1] = {0};
  vpi_get_value_array(VpiHandleOf(arr), &av, index, 2);

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
  vpi_get_value_array(VpiHandleOf(arr), &av, index, 2);

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
  vpi_get_value_array(VpiHandleOf(arr), &av, /*index_p=*/nullptr, 2);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
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
  vpi_get_value_array(VpiHandleOf(arr), &av, index, 2);

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
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
  vpi_get_value_array(VpiHandleOf(arr), &av, index, 1);

  ASSERT_NE(av.value.times, nullptr);
  EXPECT_EQ(av.value.times[0].high, 2u);
  EXPECT_EQ(av.value.times[0].low, 5u);
}

// §38.16: asking for a format that does not fit the elements' data type is an
// error, save where the clause allows it. The clause says what each of these
// three suits - vpiShortIntVal arrays of vpiShortIntVar or vpiByteVar elements
// alone, vpiLongIntVal those or vpiLongIntVar, vpiShortRealVal arrays of
// vpiShortRealVar elements alone - so an array of regs asked for any of them is
// the inconsistent request, and the routine reports the error and nulls the
// value arm rather than answering with shorts, longs or floats it invented.
TEST_F(VpiGetValueArraySim, AFormatTheElementTypeDoesNotSupportIsAnError) {
  for (int format : {vpiShortIntVal, vpiLongIntVal, vpiShortRealVal}) {
    VpiHandle arr = MakeArray("w", {{0, 1}}, 2, 32);  // elements are regs
    SetElem(0, 1);
    SetElem(1, 2);

    PLI_INT32 sentinel[2] = {0, 0};
    s_vpi_arrayvalue av = {};
    av.format = static_cast<PLI_UINT32>(format);
    av.value.integers = sentinel;  // non-NULL going in
    PLI_INT32 index[1] = {0};
    vpi_get_value_array(VpiHandleOf(arr), &av, index, 2);

    s_vpi_error_info info = {};
    EXPECT_EQ(vpi_chk_error(&info), vpiError) << "format " << format;
    EXPECT_EQ(av.value.integers, nullptr) << "format " << format;
  }
}

// §38.16's allowed exceptions: the raw and vector formats are drawn for 4-state
// arrays and may be asked of a 2-state array as well, and vpiRawTwoStateVal may
// be asked of a 4-state array. So none of them is inconsistent with any element
// data type, and a request for one is answered rather than refused whatever the
// elements are.
TEST_F(VpiGetValueArraySim, TheRawAndVectorFormatsSuitEveryElementType) {
  for (int format : {vpiRawFourStateVal, vpiRawTwoStateVal, vpiVectorVal}) {
    VpiHandle arr = MakeArray("a", {{0}}, 1, 8);  // elements are regs
    arr->children[0]->type = vpiShortRealVar;     // and a kind of their own
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

// §38.16 with §38.2: with a null array handle there is nothing to read, and
// with a null value structure nowhere to read into, so the routine returns
// without recording an error or touching the value arm it was given.
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

// §38.16: the routine reads unpacked arrays alone, so a handle to a reg, which
// is no array, is refused, the error recorded and the value arm nulled.
TEST_F(VpiGetValueArraySim, AHandleToNoArrayIsError) {
  VpiHandle arr = MakeArray("na", {{0}}, 1, 32);
  arr->type = vpiReg;  // present the object as a reg rather than an array
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

// §38.16: index_p gives one starting index per unpacked dimension, so an array
// that records no dimension has no element a coordinate could name.
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

// §38.16: the section is read element by element from the start, and a
// position with nothing to read reads 0: an element holding no storage, and a
// position past the array's last element, where the section runs off its end.
// The element between them is read all the same, and gives the section its
// width.
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

// §38.16: a section none of whose positions holds storage has no element to
// take a width from, and reads 0 throughout.
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

// §38.16: the vpiVectorVal format reports a 2-state element as known, its bval
// bits 0 whatever its storage's bval word holds.
TEST_F(VpiGetValueArraySim, VectorValOfATwoStateArrayReportsKnownBits) {
  VpiHandle arr =
      MakeArray("v2", {{0}}, 1, 16, {vpiStaticArray, /*four_state=*/false});
  SetElem(0, 0x1234, 0x00FF);
  s_vpi_arrayvalue av = {};
  av.format = vpiVectorVal;
  PLI_INT32 index[1] = {0};
  vpi_get_value_array(VpiHandleOf(arr), &av, index, 1);

  ASSERT_NE(av.value.vectors, nullptr);
  EXPECT_EQ(av.value.vectors[0].aval, 0x1234u);
  EXPECT_EQ(av.value.vectors[0].bval, 0u);
}

// §38.16 names the element kinds the narrow integer formats suit: shorts for
// vpiShortIntVar and vpiByteVar elements, longs for those and vpiLongIntVar.
// Each pairing below is one it allows, so each is answered without error.
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

// §38.16: in the raw formats an element occupies ngroups = (elemBits + 7)/8
// bytes per group, so a 72-bit element takes nine, the ninth holding bits 64
// to 71 from the element's second storage word. Only the first word was read
// and the bytes past the eighth written as 0.
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

// §38.16 takes vpiVectorVal over from vpi_get_value() (§38.15), whose
// s_vpi_vecval repeats as often as the value needs: a 40-bit element is two
// vecvals, so element 1 starts at vectors[2]. One vecval was written per
// element, element 1 into vectors[1], where element 0's upper bits belong.
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

// What the case's calltf read out of `top.arr` with vpi_get_value_array.
std::vector<PLI_INT32>& ArrayRead() {
  static std::vector<PLI_INT32> read;
  return read;
}

PLI_INT32 ReadThenWriteArray(PLI_BYTE8* /*user_data*/) {
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

// §38.16 and §38.35: vpi_get_value_array reads the elements of a run's
// static unpacked array into the application's buffer, and
// vpi_put_value_array writes them, the design then reading what was written
// (#5133).
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

// What the case's calltf read out of `top.m` with vpi_get_value_array.
std::vector<PLI_INT32>& MatrixRead() {
  static std::vector<PLI_INT32> read;
  return read;
}

PLI_INT32 ReadMatrix(PLI_BYTE8* /*user_data*/) {
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

// §38.16 with §37.17 detail 26: a run's two-dimensional array is made of
// subarrays, each holding its own elements and the indices that select it, and
// an array declared with a typedef holds that typespec too. The read takes the
// elements in fastest-varying order across the subarrays, m[0][1] to m[1][1],
// and passes over every member that is no element.
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

// Whether the case's calltf found its read of `top.s` refused.
bool& StringArrayRefused() {
  static bool refused = false;
  return refused;
}

PLI_INT32 ReadStringArray(PLI_BYTE8* /*user_data*/) {
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

// §38.16: the arrays the routine reads hold no dynamic element, a string
// variable being the standard's example, so a run's array of strings, a fixed
// unpacked array all the same, is refused with the value arm nulled. Its
// elements' text was read out as integers.
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

}  // namespace
}  // namespace delta
