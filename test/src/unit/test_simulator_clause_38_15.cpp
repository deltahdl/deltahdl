#include <gtest/gtest.h>

#include <cstring>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

class VpiGetValueSim : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  SourceManager mgr_;
  Arena arena_;
  Scheduler scheduler_{arena_};
  DiagEngine diag_{mgr_};
  SimContext sim_ctx_{scheduler_, arena_, diag_};
  VpiContext vpi_ctx_;
};

TEST_F(VpiGetValueSim, GetValueIntFormat) {
  auto* var = sim_ctx_.CreateVariable("x", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 123);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("x", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiIntVal;
  vpi_get_value(h, &val);
  EXPECT_EQ(val.value.integer, 123);
}

TEST_F(VpiGetValueSim, GetValueRealFormat) {
  auto* var = sim_ctx_.CreateVariable("r", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 42);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("r", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiRealVal;
  vpi_get_value(h, &val);
  EXPECT_DOUBLE_EQ(val.value.real, 42.0);
}

TEST_F(VpiGetValueSim, GetValueScalarFormatZero) {
  auto* var = sim_ctx_.CreateVariable("s", 1);
  var->value = MakeLogic4VecVal(arena_, 1, 0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("s", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiScalarVal;
  vpi_get_value(h, &val);
  EXPECT_EQ(val.value.scalar, vpi0);
}

TEST_F(VpiGetValueSim, GetValueScalarFormatOne) {
  auto* var = sim_ctx_.CreateVariable("s1", 1);
  var->value = MakeLogic4VecVal(arena_, 1, 1);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("s1", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiScalarVal;
  vpi_get_value(h, &val);
  EXPECT_EQ(val.value.scalar, vpi1);
}

// §38.15, Table 38-3 (scalar row): a single unknown bit is reported as vpiX
// (a=0,b=1) or vpiZ (a=1,b=1), alongside the vpi0/vpi1 cases above.
TEST_F(VpiGetValueSim, GetValueScalarFormatX) {
  auto* var = sim_ctx_.CreateVariable("sx", 1);
  var->value = MakeLogic4VecVal(arena_, 1, 0);
  var->value.words[0].bval = 1;  // a=0,b=1 -> x
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("sx", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiScalarVal;
  vpi_get_value(h, &val);
  EXPECT_EQ(val.value.scalar, vpiX);
}

TEST_F(VpiGetValueSim, GetValueScalarFormatZ) {
  auto* var = sim_ctx_.CreateVariable("sz", 1);
  var->value = MakeLogic4VecVal(arena_, 1, 1);
  var->value.words[0].bval = 1;  // a=1,b=1 -> z
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("sz", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiScalarVal;
  vpi_get_value(h, &val);
  EXPECT_EQ(val.value.scalar, vpiZ);
}

TEST_F(VpiGetValueSim, GetValueBinStrFormat) {
  auto* var = sim_ctx_.CreateVariable("b", 4);
  var->value = MakeLogic4VecVal(arena_, 4, 0b1010);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("b", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiBinStrVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.str, nullptr);
  EXPECT_STREQ(val.value.str, "1010");
}

// §38.15, Table 38-3 (binary row): the returned string uses the characters
// 1, 0, x, and z. Bit 2 is x (a=0,b=1) and bit 1 is z (a=1,b=1).
TEST_F(VpiGetValueSim, GetValueBinStrFormatUnknownBits) {
  auto* var = sim_ctx_.CreateVariable("bxz", 4);
  var->value = MakeLogic4VecVal(arena_, 4, 0b1010);
  var->value.words[0].bval = 0b0110;
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("bxz", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiBinStrVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.str, nullptr);
  EXPECT_STREQ(val.value.str, "1xz0");
}

TEST_F(VpiGetValueSim, GetValueHexStrFormat) {
  auto* var = sim_ctx_.CreateVariable("hx", 8);
  var->value = MakeLogic4VecVal(arena_, 8, 0xAB);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("hx", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiHexStrVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.str, nullptr);
  EXPECT_STREQ(val.value.str, "ab");
}

// §38.15, Table 38-3 (hex row): a hex digit covering an unknown bit is reported
// as x, or as z when the whole nibble is z. High nibble is all z (a=F,b=F),
// low nibble carries a single unknown bit and so reports x.
TEST_F(VpiGetValueSim, GetValueHexStrFormatUnknownBits) {
  auto* var = sim_ctx_.CreateVariable("hxz", 8);
  var->value = MakeLogic4VecVal(arena_, 8, 0xF0);
  var->value.words[0].bval = 0xF1;
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("hxz", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiHexStrVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.str, nullptr);
  EXPECT_STREQ(val.value.str, "zx");
}

TEST_F(VpiGetValueSim, GetValueOctStrFormat) {
  auto* var = sim_ctx_.CreateVariable("oc", 6);
  var->value = MakeLogic4VecVal(arena_, 6, 075);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("oc", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiOctStrVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.str, nullptr);
  EXPECT_STREQ(val.value.str, "75");
}

// §38.15, Table 38-3 (octal row): a digit covering an unknown bit is reported
// as x (or z when the whole group is z) rather than as a numeric digit. The
// low group is driven all-z (a=1,b=1), so it must render as 'z'.
TEST_F(VpiGetValueSim, GetValueOctStrFormatUnknownBits) {
  auto* var = sim_ctx_.CreateVariable("ocz", 6);
  var->value = MakeLogic4VecVal(arena_, 6, 0b111111);
  var->value.words[0].bval = 0b000111;  // low octal digit is all z (a=1,b=1)
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("ocz", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiOctStrVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.str, nullptr);
  EXPECT_STREQ(val.value.str, "7z");
}

// §38.15, Table 38-3 (octal row): a digit with only some unknown bits (not a
// whole-group z) is reported as x. Bit 0 alone is unknown (a=0,b=1).
TEST_F(VpiGetValueSim, GetValueOctStrFormatPartialUnknownReportsX) {
  auto* var = sim_ctx_.CreateVariable("ocx", 6);
  var->value = MakeLogic4VecVal(arena_, 6, 0);
  var->value.words[0].bval = 0b000001;
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("ocx", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiOctStrVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.str, nullptr);
  EXPECT_STREQ(val.value.str, "0x");
}

TEST_F(VpiGetValueSim, GetValueStringFormat) {
  auto* var = sim_ctx_.CreateVariable("sv", 32);

  var->value = MakeLogic4VecVal(arena_, 32, 0x00004142);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("sv", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiStringVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.str, nullptr);
  EXPECT_STREQ(val.value.str, "AB");
}

TEST_F(VpiGetValueSim, GetValueTimeFormat) {
  auto* var = sim_ctx_.CreateVariable("t", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 500);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("t", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiTimeVal;
  vpi_get_value(h, &val);
  EXPECT_EQ(val.value.integer, 500);
}

// §38.15, Table 38-3 (vpiIntVal row): any x or z bit in the object value is
// mapped to a 0 in the returned integer. Bit 2 is driven unknown (a=1,b=1),
// so it must read back as 0: 0b1111 with bit 2 cleared is 0b1011 == 11.
TEST_F(VpiGetValueSim, GetValueIntFormatMapsUnknownBitsToZero) {
  auto* var = sim_ctx_.CreateVariable("xz", 4);
  var->value = MakeLogic4VecVal(arena_, 4, 0b1111);
  var->value.words[0].bval = 0b0100;
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("xz", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiIntVal;
  vpi_get_value(h, &val);
  EXPECT_EQ(val.value.integer, 0b1011);
}

// §38.15, Table 38-3 (vpiVectorVal row) and the vector paragraph: the value is
// returned as an array of s_vpi_vecval whose size is ((vector_size-1)/32+1),
// with the LSB carried by element 0 and bit 33 by the LSB of element 1.
TEST_F(VpiGetValueSim, GetValueVectorFormatTwoWords) {
  auto* var = sim_ctx_.CreateVariable("v", 40);
  var->value = MakeLogic4VecVal(arena_, 40, 0x123456789Aull);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("v", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiVectorVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.vector, nullptr);
  // Element 0 holds bits [31:0], element 1 holds bits [39:32].
  EXPECT_EQ(val.value.vector[0].aval, 0x3456789Au);
  EXPECT_EQ(val.value.vector[0].bval, 0u);
  EXPECT_EQ(val.value.vector[1].aval, 0x12u);
  EXPECT_EQ(val.value.vector[1].bval, 0u);
}

// §38.15 (vector paragraph): the array_size formula ((vector_size-1)/32+1)
// yields a single s_vpi_vecval at the 32-bit boundary, carrying all 32 bits in
// element 0. This pins the boundary opposite the multi-word case above.
TEST_F(VpiGetValueSim, GetValueVectorFormatSingleWordBoundary) {
  auto* var = sim_ctx_.CreateVariable("vw", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 0xDEADBEEFull);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("vw", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiVectorVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.vector, nullptr);
  EXPECT_EQ(val.value.vector[0].aval, 0xDEADBEEFu);
  EXPECT_EQ(val.value.vector[0].bval, 0u);
}

// §38.15, Table 38-3 (vpiVectorVal row): unknown bits use the ab encoding
// 11=X, 01=Z, which is not the same bit pattern as the internal four-state
// word. A z bit (internal a=1,b=1) must encode as vecval a=0,b=1.
TEST_F(VpiGetValueSim, GetValueVectorFormatEncodesUnknownBits) {
  auto* var = sim_ctx_.CreateVariable("vz", 4);
  var->value = MakeLogic4VecVal(arena_, 4, 0b1111);
  var->value.words[0].bval = 0b0100;  // bit 2 is z (a=1,b=1)
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("vz", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiVectorVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.vector, nullptr);
  // ab encoding: bit 2 z -> aval bit cleared, bval bit set.
  EXPECT_EQ(val.value.vector[0].aval, 0b1011u);
  EXPECT_EQ(val.value.vector[0].bval, 0b0100u);
}

// §38.15, Table 38-3 (vpiStrengthVal row) and the strength paragraph: the value
// is returned as one s_vpi_strengthval per bit, and a reg or variable always
// reports strong strength on both drive components.
TEST_F(VpiGetValueSim, GetValueStrengthFormat) {
  auto* var = sim_ctx_.CreateVariable("st", 4);
  var->value = MakeLogic4VecVal(arena_, 4, 0b1010);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("st", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiStrengthVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.strength, nullptr);
  // Element i carries the strength of bit i: bits are 0,1,0,1 from LSB up.
  EXPECT_EQ(val.value.strength[0].logic, vpi0);
  EXPECT_EQ(val.value.strength[1].logic, vpi1);
  EXPECT_EQ(val.value.strength[2].logic, vpi0);
  EXPECT_EQ(val.value.strength[3].logic, vpi1);
  EXPECT_EQ(val.value.strength[0].s0, vpiStrongDrive);
  EXPECT_EQ(val.value.strength[0].s1, vpiStrongDrive);
}

// §38.15: with vpiObjTypeVal the routine fills the value and rewrites the
// format field according to the object type. A multi-bit reg is a vector, so
// the format becomes vpiVectorVal and the vector arm is populated.
TEST_F(VpiGetValueSim, GetValueObjTypeVectorObject) {
  auto* var = sim_ctx_.CreateVariable("ot", 8);
  var->value = MakeLogic4VecVal(arena_, 8, 0xAB);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("ot", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiObjTypeVal;
  vpi_get_value(h, &val);
  EXPECT_EQ(val.format, vpiVectorVal);
  ASSERT_NE(val.value.vector, nullptr);
  EXPECT_EQ(val.value.vector[0].aval, 0xABu);
}

// §38.15: with vpiObjTypeVal a single-bit object is a scalar, so the format
// becomes vpiScalarVal and the scalar arm carries the bit value.
TEST_F(VpiGetValueSim, GetValueObjTypeScalarObject) {
  auto* var = sim_ctx_.CreateVariable("ot1", 1);
  var->value = MakeLogic4VecVal(arena_, 1, 1);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("ot1", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiObjTypeVal;
  vpi_get_value(h, &val);
  EXPECT_EQ(val.format, vpiScalarVal);
  EXPECT_EQ(val.value.scalar, vpi1);
}

// §38.15: with vpiObjTypeVal a real object reports vpiRealVal; the routine
// fills the real arm and rewrites the format field accordingly.
TEST_F(VpiGetValueSim, GetValueObjTypeRealObject) {
  auto* var = sim_ctx_.CreateVariable("otr", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 42);
  var->value.is_real = true;
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("otr", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiObjTypeVal;
  vpi_get_value(h, &val);
  EXPECT_EQ(val.format, vpiRealVal);
  EXPECT_DOUBLE_EQ(val.value.real, 42.0);
}

}  // namespace
}  // namespace delta
