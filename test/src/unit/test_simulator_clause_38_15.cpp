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
  var->value = MakeLogic4VecVal(arena_, 1, 1);
  var->value.words[0].bval = 1;  // a=1,b=1 -> x
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
  var->value = MakeLogic4VecVal(arena_, 1, 0);
  var->value.words[0].bval = 1;  // a=0,b=1 -> z
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
// 1, 0, x, and z. Bit 2 is x (a=1,b=1) and bit 1 is z (a=0,b=1).
TEST_F(VpiGetValueSim, GetValueBinStrFormatUnknownBits) {
  auto* var = sim_ctx_.CreateVariable("bxz", 4);
  var->value = MakeLogic4VecVal(arena_, 4, 0b1100);
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

// §38.15, Table 38-3 (hex row): a nibble whose bits are all z prints lowercase
// 'z'; a nibble with only some z bits prints uppercase 'Z'. High nibble is all
// z (a=0,b=F) -> 'z'; low nibble has one z bit among three 0 bits -> 'Z'.
TEST_F(VpiGetValueSim, GetValueHexStrFormatUnknownBits) {
  auto* var = sim_ctx_.CreateVariable("hxz", 8);
  var->value = MakeLogic4VecVal(arena_, 8, 0x00);
  var->value.words[0].bval = 0xF1;
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("hxz", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiHexStrVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.str, nullptr);
  EXPECT_STREQ(val.value.str, "zZ");
}

// §38.15, Table 38-3 (hex row): a nibble with some x bits prints uppercase 'X';
// a nibble whose bits are all x prints lowercase 'x'. Low nibble is all x
// (a=F,b=F) -> 'x'; a single x bit in the other nibble would be 'X' (below).
TEST_F(VpiGetValueSim, GetValueHexStrFormatAllXLowercase) {
  auto* var = sim_ctx_.CreateVariable("hax", 8);
  var->value = MakeLogic4VecVal(arena_, 8, 0x0F);
  var->value.words[0].bval = 0x0F;  // low nibble a=F,b=F -> all x
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("hax", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiHexStrVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.str, nullptr);
  EXPECT_STREQ(val.value.str, "0x");
}

// §38.15, Table 38-3 (hex row): a nibble with only some x bits prints uppercase
// 'X'. Low nibble has one x bit (a=1,b=1) among three 0 bits.
TEST_F(VpiGetValueSim, GetValueHexStrFormatSomeXUppercase) {
  auto* var = sim_ctx_.CreateVariable("hsx", 8);
  var->value = MakeLogic4VecVal(arena_, 8, 0x01);
  var->value.words[0].bval = 0x01;  // low nibble {0,0,0,x} -> some x
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("hsx", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiHexStrVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.str, nullptr);
  EXPECT_STREQ(val.value.str, "0X");
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
  var->value = MakeLogic4VecVal(arena_, 6, 0b111000);
  var->value.words[0].bval = 0b000111;  // low octal digit is all z (a=0,b=1)
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("ocz", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiOctStrVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.str, nullptr);
  EXPECT_STREQ(val.value.str, "7z");
}

// §38.15, Table 38-3 (octal row): a digit with only some z bits (not a whole-
// group z) is reported as uppercase 'Z'. Bit 0 alone is z (a=0,b=1); the other
// two bits of the group are 0, so the group is not all-z.
TEST_F(VpiGetValueSim, GetValueOctStrFormatSomeZReportsUppercaseZ) {
  auto* var = sim_ctx_.CreateVariable("ocz2", 6);
  var->value = MakeLogic4VecVal(arena_, 6, 0);
  var->value.words[0].bval = 0b000001;
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("ocz2", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiOctStrVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.str, nullptr);
  EXPECT_STREQ(val.value.str, "0Z");
}

// §38.15, Table 38-3 (octal row): a digit whose bits are all x prints lowercase
// 'x'. The low group is driven all x (a=7,b=7).
TEST_F(VpiGetValueSim, GetValueOctStrFormatAllXReportsLowercaseX) {
  auto* var = sim_ctx_.CreateVariable("ocax", 6);
  var->value = MakeLogic4VecVal(arena_, 6, 0b000111);
  var->value.words[0].bval = 0b000111;  // low digit a=7,b=7 -> all x
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("ocax", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiOctStrVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.str, nullptr);
  EXPECT_STREQ(val.value.str, "0x");
}

// §38.15, Table 38-3 (octal row): a digit with only some x bits prints
// uppercase 'X'. The low group has one x bit (a=1,b=1) among two 0 bits.
TEST_F(VpiGetValueSim, GetValueOctStrFormatSomeXReportsUppercaseX) {
  auto* var = sim_ctx_.CreateVariable("ocsx", 6);
  var->value = MakeLogic4VecVal(arena_, 6, 0b000001);
  var->value.words[0].bval = 0b000001;  // low digit {0,0,x} -> some x
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("ocsx", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiOctStrVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.str, nullptr);
  EXPECT_STREQ(val.value.str, "0X");
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

// §38.15, Table 38-3 (vpiVectorVal row) / Figure 38-8: unknown bits use the ab
// encoding 11=X, 01=Z, which now matches the internal four-state word, so the
// returned value is a direct copy. A z bit is internal a=0,b=1.
TEST_F(VpiGetValueSim, GetValueVectorFormatEncodesUnknownBits) {
  auto* var = sim_ctx_.CreateVariable("vz", 4);
  var->value = MakeLogic4VecVal(arena_, 4, 0b1011);
  var->value.words[0].bval = 0b0100;  // bit 2 is z (a=0,b=1)
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

// §38.15, Table 38-3 (vpiVectorVal row) / Figure 38-8: the other unknown
// encoding is 11=X. An x bit is internal a=1,b=1, so both the aval and bval
// bits are set in the returned vecval -- distinct from the z case above where
// aval is clear.
TEST_F(VpiGetValueSim, GetValueVectorFormatEncodesXBit) {
  auto* var = sim_ctx_.CreateVariable("vx", 4);
  var->value = MakeLogic4VecVal(arena_, 4, 0b1111);
  var->value.words[0].bval = 0b0100;  // bit 2 is x (a=1,b=1)
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("vx", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiVectorVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.vector, nullptr);
  // ab encoding: bit 2 x -> both aval and bval bits set.
  EXPECT_EQ(val.value.vector[0].aval, 0b1111u);
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

// §38.15, Table 38-3 (vpiStrengthVal row): the per-bit logic value carries the
// bit's four-state value, so an x bit reports vpiX and a z bit reports vpiZ,
// while the drive components stay strong on a variable. Bits from LSB up are
// 1, 0, x (a=1,b=1), z (a=0,b=1).
TEST_F(VpiGetValueSim, GetValueStrengthFormatUnknownBits) {
  auto* var = sim_ctx_.CreateVariable("stu", 4);
  var->value = MakeLogic4VecVal(arena_, 4, 0b0101);
  var->value.words[0].bval = 0b1100;  // bit 2 x, bit 3 z
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("stu", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiStrengthVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.strength, nullptr);
  EXPECT_EQ(val.value.strength[0].logic, vpi1);
  EXPECT_EQ(val.value.strength[1].logic, vpi0);
  EXPECT_EQ(val.value.strength[2].logic, vpiX);
  EXPECT_EQ(val.value.strength[3].logic, vpiZ);
  EXPECT_EQ(val.value.strength[2].s0, vpiStrongDrive);
  EXPECT_EQ(val.value.strength[2].s1, vpiStrongDrive);
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

// Builds a real object the way the runtime stores one: the IEEE-754 bit
// pattern of `d` laid into a 64-bit four-state word with is_real set. Mirrors
// eval_expr.cpp's real construction so the VPI read observes a genuine double.
static void SetRealValue(Variable* var, Arena& arena, double d) {
  uint64_t bits = 0;
  std::memcpy(&bits, &d, sizeof(double));
  var->value = MakeLogic4VecVal(arena, 64, bits);
  var->value.is_real = true;
}

// §38.15: with vpiObjTypeVal a real object reports vpiRealVal; the routine
// fills the real arm and rewrites the format field accordingly.
TEST_F(VpiGetValueSim, GetValueObjTypeRealObject) {
  auto* var = sim_ctx_.CreateVariable("otr", 64);
  SetRealValue(var, arena_, 42.0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("otr", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiObjTypeVal;
  vpi_get_value(h, &val);
  EXPECT_EQ(val.format, vpiRealVal);
  EXPECT_DOUBLE_EQ(val.value.real, 42.0);
}

// §38.15, Table 38-3 (vpiRealVal row): a real object read in vpiRealVal format
// yields the stored floating-point value, not its bit pattern reinterpreted as
// an integer. 3.5 must come back as exactly 3.5.
TEST_F(VpiGetValueSim, GetValueRealObjectRealFormat) {
  auto* var = sim_ctx_.CreateVariable("rr", 64);
  SetRealValue(var, arena_, 3.5);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("rr", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiRealVal;
  vpi_get_value(h, &val);
  EXPECT_DOUBLE_EQ(val.value.real, 3.5);
}

// §38.15: a real object returned in a format other than vpiRealVal/vpiStringVal
// is first converted to an integer using the §6.12.1 rounding (nearest, ties
// away from zero). 2.5 rounds to 3, distinguishing it from round-half-to-even
// (which would give 2) and from a raw bit-pattern truncation (garbage).
TEST_F(VpiGetValueSim, GetValueRealObjectIntFormatRoundsHalfAwayFromZero) {
  auto* var = sim_ctx_.CreateVariable("ri", 64);
  SetRealValue(var, arena_, 2.5);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("ri", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiIntVal;
  vpi_get_value(h, &val);
  EXPECT_EQ(val.value.integer, 3);
}

// §38.15: the same §6.12.1 rounding applies to negative reals, rounding away
// from zero. -2.5 rounds to -3.
TEST_F(VpiGetValueSim, GetValueRealObjectIntFormatNegativeRounding) {
  auto* var = sim_ctx_.CreateVariable("rin", 64);
  SetRealValue(var, arena_, -2.5);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("rin", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiIntVal;
  vpi_get_value(h, &val);
  EXPECT_EQ(val.value.integer, -3);
}

// §38.15: when the requested format is vpiStringVal, a real object is returned
// as a decimal-notation string of the floating-point number (not an ASCII
// repacking of its bits). 3.5 renders as the text "3.5".
TEST_F(VpiGetValueSim, GetValueRealObjectStringFormat) {
  auto* var = sim_ctx_.CreateVariable("rs", 64);
  SetRealValue(var, arena_, 3.5);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("rs", nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiStringVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.str, nullptr);
  EXPECT_STREQ(val.value.str, "3.5");
}

// §38.15: the buffer vpi_get_value() uses for string values shall be different
// from the buffer vpi_get_str() uses. So a pointer returned by vpi_get_str()
// must survive a following vpi_get_value() call in a string format -- the value
// string lands in a separate buffer and does not clobber the earlier name.
TEST_F(VpiGetValueSim, GetValueStringBufferDistinctFromGetStr) {
  auto* var = sim_ctx_.CreateVariable("nm", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 0x00004142);  // packs to "AB"
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name("nm", nullptr);
  ASSERT_NE(h, nullptr);

  // Hold the pointer returned by vpi_get_str(vpiName, ...).
  const char* name = vpi_get_str(vpiName, h);
  ASSERT_NE(name, nullptr);
  EXPECT_STREQ(name, "nm");

  // Retrieving a string value must not overwrite the vpi_get_str() buffer.
  s_vpi_value val = {};
  val.format = vpiStringVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.str, nullptr);
  EXPECT_STREQ(val.value.str, "AB");
  EXPECT_NE(static_cast<const void*>(val.value.str),
            static_cast<const void*>(name));  // the two buffers are distinct
  EXPECT_STREQ(name, "nm");                   // the name buffer is left intact
}

}  // namespace
}  // namespace delta
