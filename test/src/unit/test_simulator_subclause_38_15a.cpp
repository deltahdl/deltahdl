#include <gtest/gtest.h>

#include <cstdint>
#include <cstring>
#include <string>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/packed_range.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "fixture_vpi_run.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

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

  vpiHandle h = vpi_handle_by_name(VpiText("x"), nullptr);
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

  vpiHandle h = vpi_handle_by_name(VpiText("r"), nullptr);
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

  vpiHandle h = vpi_handle_by_name(VpiText("s"), nullptr);
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

  vpiHandle h = vpi_handle_by_name(VpiText("s1"), nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiScalarVal;
  vpi_get_value(h, &val);
  EXPECT_EQ(val.value.scalar, vpi1);
}

TEST_F(VpiGetValueSim, GetValueScalarFormatX) {
  auto* var = sim_ctx_.CreateVariable("sx", 1);
  var->value = MakeLogic4VecVal(arena_, 1, 1);
  var->value.words[0].bval = 1;
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name(VpiText("sx"), nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiScalarVal;
  vpi_get_value(h, &val);
  EXPECT_EQ(val.value.scalar, vpiX);
}

TEST_F(VpiGetValueSim, GetValueScalarFormatZ) {
  auto* var = sim_ctx_.CreateVariable("sz", 1);
  var->value = MakeLogic4VecVal(arena_, 1, 0);
  var->value.words[0].bval = 1;
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name(VpiText("sz"), nullptr);
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

  vpiHandle h = vpi_handle_by_name(VpiText("b"), nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiBinStrVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.str, nullptr);
  EXPECT_STREQ(val.value.str, "1010");
}

TEST_F(VpiGetValueSim, GetValueBinStrFormatUnknownBits) {
  auto* var = sim_ctx_.CreateVariable("bxz", 4);
  var->value = MakeLogic4VecVal(arena_, 4, 0b1100);
  var->value.words[0].bval = 0b0110;
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name(VpiText("bxz"), nullptr);
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

  vpiHandle h = vpi_handle_by_name(VpiText("hx"), nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiHexStrVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.str, nullptr);
  EXPECT_STREQ(val.value.str, "ab");
}

TEST_F(VpiGetValueSim, GetValueHexStrFormatUnknownBits) {
  auto* var = sim_ctx_.CreateVariable("hxz", 8);
  var->value = MakeLogic4VecVal(arena_, 8, 0x00);
  var->value.words[0].bval = 0xF1;
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name(VpiText("hxz"), nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiHexStrVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.str, nullptr);
  EXPECT_STREQ(val.value.str, "zZ");
}

TEST_F(VpiGetValueSim, GetValueHexStrFormatAllXLowercase) {
  auto* var = sim_ctx_.CreateVariable("hax", 8);
  var->value = MakeLogic4VecVal(arena_, 8, 0x0F);
  var->value.words[0].bval = 0x0F;
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name(VpiText("hax"), nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiHexStrVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.str, nullptr);
  EXPECT_STREQ(val.value.str, "0x");
}

TEST_F(VpiGetValueSim, GetValueHexStrFormatSomeXUppercase) {
  auto* var = sim_ctx_.CreateVariable("hsx", 8);
  var->value = MakeLogic4VecVal(arena_, 8, 0x01);
  var->value.words[0].bval = 0x01;
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name(VpiText("hsx"), nullptr);
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

  vpiHandle h = vpi_handle_by_name(VpiText("oc"), nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiOctStrVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.str, nullptr);
  EXPECT_STREQ(val.value.str, "75");
}

TEST_F(VpiGetValueSim, GetValueOctStrFormatUnknownBits) {
  auto* var = sim_ctx_.CreateVariable("ocz", 6);
  var->value = MakeLogic4VecVal(arena_, 6, 0b111000);
  var->value.words[0].bval = 0b000111;
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name(VpiText("ocz"), nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiOctStrVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.str, nullptr);
  EXPECT_STREQ(val.value.str, "7z");
}

TEST_F(VpiGetValueSim, GetValueOctStrFormatSomeZReportsUppercaseZ) {
  auto* var = sim_ctx_.CreateVariable("ocz2", 6);
  var->value = MakeLogic4VecVal(arena_, 6, 0);
  var->value.words[0].bval = 0b000001;
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name(VpiText("ocz2"), nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiOctStrVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.str, nullptr);
  EXPECT_STREQ(val.value.str, "0Z");
}

TEST_F(VpiGetValueSim, GetValueOctStrFormatAllXReportsLowercaseX) {
  auto* var = sim_ctx_.CreateVariable("ocax", 6);
  var->value = MakeLogic4VecVal(arena_, 6, 0b000111);
  var->value.words[0].bval = 0b000111;
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name(VpiText("ocax"), nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiOctStrVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.str, nullptr);
  EXPECT_STREQ(val.value.str, "0x");
}

TEST_F(VpiGetValueSim, GetValueOctStrFormatSomeXReportsUppercaseX) {
  auto* var = sim_ctx_.CreateVariable("ocsx", 6);
  var->value = MakeLogic4VecVal(arena_, 6, 0b000001);
  var->value.words[0].bval = 0b000001;
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name(VpiText("ocsx"), nullptr);
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

  vpiHandle h = vpi_handle_by_name(VpiText("sv"), nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiStringVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.str, nullptr);
  EXPECT_STREQ(val.value.str, "AB");
}

TEST_F(VpiGetValueSim, GetValueTimeFormat) {
  auto* var = sim_ctx_.CreateVariable("t", 64);
  var->value = MakeLogic4VecVal(arena_, 64, (uint64_t{3} << 32) | 500);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name(VpiText("t"), nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiTimeVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.time, nullptr);
  EXPECT_EQ(val.value.time->type, vpiSimTime);
  EXPECT_EQ(val.value.time->high, 3u);
  EXPECT_EQ(val.value.time->low, 500u);
}

TEST_F(VpiGetValueSim, GetValueDecStrFormatHonoursSignedness) {
  auto* sv = sim_ctx_.CreateVariable("sv", 8);
  sv->value = MakeLogic4VecVal(arena_, 8, 0xFB);
  sv->is_signed = true;
  sv->value.is_signed = true;
  auto* uv = sim_ctx_.CreateVariable("uv", 8);
  uv->value = MakeLogic4VecVal(arena_, 8, 0xFB);
  vpi_ctx_.Attach(sim_ctx_);

  s_vpi_value val = {};
  val.format = vpiDecStrVal;
  vpi_get_value(vpi_handle_by_name(VpiText("sv"), nullptr), &val);
  ASSERT_NE(val.value.str, nullptr);
  EXPECT_STREQ(val.value.str, "-5");
  val = {};
  val.format = vpiDecStrVal;
  vpi_get_value(vpi_handle_by_name(VpiText("uv"), nullptr), &val);
  ASSERT_NE(val.value.str, nullptr);
  EXPECT_STREQ(val.value.str, "251");
}

TEST_F(VpiGetValueSim, GetValueIntFormatMapsUnknownBitsToZero) {
  auto* var = sim_ctx_.CreateVariable("xz", 4);
  var->value = MakeLogic4VecVal(arena_, 4, 0b1111);
  var->value.words[0].bval = 0b0100;
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name(VpiText("xz"), nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiIntVal;
  vpi_get_value(h, &val);
  EXPECT_EQ(val.value.integer, 0b1011);
}

TEST_F(VpiGetValueSim, GetValueVectorFormatTwoWords) {
  auto* var = sim_ctx_.CreateVariable("v", 40);
  var->value = MakeLogic4VecVal(arena_, 40, 0x123456789Aull);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name(VpiText("v"), nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiVectorVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.vector, nullptr);
  EXPECT_EQ(val.value.vector[0].aval, 0x3456789Au);
  EXPECT_EQ(val.value.vector[0].bval, 0u);
  EXPECT_EQ(val.value.vector[1].aval, 0x12u);
  EXPECT_EQ(val.value.vector[1].bval, 0u);
}

TEST_F(VpiGetValueSim, GetValueVectorFormatSingleWordBoundary) {
  auto* var = sim_ctx_.CreateVariable("vw", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 0xDEADBEEFull);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name(VpiText("vw"), nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiVectorVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.vector, nullptr);
  EXPECT_EQ(val.value.vector[0].aval, 0xDEADBEEFu);
  EXPECT_EQ(val.value.vector[0].bval, 0u);
}

TEST_F(VpiGetValueSim, GetValueVectorFormatEncodesUnknownBits) {
  auto* var = sim_ctx_.CreateVariable("vz", 4);
  var->value = MakeLogic4VecVal(arena_, 4, 0b1011);
  var->value.words[0].bval = 0b0100;
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name(VpiText("vz"), nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiVectorVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.vector, nullptr);
  EXPECT_EQ(val.value.vector[0].aval, 0b1011u);
  EXPECT_EQ(val.value.vector[0].bval, 0b0100u);
}

TEST_F(VpiGetValueSim, GetValueVectorFormatEncodesXBit) {
  auto* var = sim_ctx_.CreateVariable("vx", 4);
  var->value = MakeLogic4VecVal(arena_, 4, 0b1111);
  var->value.words[0].bval = 0b0100;
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name(VpiText("vx"), nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiVectorVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.vector, nullptr);
  EXPECT_EQ(val.value.vector[0].aval, 0b1111u);
  EXPECT_EQ(val.value.vector[0].bval, 0b0100u);
}

TEST_F(VpiGetValueSim, GetValueStrengthFormat) {
  auto* var = sim_ctx_.CreateVariable("st", 4);
  var->value = MakeLogic4VecVal(arena_, 4, 0b1010);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name(VpiText("st"), nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiStrengthVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.strength, nullptr);
  EXPECT_EQ(val.value.strength[0].logic, vpi0);
  EXPECT_EQ(val.value.strength[1].logic, vpi1);
  EXPECT_EQ(val.value.strength[2].logic, vpi0);
  EXPECT_EQ(val.value.strength[3].logic, vpi1);
  EXPECT_EQ(val.value.strength[0].s0, vpiStrongDrive);
  EXPECT_EQ(val.value.strength[0].s1, vpiStrongDrive);
}

TEST_F(VpiGetValueSim, GetValueStrengthFormatUnknownBits) {
  auto* var = sim_ctx_.CreateVariable("stu", 4);
  var->value = MakeLogic4VecVal(arena_, 4, 0b0101);
  var->value.words[0].bval = 0b1100;
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name(VpiText("stu"), nullptr);
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

TEST_F(VpiGetValueSim, GetValueObjTypeVectorObject) {
  auto* var = sim_ctx_.CreateVariable("ot", 8);
  var->value = MakeLogic4VecVal(arena_, 8, 0xAB);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name(VpiText("ot"), nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiObjTypeVal;
  vpi_get_value(h, &val);
  EXPECT_EQ(val.format, vpiVectorVal);
  ASSERT_NE(val.value.vector, nullptr);
  EXPECT_EQ(val.value.vector[0].aval, 0xABu);
}

TEST_F(VpiGetValueSim, GetValueObjTypeScalarObject) {
  auto* var = sim_ctx_.CreateVariable("ot1", 1);
  var->value = MakeLogic4VecVal(arena_, 1, 1);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name(VpiText("ot1"), nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiObjTypeVal;
  vpi_get_value(h, &val);
  EXPECT_EQ(val.format, vpiScalarVal);
  EXPECT_EQ(val.value.scalar, vpi1);
}

static void SetRealValue(Variable* var, Arena& arena, double d) {
  uint64_t bits = 0;
  std::memcpy(&bits, &d, sizeof(double));
  var->value = MakeLogic4VecVal(arena, 64, bits);
  var->value.is_real = true;
}

TEST_F(VpiGetValueSim, GetValueObjTypeRealObject) {
  auto* var = sim_ctx_.CreateVariable("otr", 64);
  SetRealValue(var, arena_, 42.0);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name(VpiText("otr"), nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiObjTypeVal;
  vpi_get_value(h, &val);
  EXPECT_EQ(val.format, vpiRealVal);
  EXPECT_DOUBLE_EQ(val.value.real, 42.0);
}

TEST_F(VpiGetValueSim, GetValueRealObjectRealFormat) {
  auto* var = sim_ctx_.CreateVariable("rr", 64);
  SetRealValue(var, arena_, 3.5);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name(VpiText("rr"), nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiRealVal;
  vpi_get_value(h, &val);
  EXPECT_DOUBLE_EQ(val.value.real, 3.5);
}

TEST_F(VpiGetValueSim, GetValueRealObjectIntFormatRoundsHalfAwayFromZero) {
  auto* var = sim_ctx_.CreateVariable("ri", 64);
  SetRealValue(var, arena_, 2.5);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name(VpiText("ri"), nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiIntVal;
  vpi_get_value(h, &val);
  EXPECT_EQ(val.value.integer, 3);
}

TEST_F(VpiGetValueSim, GetValueRealObjectIntFormatNegativeRounding) {
  auto* var = sim_ctx_.CreateVariable("rin", 64);
  SetRealValue(var, arena_, -2.5);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name(VpiText("rin"), nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiIntVal;
  vpi_get_value(h, &val);
  EXPECT_EQ(val.value.integer, -3);
}

TEST_F(VpiGetValueSim, GetValueRealObjectStringFormat) {
  auto* var = sim_ctx_.CreateVariable("rs", 64);
  SetRealValue(var, arena_, 3.5);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name(VpiText("rs"), nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiStringVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.str, nullptr);
  EXPECT_STREQ(val.value.str, "3.5");
}

TEST_F(VpiGetValueSim, GetValueStringBufferDistinctFromGetStr) {
  auto* var = sim_ctx_.CreateVariable("nm", 32);
  var->value = MakeLogic4VecVal(arena_, 32, 0x00004142);
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name(VpiText("nm"), nullptr);
  ASSERT_NE(h, nullptr);

  const char* name = vpi_get_str(vpiName, h);
  ASSERT_NE(name, nullptr);
  EXPECT_STREQ(name, "nm");

  s_vpi_value val = {};
  val.format = vpiStringVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.str, nullptr);
  EXPECT_STREQ(val.value.str, "AB");
  EXPECT_NE(static_cast<const void*>(val.value.str),
            static_cast<const void*>(name));
  EXPECT_STREQ(name, "nm");
}

class BlockVariableValuesOfARun : public VpiDesignRun {
 protected:
  static void ExpectValues(
      const std::vector<std::pair<const char*, int>>& expected) {
    for (const auto& [name, value] : expected) {
      vpiHandle v = vpi_handle_by_name(VpiText(name), nullptr);
      ASSERT_NE(v, nullptr) << name;
      s_vpi_value val = {};
      val.format = vpiIntVal;
      vpi_get_value(v, &val);
      EXPECT_EQ(val.value.integer, value) << name;
    }
  }
};

TEST_F(BlockVariableValuesOfARun, ABlockVariableReadsWhatTheBlockLeft) {
  Run("module m; initial begin : blk int v; v = 7; end endmodule\n"
      "module top; m i0(); initial begin : blk int v; v = 3; end\n"
      "endmodule\n");
  ExpectValues({{"top.blk.v", 3}, {"top.i0.blk.v", 7}});
}

TEST_F(BlockVariableValuesOfARun, ANestedBlocksVariableReadsItsValue) {
  Run("module top;\n"
      "  initial begin : outer begin : inner int v; v = 5; end end\n"
      "endmodule\n");
  ExpectValues({{"top.outer.inner.v", 5}});
}

TEST_F(VpiGetValueSim, DigitStringsReadEveryWordOfAWideValue) {
  auto* var = sim_ctx_.CreateVariable("w", 72);
  var->value.words[0] = {0x1, 0};
  var->value.words[1] = {0xAB, 0};
  auto* xz = sim_ctx_.CreateVariable("xz", 72);
  xz->value.words[0] = {0x1, 0};
  xz->value.words[1] = {0xF0, 0xFF};
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name(VpiText("w"), nullptr);
  ASSERT_NE(h, nullptr);
  s_vpi_value val = {};
  val.format = vpiHexStrVal;
  vpi_get_value(h, &val);
  EXPECT_STREQ(val.value.str, "ab0000000000000001");
  val.format = vpiBinStrVal;
  vpi_get_value(h, &val);
  EXPECT_EQ(std::string(val.value.str),
            "10101011" + std::string(63, '0') + "1");
  val.format = vpiOctStrVal;
  vpi_get_value(h, &val);
  EXPECT_STREQ(val.value.str, "526000000000000000000001");

  h = vpi_handle_by_name(VpiText("xz"), nullptr);
  ASSERT_NE(h, nullptr);
  val.format = vpiHexStrVal;
  vpi_get_value(h, &val);
  EXPECT_STREQ(val.value.str, "xz0000000000000001");
}

TEST_F(VpiGetValueSim, StringValReadsEveryCharacterOfAWideValue) {
  auto* var = sim_ctx_.CreateVariable("s", 80);
  var->value.words[0] = {0x636465666768696Aull, 0};
  var->value.words[1] = {0x6162, 0};
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name(VpiText("s"), nullptr);
  ASSERT_NE(h, nullptr);
  s_vpi_value val = {};
  val.format = vpiStringVal;
  vpi_get_value(h, &val);
  ASSERT_NE(val.value.str, nullptr);
  EXPECT_STREQ(val.value.str, "abcdefghij");
}

TEST_F(VpiGetValueSim, HexDigitOfMixedXAndZBitsIsUppercaseX) {
  auto* var = sim_ctx_.CreateVariable("xz", 4);
  var->value.words[0] = {0xA, 0xF};
  vpi_ctx_.Attach(sim_ctx_);

  vpiHandle h = vpi_handle_by_name(VpiText("xz"), nullptr);
  ASSERT_NE(h, nullptr);
  s_vpi_value val = {};
  val.format = vpiHexStrVal;
  vpi_get_value(h, &val);
  EXPECT_STREQ(val.value.str, "X");
}

TEST_F(VpiGetValueSim, ANullHandleOrValueReadsNothing) {
  auto* var = sim_ctx_.CreateVariable("nv", 8);
  var->value = MakeLogic4VecVal(arena_, 8, 1);
  vpi_ctx_.Attach(sim_ctx_);
  vpiHandle h = vpi_handle_by_name(VpiText("nv"), nullptr);
  ASSERT_NE(h, nullptr);

  s_vpi_value val = {};
  val.format = vpiIntVal;
  val.value.integer = 77;
  vpi_get_value(nullptr, &val);
  vpi_get_value(h, nullptr);
  EXPECT_EQ(val.value.integer, 77);
}

TEST_F(VpiGetValueSim, ASelectWhoseIndexWasNotBuiltSelectsNothing) {
  auto* var = sim_ctx_.CreateVariable("v16", 16);
  var->value = MakeLogic4VecVal(arena_, 16, 0x1234);
  VpiObject select;
  select.type = vpiReg;
  select.var = var;
  select.size = 8;
  select.select_dim = PackedRange{1, 0};

  s_vpi_value val = {};
  val.format = vpiBinStrVal;
  vpi_get_value(VpiHandleOf(&select), &val);
  EXPECT_STREQ(val.value.str, "xxxxxxxx");
}

}  // namespace
}  // namespace delta
