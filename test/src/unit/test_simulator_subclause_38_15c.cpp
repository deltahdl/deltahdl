#include <gtest/gtest.h>

#include <cmath>
#include <cstddef>
#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class FormatsOfARun : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    Run("module top;\n"
        "  real up = 2.5, down = -2.5, third = 1.0 / 3.0, tenth = 0.1;\n"
        "  real big = 1234567890.123456789, oct = 10.5, hex = 26.5;\n"
        "  real high = 0.6, low = 0.4;\n"
        "  realtime rt = 1.5; shortreal sr = 0.25;\n"
        "  logic [2:0] mixed = 3'bxzz;\n"
        "  logic [99:0] wide = {4'hA, 32'h33333333, 32'h22222222,\n"
        "                       32'h11111111};\n"
        "  logic en = 1'bx;\n"
        "  wire h, l; bufif1 bh(h, 1'b1, en); bufif1 bl(l, 1'b0, en);\n"
        "  wire w; assign (weak1, weak0) w = 1'b1;\n"
        "  wire p; pullup pu(p);\n"
        "  wire [1:0] v; assign v[0] = 1'b1; pullup pv(v[1]);\n"
        "  wire [23:0] text; assign text = \"abc\";\n"
        "  wire sn = 1'b1; wire [7:0] vn = 8'h5A;\n"
        "  int n = -7; integer g = 9; time t = 64'd5000000000;\n"
        "  typedef enum {A, B, C} e_t; e_t e = C;\n"
        "  typedef struct packed { logic [3:0] a, b; } ps_t;\n"
        "  ps_t ps = 8'h12;\n"
        "endmodule\n");
  }

  static s_vpi_value Read(const char* name, PLI_INT32 format) {
    s_vpi_value value = {};
    value.format = format;
    vpi_get_value(By(name), &value);
    return value;
  }

  static std::string TextOf(const char* name, PLI_INT32 format) {
    const s_vpi_value kValue = Read(name, format);
    return kValue.value.str != nullptr ? std::string(kValue.value.str) : "";
  }

  static std::string Digits(const char* name, PLI_INT32 format) {
    const std::string kText = TextOf(name, format);
    const std::size_t kFirst = kText.find_first_not_of('0');
    return kFirst == std::string::npos ? "0" : kText.substr(kFirst);
  }

  static int SignificantDigits(const std::string& text) {
    int count = 0;
    bool leading = true;
    for (const char kChar : text) {
      if (kChar == 'e' || kChar == 'E') break;
      if (kChar < '0' || kChar > '9') continue;
      if (leading && kChar == '0') continue;
      leading = false;
      ++count;
    }
    return count;
  }

  static PLI_INT32 StrengthOne(const char* name, int bit) {
    const s_vpi_value kValue = Read(name, vpiStrengthVal);
    return kValue.value.strength != nullptr ? kValue.value.strength[bit].s1
                                            : -1;
  }
};

TEST_F(FormatsOfARun, ARealReadAsAVectorHoldsItsRoundedInteger) {
  const s_vpi_value kUp = Read("top.up", vpiVectorVal);
  ASSERT_NE(kUp.value.vector, nullptr);
  EXPECT_EQ(kUp.value.vector[0].aval, 3u);
  EXPECT_EQ(kUp.value.vector[0].bval, 0u);
  const s_vpi_value kDown = Read("top.down", vpiVectorVal);
  ASSERT_NE(kDown.value.vector, nullptr);
  EXPECT_EQ(kDown.value.vector[0].aval, 0xFFFFFFFDu);
  EXPECT_EQ(kDown.value.vector[0].bval, 0u);
}

TEST_F(FormatsOfARun, ARealReadAsTextIsItsRoundedIntegersText) {
  EXPECT_EQ(Digits("top.up", vpiBinStrVal), "11");
  EXPECT_EQ(Digits("top.oct", vpiOctStrVal), "13");
  EXPECT_EQ(Digits("top.hex", vpiHexStrVal), "1b");
  EXPECT_EQ(TextOf("top.up", vpiDecStrVal), "3");
}

TEST_F(FormatsOfARun, DISABLED_ANegativeRealReadAsDecimalTextKeepsItsSign) {
  EXPECT_EQ(TextOf("top.down", vpiDecStrVal), "-3");
}

TEST_F(FormatsOfARun, ARealReadAsAScalarOrStrengthTakesItsRoundedInteger) {
  EXPECT_EQ(Read("top.high", vpiScalarVal).value.scalar, vpi1);
  EXPECT_EQ(Read("top.low", vpiScalarVal).value.scalar, vpi0);
  const s_vpi_value kHigh = Read("top.high", vpiStrengthVal);
  ASSERT_NE(kHigh.value.strength, nullptr);
  EXPECT_EQ(kHigh.value.strength[0].logic, vpi1);
  const s_vpi_value kLow = Read("top.low", vpiStrengthVal);
  ASSERT_NE(kLow.value.strength, nullptr);
  EXPECT_EQ(kLow.value.strength[0].logic, vpi0);
}

TEST_F(FormatsOfARun, ARealReadAsATimeHoldsItsRoundedInteger) {
  const s_vpi_value kUp = Read("top.up", vpiTimeVal);
  ASSERT_NE(kUp.value.time, nullptr);
  EXPECT_EQ(kUp.value.time->low, 3u);
  EXPECT_EQ(kUp.value.time->high, 0u);
}

TEST_F(FormatsOfARun, ARealReadAsAStringHasAtMostSixteenDigits) {
  for (const char* name : {"top.third", "top.tenth", "top.big"}) {
    const std::string kText = TextOf(name, vpiStringVal);
    ASSERT_FALSE(kText.empty()) << name;
    EXPECT_LE(SignificantDigits(kText), 16) << name << " " << kText;
    const double kExpected = Read(name, vpiRealVal).value.real;
    EXPECT_NEAR(std::stod(kText), kExpected, std::fabs(kExpected) * 1e-15)
        << name;
  }
}

TEST_F(FormatsOfARun, AStringConstantReadsAsAStringOrAVector) {
  vpiHandle constant = nullptr;
  for (vpiHandle assign : ObjectsOf(vpiContAssign, By("top"))) {
    vpiHandle rhs = vpi_handle(vpiRhs, assign);
    if (rhs != nullptr && vpi_get(vpiType, rhs) == vpiConstant &&
        vpi_get(vpiConstType, rhs) == vpiStringConst) {
      constant = rhs;
    }
  }
  ASSERT_NE(constant, nullptr);
  s_vpi_value text = {};
  text.format = vpiStringVal;
  vpi_get_value(constant, &text);
  ASSERT_NE(text.value.str, nullptr);
  EXPECT_STREQ(text.value.str, "abc");
  s_vpi_value bits = {};
  bits.format = vpiVectorVal;
  vpi_get_value(constant, &bits);
  ASSERT_NE(bits.value.vector, nullptr);
  EXPECT_EQ(bits.value.vector[0].aval, 0x616263u);
  EXPECT_EQ(bits.value.vector[0].bval, 0u);
}

TEST_F(FormatsOfARun, AnOctalDigitMixingXAndZBitsReadsAsCapitalX) {
  EXPECT_EQ(TextOf("top.mixed", vpiOctStrVal), "X");
}

TEST_F(FormatsOfARun, DISABLED_ANetOfAmbiguousStrengthReadsAsHOrL) {
  EXPECT_EQ(Read("top.h", vpiScalarVal).value.scalar, vpiH);
  EXPECT_EQ(Read("top.l", vpiScalarVal).value.scalar, vpiL);
}

TEST_F(FormatsOfARun, DISABLED_ANetReportsTheStrengthItIsDriven) {
  EXPECT_EQ(StrengthOne("top.w", 0), vpiWeakDrive);
  EXPECT_EQ(StrengthOne("top.p", 0), vpiPullDrive);
}

TEST_F(FormatsOfARun, DISABLED_EachBitOfAVectorNetReportsItsOwnStrength) {
  EXPECT_EQ(StrengthOne("top.v", 0), vpiStrongDrive);
  EXPECT_EQ(StrengthOne("top.v", 1), vpiPullDrive);
}

TEST_F(FormatsOfARun, AValueOfFourWordsKeepsEveryWordInPlace) {
  const s_vpi_value kWide = Read("top.wide", vpiVectorVal);
  ASSERT_NE(kWide.value.vector, nullptr);
  const std::vector<PLI_UINT32> kAvals = {
      kWide.value.vector[0].aval, kWide.value.vector[1].aval,
      kWide.value.vector[2].aval, kWide.value.vector[3].aval};
  EXPECT_EQ(kAvals, (std::vector<PLI_UINT32>{0x11111111u, 0x22222222u,
                                             0x33333333u, 0xAu}));
  EXPECT_EQ(kWide.value.vector[3].bval, 0u);
}

TEST_F(FormatsOfARun, ObjTypeReadsEveryRealKindAsAReal) {
  const s_vpi_value kUp = Read("top.up", vpiObjTypeVal);
  EXPECT_EQ(kUp.format, vpiRealVal);
  EXPECT_DOUBLE_EQ(kUp.value.real, 2.5);
  const s_vpi_value kRt = Read("top.rt", vpiObjTypeVal);
  EXPECT_EQ(kRt.format, vpiRealVal);
  EXPECT_DOUBLE_EQ(kRt.value.real, 1.5);
  const s_vpi_value kSr = Read("top.sr", vpiObjTypeVal);
  EXPECT_EQ(kSr.format, vpiRealVal);
  EXPECT_DOUBLE_EQ(kSr.value.real, 0.25);
}

TEST_F(FormatsOfARun, ObjTypeReadsAScalarNetAsAScalarAndAVectorNetAsAVector) {
  const s_vpi_value kScalar = Read("top.sn", vpiObjTypeVal);
  ASSERT_TRUE(kScalar.format == vpiScalarVal ||
              kScalar.format == vpiStrengthVal);
  if (kScalar.format == vpiScalarVal) {
    EXPECT_EQ(kScalar.value.scalar, vpi1);
  } else {
    ASSERT_NE(kScalar.value.strength, nullptr);
    EXPECT_EQ(kScalar.value.strength[0].logic, vpi1);
  }
  const s_vpi_value kVector = Read("top.vn", vpiObjTypeVal);
  EXPECT_EQ(kVector.format, vpiVectorVal);
  ASSERT_NE(kVector.value.vector, nullptr);
  EXPECT_EQ(kVector.value.vector[0].aval, 0x5Au);
}

TEST_F(FormatsOfARun, ObjTypeReadsAnIntegerKindAsAnInteger) {
  const s_vpi_value kInt = Read("top.n", vpiObjTypeVal);
  EXPECT_EQ(kInt.format, vpiIntVal);
  EXPECT_EQ(kInt.value.integer, -7);
  const s_vpi_value kInteger = Read("top.g", vpiObjTypeVal);
  EXPECT_EQ(kInteger.format, vpiIntVal);
  EXPECT_EQ(kInteger.value.integer, 9);
}

TEST_F(FormatsOfARun, DISABLED_ObjTypeReadsAnEnumOfIntAsAnInteger) {
  const s_vpi_value kEnum = Read("top.e", vpiObjTypeVal);
  EXPECT_EQ(kEnum.format, vpiIntVal);
  EXPECT_EQ(kEnum.value.integer, 2);
}

TEST_F(FormatsOfARun, ObjTypeReadsATimeVariableAsASimulationTime) {
  const s_vpi_value kTime = Read("top.t", vpiObjTypeVal);
  EXPECT_EQ(kTime.format, vpiTimeVal);
  ASSERT_NE(kTime.value.time, nullptr);
  EXPECT_EQ(kTime.value.time->type, vpiSimTime);
  EXPECT_EQ(kTime.value.time->high, 1u);
  EXPECT_EQ(kTime.value.time->low, 705032704u);
}

TEST_F(FormatsOfARun, ObjTypeReadsAPackedStructAsAVector) {
  const s_vpi_value kStruct = Read("top.ps", vpiObjTypeVal);
  EXPECT_EQ(kStruct.format, vpiVectorVal);
  ASSERT_NE(kStruct.value.vector, nullptr);
  EXPECT_EQ(kStruct.value.vector[0].aval, 0x12u);
}

}  // namespace
}  // namespace delta
