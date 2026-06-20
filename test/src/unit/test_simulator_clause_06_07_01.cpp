#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §6.7.1 default net initialization, observed through the real simulator: a
// design is elaborated, lowered, and run, then the resolved net value is read
// back from the SimContext.

// 4-state value of bit 0, encoded as (bval << 1) | aval.
//   0 -> 0, 1 -> 1, x -> 2, z -> 3
uint8_t Bit0(const Variable& v) {
  uint8_t a = v.value.words[0].aval & 1;
  uint8_t b = v.value.words[0].bval & 1;
  return static_cast<uint8_t>((b << 1) | a);
}

constexpr uint8_t kVal1 = 1;
constexpr uint8_t kValX = 2;
constexpr uint8_t kValZ = 3;

// §6.7.1: the default initialization value for a net shall be z.
TEST(NetDefaultValue, UndrivenWireDefaultsToZ) {
  LowerFixture f;
  auto* design = ElaborateSrc("module t; wire w; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(Bit0(*var), kValZ);
}

// §6.7.1: nets with drivers shall assume the output value of their drivers.
TEST(NetDefaultValue, DrivenNetAssumesDriverValue) {
  LowerFixture f;
  auto* design =
      ElaborateSrc("module t; wire w; assign w = 1'b1; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(Bit0(*var), kVal1);
}

// §6.7.1: the default applies to every bit of a vector net, not just bit 0.
// All four bits of an undriven vector wire come up z (aval=1, bval=1 per bit).
TEST(NetDefaultValue, UndrivenVectorWireAllBitsZ) {
  LowerFixture f;
  auto* design = ElaborateSrc("module t; wire [3:0] w; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval & 0xF, 0xFu);
  EXPECT_EQ(var->value.words[0].bval & 0xF, 0xFu);
}

// §6.7.1: the trireg net is an exception and shall default to x.
TEST(NetDefaultValue, UndrivenTriregDefaultsToX) {
  LowerFixture f;
  auto* design = ElaborateSrc("module t; trireg r; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(Bit0(*var), kValX);
}

// §6.7.1: the trireg x default also applies across every bit of a vector trireg
// (x is aval=0, bval=1 per bit).
TEST(NetDefaultValue, UndrivenVectorTriregAllBitsX) {
  LowerFixture f;
  auto* design = ElaborateSrc("module t; trireg [3:0] r; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* var = f.ctx.FindVariable("r");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.words[0].aval & 0xF, 0x0u);
  EXPECT_EQ(var->value.words[0].bval & 0xF, 0xFu);
}

}  // namespace
