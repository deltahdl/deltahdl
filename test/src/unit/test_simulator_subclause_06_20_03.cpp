#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(TypeParameterSim, DefaultTypeParamResolvesWidth) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  parameter type T = shortint;\n"
      "  T x;\n"
      "  initial x = 32'hFFFFFFFF;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.width, 16u);
  EXPECT_EQ(var->value.ToUint64(), 0xFFFFu);
}

TEST(TypeParameterSim, LocalparamTypeResolvesWidth) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  localparam type T = byte;\n"
      "  T data;\n"
      "  initial data = 8'hAB;\n"
      "endmodule\n",
      f, "data");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.width, 8u);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

// §6.20.3: a type parameter whose type is a packed vector sets the width of a
// dependent variable, observable at run time when an over-wide value assigned
// to it is truncated to that width.
TEST(TypeParameterSim, VectorTypeParamResolvesWidth) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  parameter type T = logic [7:0];\n"
      "  T x;\n"
      "  initial x = 16'hABCD;\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);

  EXPECT_EQ(var->value.width, 8u);
  EXPECT_EQ(var->value.ToUint64(), 0xCDu);
}

TEST(TypeParameterSim, MultipleTypeParamsResolveCorrectly) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter type A = int;\n"
      "  parameter type B = shortint;\n"
      "  A x;\n"
      "  B y;\n"
      "  initial begin\n"
      "    x = 32'hDEADBEEF;\n"
      "    y = 16'hCAFE;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();

  auto* vx = f.ctx.FindVariable("x");
  auto* vy = f.ctx.FindVariable("y");
  ASSERT_NE(vx, nullptr);
  ASSERT_NE(vy, nullptr);

  EXPECT_EQ(vx->value.width, 32u);
  EXPECT_EQ(vx->value.ToUint64(), 0xDEADBEEFu);
  EXPECT_EQ(vy->value.width, 16u);
  EXPECT_EQ(vy->value.ToUint64(), 0xCAFEu);
}

// §23.10.2 with §6.20.3: an override is written in the instantiating module,
// so `child #(bus_t)` hands the child the parent's bus_t, 13 bits, although the
// child's own type parameter has the same name; so does §6.23's
// `parameter type bus_t = type(A_bus)` for a parent's bus_t.
TEST(TypeParameterSim, OverrideNamesTheParentsTypeOfTheSameName) {
  const std::string kSrc =
      "module child #(type bus_t = bit [7:0]) ();\n"
      "  bus_t v;\n"
      "  int w;\n"
      "  initial w = $bits(v);\n"
      "endmodule\n"
      "module t;\n"
      "  bit [12:0] A_bus;\n"
      "  parameter type bus_t = bit [12:0];\n"
      "  parameter type ref_t = type(A_bus);\n"
      "  child #(bus_t) u1 ();\n"
      "  child #(.bus_t(ref_t)) u2 ();\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "u1.w"), 13u);
  EXPECT_EQ(RunAndGet(kSrc, "u2.w"), 13u);
}

// Each override reads the parent's names, not a child parameter an earlier
// override has already set: `.A(B), .B(A)` swaps the parent's byte and
// shortint into the child.
TEST(TypeParameterSim, OverridesSwappingTwoNamesReadTheParents) {
  const std::string kSrc =
      "module child #(type A = int, type B = int) ();\n"
      "  A a; B b;\n"
      "  int wa, wb;\n"
      "  initial begin wa = $bits(a); wb = $bits(b); end\n"
      "endmodule\n"
      "module t;\n"
      "  parameter type A = byte;\n"
      "  parameter type B = shortint;\n"
      "  child #(.A(B), .B(A)) u ();\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(kSrc, "u.wa"), 16u);
  EXPECT_EQ(RunAndGet(kSrc, "u.wb"), 8u);
}

}  // namespace
