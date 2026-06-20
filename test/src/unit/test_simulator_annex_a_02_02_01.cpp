#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(NetAndVariableTypeSimulation, IntegerVectorTypeLogicRuntimeWidth) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial x = 8'hAB;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 8u);
  EXPECT_EQ(var->value.ToUint64(), 0xABu);
}

TEST(NetAndVariableTypeSimulation, IntegerAtomByteRuntimeWidth) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  byte b;\n"
      "  initial b = 8'h7F;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 8u);
}

TEST(NetAndVariableTypeSimulation, IntegerAtomIntRuntimeWidth) {
  auto val = RunAndGet(
      "module t;\n"
      "  int i;\n"
      "  initial i = 32'hDEAD_BEEF;\n"
      "endmodule\n",
      "i");
  EXPECT_EQ(val, 0xDEADBEEFull);
}

TEST(NetAndVariableTypeSimulation, SigningSignedExtendsThroughArithmetic) {
  auto val = RunAndGet(
      "module t;\n"
      "  logic signed [3:0] s;\n"
      "  logic signed [7:0] y;\n"
      "  initial begin\n"
      "    s = -4'sd3;\n"
      "    y = s;\n"
      "  end\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(val & 0xFFu, 0xFDu);
}

TEST(NetAndVariableTypeSimulation, NetTypeWireDrivesValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  wire [3:0] w;\n"
      "  assign w = 4'hA;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("w");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 0xAu);
}

TEST(NetAndVariableTypeSimulation, StructUnionPackedMemberAccess) {
  auto val = RunAndGet(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [3:0] hi;\n"
      "    logic [3:0] lo;\n"
      "  } s_t;\n"
      "  s_t s;\n"
      "  logic [3:0] y;\n"
      "  initial begin\n"
      "    s = 8'hA5;\n"
      "    y = s.lo;\n"
      "  end\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(val, 0x5u);
}

TEST(NetAndVariableTypeSimulation, EnumNameValueResolvesAtRuntime) {
  auto val = RunAndGet(
      "module t;\n"
      "  typedef enum logic [2:0] { A = 0, B = 1, C = 4 } e_t;\n"
      "  e_t e;\n"
      "  logic [2:0] y;\n"
      "  initial begin\n"
      "    e = C;\n"
      "    y = e;\n"
      "  end\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(val, 4u);
}

TEST(NetAndVariableTypeSimulation, PackedDimensionDrivesRuntimeWidth) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter int W = 12;\n"
      "  logic [W-1:0] data;\n"
      "  initial data = '0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("data");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.width, 12u);
}

TEST(NetAndVariableTypeSimulation, IntegerVectorTypeBitIsTwoState) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  bit [3:0] b;\n"
      "  initial b = 4'b1010;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("b");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64() & 0xFu, 0xAu);
}

}  // namespace
