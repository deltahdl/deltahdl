#include "builders_ast.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(PrimarySim, PrimarySystemCallBits) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] data;\n"
      "  int x;\n"
      "  initial x = $bits(data);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 8u);
}

// §20.6.2: $bits returns a value whose type is integer; the simulator
// constructs the result as a 32-bit Logic4Vec irrespective of how wide the
// argument is.
TEST(UtilitySystemTaskTest, BitsResultIsInteger) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("v", 7);
  var->value = MakeLogic4VecVal(f.arena, 7, 0);
  auto* expr = MakeSysCall(f.arena, "$bits", {MakeId(f.arena, "v")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
  EXPECT_EQ(result.ToUint64(), 7u);
}

// §20.6.2: $bits returns 0 when its argument is a dynamically sized
// expression that is currently empty; the simulator's width-driven path
// yields 0 for a value carrying zero bits.
TEST(UtilitySystemTaskTest, BitsOfCurrentlyEmptyDynamicReturnsZero) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("empty", 0);
  var->value = MakeLogic4VecVal(f.arena, 0, 0);
  auto* expr = MakeSysCall(f.arena, "$bits", {MakeId(f.arena, "empty")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

// §20.6.2: a 4-state value counts as 1 bit. An 8-bit logic vector whose
// content has X/Z mixed with 0/1 shall still report a bit-stream size of 8,
// since the X/Z don't expand the stream.
TEST(UtilitySystemTaskTest, BitsOf4StateValueCountsOneBitPerPosition) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("mixed", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 0xAA);
  var->value.words[0].bval = 0x0F;
  auto* expr = MakeSysCall(f.arena, "$bits", {MakeId(f.arena, "mixed")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 8u);
}

// §20.6.2 NC6: the packed struct {logic valid; bit [8:1] data;} has total
// bit-stream width 9 (1 + 8). $bits on either the typedef or a variable of
// that type shall report exactly that width.
TEST(PrimarySim, BitsOfPackedStructTypedefMatchesMemberSum) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic valid; bit [8:1] data; } MyType;\n"
      "  int w_type;\n"
      "  int w_var;\n"
      "  MyType m;\n"
      "  initial begin\n"
      "    w_type = $bits(MyType);\n"
      "    w_var = $bits(m);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* w_type = f.ctx.FindVariable("w_type");
  auto* w_var = f.ctx.FindVariable("w_var");
  ASSERT_NE(w_type, nullptr);
  ASSERT_NE(w_var, nullptr);
  EXPECT_EQ(w_type->value.ToUint64(), 9u);
  EXPECT_EQ(w_var->value.ToUint64(), 9u);
}

}  // namespace
