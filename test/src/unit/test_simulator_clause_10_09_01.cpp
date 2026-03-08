// Non-LRM tests

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §10.9.1: Variable declaration with array assignment pattern init.
TEST(SimCh10i, ArrayVarDeclPatternInit) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int arr [0:2] = '{5, 10, 15};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* e0 = f.ctx.FindVariable("arr[0]");
  auto* e1 = f.ctx.FindVariable("arr[1]");
  auto* e2 = f.ctx.FindVariable("arr[2]");
  ASSERT_NE(e0, nullptr);
  ASSERT_NE(e1, nullptr);
  ASSERT_NE(e2, nullptr);
  EXPECT_EQ(e0->value.ToUint64(), 5u);
  EXPECT_EQ(e1->value.ToUint64(), 10u);
  EXPECT_EQ(e2->value.ToUint64(), 15u);
}

// §10.9: Struct pattern type-keyed in full simulation.
TEST(SimCh10i, StructTypeKeyedPattern) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed {\n"
      "    int a;\n"
      "    logic [7:0] b;\n"
      "  } mixed_t;\n"
      "  mixed_t m;\n"
      "  initial begin\n"
      "    m = mixed_t'{int: 32'd99, default: 8'd0};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("m");
  ASSERT_NE(var, nullptr);
  // a (int, 32 bits at [39:8]) = 99, b (logic, 8 bits at [7:0]) = 0.
  EXPECT_EQ(var->value.ToUint64(), uint64_t{99} << 8);
}

}  // namespace
