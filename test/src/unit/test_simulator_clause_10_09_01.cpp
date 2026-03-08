// Non-LRM tests

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §10.9.1: Default key fills all array elements with the same value.
TEST(SimCh10i, ArrayDefaultKeyFillsAllElements) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] arr [0:3];\n"
      "  initial begin\n"
      "    arr = '{default: 8'd42};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  for (int i = 0; i < 4; ++i) {
    auto name = "arr[" + std::to_string(i) + "]";
    auto* elem = f.ctx.FindVariable(name);
    ASSERT_NE(elem, nullptr) << name;
    EXPECT_EQ(elem->value.ToUint64(), 42u) << name;
  }
}

// §10.9.1: Replication form fills array elements by repeating the value.
TEST(SimCh10i, ArrayReplicationPatternFills) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int arr [0:3];\n"
      "  initial begin\n"
      "    arr = '{4{7}};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  for (int i = 0; i < 4; ++i) {
    auto name = "arr[" + std::to_string(i) + "]";
    auto* elem = f.ctx.FindVariable(name);
    ASSERT_NE(elem, nullptr) << name;
    EXPECT_EQ(elem->value.ToUint64(), 7u) << name;
  }
}

// §10.9.1: Index key assigns specific elements; default fills the rest.
TEST(SimCh10i, ArrayIndexKeyWithDefault) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int arr [0:2];\n"
      "  initial begin\n"
      "    arr = '{0: 100, 2: 200, default: 0};\n"
      "  end\n"
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
  EXPECT_EQ(e0->value.ToUint64(), 100u);
  EXPECT_EQ(e1->value.ToUint64(), 0u);
  EXPECT_EQ(e2->value.ToUint64(), 200u);
}

// §10.9.1: Descending-range array with positional pattern.
TEST(SimCh10i, ArrayDescendingRangePositional) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  int arr [1:0];\n"
      "  initial begin\n"
      "    arr = '{30, 40};\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* e0 = f.ctx.FindVariable("arr[0]");
  auto* e1 = f.ctx.FindVariable("arr[1]");
  ASSERT_NE(e0, nullptr);
  ASSERT_NE(e1, nullptr);
  EXPECT_EQ(e1->value.ToUint64(), 30u);
  EXPECT_EQ(e0->value.ToUint64(), 40u);
}

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
