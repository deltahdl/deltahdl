#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_array.h"
#include "helpers_scheduler.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"
#include "simulator/statement_assign.h"

using namespace delta;

namespace {

TEST(ArrayAssignmentSimulation, WholeArrayCopy) {
  SimFixture f;
  MakeArray4(f, "src");
  MakeArray4(f, "dst");

  auto* d0 = f.ctx.FindVariable("dst[0]");
  ASSERT_NE(d0, nullptr);
  d0->value = MakeLogic4VecVal(f.arena, 8, 99);

  auto* stmt = MakeAssign(f.arena, "dst", MakeId(f.arena, "src"));
  ExecBlockingAssignImpl(stmt, f.ctx, f.arena);

  for (uint32_t i = 0; i < 4; ++i) {
    auto name = "dst[" + std::to_string(i) + "]";
    auto* v = f.ctx.FindVariable(name);
    ASSERT_NE(v, nullptr);
    EXPECT_EQ(v->value.ToUint64(), (i + 1) * 10);
  }
}

TEST(ArrayAssignmentSimulation, PatternDistribute) {
  SimFixture f;
  f.ctx.RegisterArray("arr", {0, 3, 8, false, false, false});
  for (uint32_t i = 0; i < 3; ++i) {
    auto name = "arr[" + std::to_string(i) + "]";
    auto* s = f.arena.AllocString(name.c_str(), name.size());
    f.ctx.CreateVariable(std::string_view(s, name.size()), 8);
  }

  auto* pattern = f.arena.Create<Expr>();
  pattern->kind = ExprKind::kAssignmentPattern;
  pattern->elements = {MakeInt(f.arena, 10), MakeInt(f.arena, 20),
                       MakeInt(f.arena, 30)};

  auto* stmt = MakeAssign(f.arena, "arr", pattern);
  ExecBlockingAssignImpl(stmt, f.ctx, f.arena);

  EXPECT_EQ(f.ctx.FindVariable("arr[0]")->value.ToUint64(), 10u);
  EXPECT_EQ(f.ctx.FindVariable("arr[1]")->value.ToUint64(), 20u);
  EXPECT_EQ(f.ctx.FindVariable("arr[2]")->value.ToUint64(), 30u);
}

TEST(ArrayAssignmentSimulation, WholeArrayCopyEndToEnd) {
  auto v = RunAndGet(
      "module t;\n"
      "  int a[4];\n"
      "  int b[4];\n"
      "  int result;\n"
      "  initial begin\n"
      "    a[0] = 10; a[1] = 20; a[2] = 30; a[3] = 40;\n"
      "    b = a;\n"
      "    result = b[2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 30u);
}

TEST(ArrayAssignmentSimulation, DynamicArrayResizesOnAssign) {
  auto v = RunAndGet(
      "module t;\n"
      "  int src[] = '{10, 20, 30};\n"
      "  int dst[];\n"
      "  int result;\n"
      "  initial begin\n"
      "    dst = src;\n"
      "    result = dst.size();\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 3u);
}

TEST(ArrayAssignmentSimulation, DynamicArrayCopiesValues) {
  auto v = RunAndGet(
      "module t;\n"
      "  int src[] = '{10, 20, 30};\n"
      "  int dst[];\n"
      "  int result;\n"
      "  initial begin\n"
      "    dst = src;\n"
      "    result = dst[1];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 20u);
}

TEST(ArrayAssignmentSimulation, LeftToRightCorrespondence) {
  auto v = RunAndGet(
      "module t;\n"
      "  int a[3];\n"
      "  int b[3];\n"
      "  int result;\n"
      "  initial begin\n"
      "    a[0] = 100; a[1] = 200; a[2] = 300;\n"
      "    b = a;\n"
      "    result = b[0];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 100u);
}

TEST(ArrayAssignmentSimulation, AssignmentPatternEndToEnd) {
  auto v = RunAndGet(
      "module t;\n"
      "  int a[3];\n"
      "  int result;\n"
      "  initial begin\n"
      "    a = '{5, 10, 15};\n"
      "    result = a[2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 15u);
}

}  // namespace
