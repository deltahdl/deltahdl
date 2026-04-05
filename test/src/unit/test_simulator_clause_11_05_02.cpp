#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "helpers_scheduler.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

TEST(ArrayAddressing, ArrayXZAddrReturnsX) {
  SimFixture f;

  MakeVar(f, "arr4[0]", 8, 0x11);
  MakeVar(f, "arr4[1]", 8, 0x22);
  ArrayInfo info{};
  info.lo = 0;
  info.size = 2;
  info.elem_width = 8;
  f.ctx.RegisterArray("arr4", info);

  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "arr4");

  auto* idx = MakeInt(f.arena, 0);
  sel->index = idx;

  auto* xvar = f.ctx.CreateVariable("xidx", 8);
  xvar->value = MakeLogic4Vec(f.arena, 8);
  xvar->value.words[0].aval = 1;
  xvar->value.words[0].bval = 1;
  sel->index = MakeId(f.arena, "xidx");

  auto result = EvalExpr(sel, f.ctx, f.arena);

  EXPECT_NE(result.nwords, 0u);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(MemorySimulation, WordWriteAndReadByAddress) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] mema [0:255];\n"
      "  int result;\n"
      "  int addr;\n"
      "  initial begin\n"
      "    mema[5] = 8'hA5;\n"
      "    addr = 5;\n"
      "    result = mema[addr];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xA5u);
}

TEST(MultidimensionalArraySimulation, TwoDimElementAccess) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] mem [0:3][0:3];\n"
      "  int result;\n"
      "  initial begin\n"
      "    mem[1][2] = 8'hAB;\n"
      "    result = mem[1][2];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xABu);
}

TEST(ArrayAddressing, MemoryIndirection) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] mem [0:7];\n"
      "  int result;\n"
      "  initial begin\n"
      "    mem[3] = 8'd1;\n"
      "    mem[1] = 8'hCD;\n"
      "    result = mem[mem[3]];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xCDu);
}

TEST(ArrayAddressing, ComputedIndexExpression) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] mem [0:7];\n"
      "  int result;\n"
      "  int a, b;\n"
      "  initial begin\n"
      "    mem[5] = 8'hEF;\n"
      "    a = 2;\n"
      "    b = 3;\n"
      "    result = mem[a + b];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0xEFu);
}

TEST(ArrayAddressing, ArrayOOBReturnsX) {
  SimFixture f;

  ArrayInfo info{};
  info.lo = 0;
  info.size = 4;
  info.elem_width = 8;
  info.is_4state = true;
  f.ctx.RegisterArray("oob_arr", info);
  for (uint32_t i = 0; i < 4; ++i) {
    auto tmp = "oob_arr[" + std::to_string(i) + "]";
    auto* s = f.arena.AllocString(tmp.c_str(), tmp.size());
    auto* v = f.ctx.CreateVariable(std::string_view(s, tmp.size()), 8);
    v->value = MakeLogic4VecVal(f.arena, 8, static_cast<uint64_t>(i + 1) * 10);
  }

  auto result = EvalExpr(MakeSelect(f.arena, "oob_arr", 10), f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(ArrayAddressing, BitSelectAfterArrayElement) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] arr [0:3];\n"
      "  logic result;\n"
      "  initial begin\n"
      "    arr[2] = 8'b01000000;\n"
      "    result = arr[2][6];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 1u);
}

TEST(ArrayAddressing, PartSelectAfterArrayElement) {
  auto v = RunAndGet(
      "module t;\n"
      "  logic [7:0] twod [0:3][0:3];\n"
      "  logic [3:0] result;\n"
      "  initial begin\n"
      "    twod[1][2] = 8'hA5;\n"
      "    result = twod[1][2][3:0];\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 0x5u);
}

}  // namespace
