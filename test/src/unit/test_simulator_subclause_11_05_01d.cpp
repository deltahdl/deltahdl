#include <gtest/gtest.h>

#include <string>

#include "builders_ast.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_eval_op.h"
#include "parser/ast_expr.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"

using namespace delta;

namespace {

TEST(SelectXZHandling, NonIndexedPartSelectWithAnUnknownSecondBoundReadsAllX) {
  SimFixture f;
  auto* rx = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  logic [3:0] rx;\n"
      "  logic [3:0] rz;\n"
      "  initial begin\n"
      "    a = 8'hA5;\n"
      "    rx = a[3 : 1'bx];\n"
      "    rz = a[3 : 1'bz];\n"
      "  end\n"
      "endmodule\n",
      f, "rx");
  ASSERT_NE(rx, nullptr);
  auto* rz = f.ctx.FindVariable("rz");
  ASSERT_NE(rz, nullptr);
  EXPECT_EQ(rx->value.ToString(), "xxxx");
  EXPECT_EQ(rz->value.ToString(), "xxxx");
}

TEST(SelectXZHandling, NonIndexedPartSelectWithAnUnknownSecondBoundWritesNone) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] a;\n"
      "  initial begin\n"
      "    a = 8'hA5;\n"
      "    a[1 : 1'bx] = 2'b00;\n"
      "  end\n"
      "endmodule\n",
      f, "a");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToString(), "10100101");
}

TEST(SelectXZHandling, PartSelectWithAnUnknownSecondBoundAgreesAcrossWriters) {
  SimFixture f;
  auto* v = f.ctx.CreateVariable("wsv", 8);
  v->value = MakeLogic4VecVal(f.arena, 8, 0xA5);
  MakeVar4(f, "wsb", 1, 0, 1);

  auto* sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "wsv");
  sel->index = MakeInt(f.arena, 1);
  sel->index_end = MakeId(f.arena, "wsb");

  EXPECT_EQ(SelectStorageBits(*v, sel, f.ctx, f.arena).width, 0u);
  WriteBitSelect(v, sel, MakeLogic4VecVal(f.arena, 2, 0), f.ctx, f.arena);
  EXPECT_EQ(v->value.ToString(), "10100101");
}

}  // namespace
