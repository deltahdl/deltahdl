#include "builders_ast.h"
#include "fixture_simulator.h"
#include "helpers_array.h"
#include "simulator/eval.h"
#include "simulator/eval_array.h"
#include "simulator/stmt_assign.h"

using namespace delta;

namespace {

// §7.6: Whole-array copy (B = A) copies elements left-to-right.
TEST(ArrayAssign, WholeArrayCopy) {
  SimFixture f;
  MakeArray4(f, "src");
  MakeArray4(f, "dst");

  // Overwrite dst[0] to prove copy replaces it.
  auto* d0 = f.ctx.FindVariable("dst[0]");
  ASSERT_NE(d0, nullptr);
  d0->value = MakeLogic4VecVal(f.arena, 8, 99);

  // Execute: dst = src;
  auto* stmt = MakeAssign(f.arena, "dst", MakeId(f.arena, "src"));
  ExecBlockingAssignImpl(stmt, f.ctx, f.arena);

  // Verify all elements were copied.
  for (uint32_t i = 0; i < 4; ++i) {
    auto name = "dst[" + std::to_string(i) + "]";
    auto* v = f.ctx.FindVariable(name);
    ASSERT_NE(v, nullptr);
    EXPECT_EQ(v->value.ToUint64(), (i + 1) * 10);
  }
}

// §7.6: Array assignment pattern distributes to elements.
TEST(ArrayAssign, PatternDistribute) {
  SimFixture f;
  f.ctx.RegisterArray("arr", {0, 3, 8, false, false, false});
  for (uint32_t i = 0; i < 3; ++i) {
    auto name = "arr[" + std::to_string(i) + "]";
    auto* s = f.arena.AllocString(name.c_str(), name.size());
    f.ctx.CreateVariable(std::string_view(s, name.size()), 8);
  }

  // Build assignment pattern '{10, 20, 30}
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

}  // namespace
