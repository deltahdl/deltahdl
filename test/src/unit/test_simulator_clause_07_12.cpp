// §7.12: Array manipulation methods

#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/eval.h"
#include "simulator/eval_array.h"

using namespace delta;

// =============================================================================
// Helper fixture
// =============================================================================
static void MakeDynArray(SimFixture& f, std::string_view name,
                         const std::vector<uint64_t>& vals) {
  auto* q = f.ctx.CreateQueue(name, 32);
  for (auto v : vals) {
    q->elements.push_back(MakeLogic4VecVal(f.arena, 32, v));
  }
  ArrayInfo info;
  info.is_dynamic = true;
  info.elem_width = 32;
  info.size = static_cast<uint32_t>(vals.size());
  f.ctx.RegisterArray(name, info);
}

namespace {

TEST(DynArrayMethod, SumReduction) {
  SimFixture f;
  MakeDynArray(f, "d", {10, 20, 30, 40});
  Logic4Vec out{};
  bool ok = TryEvalArrayProperty("d", "sum", f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 100u);
}

TEST(DynArrayMethod, SizeProperty) {
  SimFixture f;
  MakeDynArray(f, "d", {1, 2, 3});
  Logic4Vec out{};
  bool ok = TryEvalArrayProperty("d", "size", f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 3u);
}

TEST(DynArrayMethod, MinReduction) {
  SimFixture f;
  MakeDynArray(f, "d", {50, 10, 30});
  Logic4Vec out{};
  bool ok = TryEvalArrayProperty("d", "min", f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 10u);
}

TEST(DynArrayMethod, MaxReduction) {
  SimFixture f;
  MakeDynArray(f, "d", {50, 10, 30});
  Logic4Vec out{};
  bool ok = TryEvalArrayProperty("d", "max", f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 50u);
}

}  // namespace
