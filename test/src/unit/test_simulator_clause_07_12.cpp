// §7.12: Array manipulation methods

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/parser.h"
#include "simulation/eval.h"
#include "simulation/eval_array.h"
#include "simulation/sim_context.h"
#include <gtest/gtest.h>
#include <string>

using namespace delta;

// =============================================================================
// Helper fixture
// =============================================================================
struct AggFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static void MakeDynArray(AggFixture &f, std::string_view name,
                         const std::vector<uint64_t> &vals) {
  auto *q = f.ctx.CreateQueue(name, 32);
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
  AggFixture f;
  MakeDynArray(f, "d", {10, 20, 30, 40});
  Logic4Vec out{};
  bool ok = TryEvalArrayProperty("d", "sum", f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 100u);
}

TEST(DynArrayMethod, SizeProperty) {
  AggFixture f;
  MakeDynArray(f, "d", {1, 2, 3});
  Logic4Vec out{};
  bool ok = TryEvalArrayProperty("d", "size", f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 3u);
}

TEST(DynArrayMethod, MinReduction) {
  AggFixture f;
  MakeDynArray(f, "d", {50, 10, 30});
  Logic4Vec out{};
  bool ok = TryEvalArrayProperty("d", "min", f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 10u);
}

TEST(DynArrayMethod, MaxReduction) {
  AggFixture f;
  MakeDynArray(f, "d", {50, 10, 30});
  Logic4Vec out{};
  bool ok = TryEvalArrayProperty("d", "max", f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  EXPECT_EQ(out.ToUint64(), 50u);
}

} // namespace
