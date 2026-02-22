// §7.10: Queues

#include <gtest/gtest.h>
#include <string>
#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/parser.h"
#include "simulation/eval.h"
#include "simulation/eval_array.h"
#include "simulation/sim_context.h"

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

static Expr* ParseExprFrom(const std::string& src, AggFixture& f) {
  std::string code = "module t; initial x = " + src + "; endmodule";
  auto fid = f.mgr.AddFile("<test>", code);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  auto* item = cu->modules[0]->items[0];
  return item->body->rhs;
}

// =============================================================================
// §7.2 Struct type metadata — StructTypeInfo registration
// =============================================================================
static void VerifyStructField(const StructFieldInfo& field,
                              const char* expected_name,
                              uint32_t expected_offset, uint32_t expected_width,
                              size_t index) {
  EXPECT_EQ(field.name, expected_name) << "field " << index;
  EXPECT_EQ(field.bit_offset, expected_offset) << "field " << index;
  EXPECT_EQ(field.width, expected_width) << "field " << index;
}

namespace {

TEST(ArrayAccess, OutOfBoundsReturnsX) {
  AggFixture f;
  // Register a 4-element array arr[0:3], each element 8 bits.
  f.ctx.RegisterArray("arr", {0, 4, 8, false, false, false});
  for (uint32_t i = 0; i < 4; ++i) {
    auto tmp = "arr[" + std::to_string(i) + "]";
    auto* s = f.arena.AllocString(tmp.c_str(), tmp.size());
    auto* v = f.ctx.CreateVariable(std::string_view(s, tmp.size()), 8);
    v->value = MakeLogic4VecVal(f.arena, 8, static_cast<uint64_t>(i + 1) * 10);
  }
  // In-bounds: arr[2] should return 30.
  auto in_result = EvalExpr(MkSelect(f.arena, "arr", 2), f.ctx, f.arena);
  EXPECT_EQ(in_result.ToUint64(), 30u);
  EXPECT_TRUE(in_result.IsKnown());
  // Out-of-bounds: arr[10] should return X.
  auto oob_result = EvalExpr(MkSelect(f.arena, "arr", 10), f.ctx, f.arena);
  EXPECT_FALSE(oob_result.IsKnown());
}

TEST(QueueAccess, OutOfBoundsReturnsX) {
  AggFixture f;
  auto* q = f.ctx.CreateQueue("q", 16);
  q->elements.push_back(MakeLogic4VecVal(f.arena, 16, 100));
  q->elements.push_back(MakeLogic4VecVal(f.arena, 16, 200));
  // In-bounds: q[1] should return 200.
  auto in_result = EvalExpr(MkSelect(f.arena, "q", 1), f.ctx, f.arena);
  EXPECT_EQ(in_result.ToUint64(), 200u);
  EXPECT_TRUE(in_result.IsKnown());
  // Out-of-bounds: q[5] should return X.
  auto oob_result = EvalExpr(MkSelect(f.arena, "q", 5), f.ctx, f.arena);
  EXPECT_FALSE(oob_result.IsKnown());
}

}  // namespace
