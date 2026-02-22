// Non-LRM tests

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

TEST(ArraySlice, ReadSliceConcat) {
  AggFixture f;
  MakeArray4(f, "arr");
  // arr = {10, 20, 30, 40}.  arr[2:1] should give {arr[2], arr[1]} = {30, 20}.
  // Concatenated into a 16-bit value: arr[2] in high byte, arr[1] in low byte.
  auto result = EvalExpr(MkSlice(f.arena, "arr", 2, 1), f.ctx, f.arena);
  EXPECT_EQ(result.width, 16u);
  // arr[2]=30, arr[1]=20  →  (30 << 8) | 20 = 7700
  EXPECT_EQ(result.ToUint64(), (30u << 8) | 20u);
}

TEST(ArrayEquality, EqualArrays) {
  AggFixture f;
  MakeArray4(f, "a");
  MakeArray4(f, "b");
  auto result = EvalExpr(MkEq(f.arena, "a", "b"), f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(ArrayEquality, UnequalArrays) {
  AggFixture f;
  MakeArray4(f, "a");
  MakeArray4(f, "b");
  // Modify b[2] to differ.
  auto* v = f.ctx.FindVariable("b[2]");
  ASSERT_NE(v, nullptr);
  v->value = MakeLogic4VecVal(f.arena, 8, 99);
  auto result = EvalExpr(MkEq(f.arena, "a", "b"), f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(AssocTraversal, FirstReturnsTruncationFlag) {
  AggFixture f;
  // 32-bit index type, ref variable is only 8 bits → truncation → returns -1.
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->index_width = 32;
  aa->int_data[1000] = MakeLogic4VecVal(f.arena, 32, 42);
  auto* ref = f.ctx.CreateVariable("k", 8);
  ref->value = MakeLogic4VecVal(f.arena, 8, 0);
  Logic4Vec out{};
  auto* call = MkAssocCall(f.arena, "aa", "first", "k");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  ASSERT_TRUE(ok);
  // ref width (8) < index_width (32) → result should be -1 (as uint64 = max).
  // WriteTraversalKey returns -1, cast to uint64_t wraps.
  uint64_t r = out.ToUint64();
  // The result is stored as MakeLogic4VecVal(32, (uint64_t)-1) = 0xFFFFFFFF.
  EXPECT_EQ(r, static_cast<uint64_t>(static_cast<uint32_t>(-1)));
  // Key should still be written (truncated to 8 bits).
  EXPECT_EQ(ref->value.ToUint64(), 1000u & 0xFFu);
}

}  // namespace
