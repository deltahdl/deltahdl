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

TEST(StructPattern, DefaultWithNamedOverride) {
  // '{a: 1, default: 0} → a=1, b=0
  AggFixture f;
  StructTypeInfo info;
  info.type_name = "pair_t";
  info.is_packed = true;
  info.total_width = 16;
  info.fields.push_back({"a", 8, 8, DataTypeKind::kLogic});
  info.fields.push_back({"b", 0, 8, DataTypeKind::kLogic});

  auto* pat = f.arena.Create<Expr>();
  pat->kind = ExprKind::kAssignmentPattern;
  pat->pattern_keys = {"a", "default"};
  pat->elements = {MakeIntLit(f.arena, 1), MakeIntLit(f.arena, 0)};

  auto result = EvalStructPattern(pat, &info, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0x0100u);
}

TEST(StructPattern, TypeKeyedInt) {
  // '{int: 42} on struct { int a; logic [7:0] b; } → a=42, b=0
  AggFixture f;
  StructTypeInfo info;
  info.type_name = "mixed_t";
  info.is_packed = true;
  info.total_width = 40;
  info.fields.push_back({"a", 8, 32, DataTypeKind::kInt});
  info.fields.push_back({"b", 0, 8, DataTypeKind::kLogic});

  auto* pat = f.arena.Create<Expr>();
  pat->kind = ExprKind::kAssignmentPattern;
  pat->pattern_keys = {"int"};
  pat->elements = {MakeIntLit(f.arena, 42)};

  auto result = EvalStructPattern(pat, &info, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), uint64_t{42} << 8);
}

TEST(StructPattern, MixedPrecedence) {
  // '{a: 1, byte: 2, default: 3} — member > type > default
  // struct { byte a; byte b; logic [7:0] c; }
  // a=1 (explicit member overrides byte key), b=2 (byte type key), c=3
  // (default)
  AggFixture f;
  StructTypeInfo info;
  info.type_name = "multi_t";
  info.is_packed = true;
  info.total_width = 24;
  info.fields.push_back({"a", 16, 8, DataTypeKind::kByte});
  info.fields.push_back({"b", 8, 8, DataTypeKind::kByte});
  info.fields.push_back({"c", 0, 8, DataTypeKind::kLogic});

  auto* pat = f.arena.Create<Expr>();
  pat->kind = ExprKind::kAssignmentPattern;
  pat->pattern_keys = {"a", "byte", "default"};
  pat->elements = {MakeIntLit(f.arena, 1), MakeIntLit(f.arena, 2),
                   MakeIntLit(f.arena, 3)};

  auto result = EvalStructPattern(pat, &info, f.ctx, f.arena);
  uint64_t expected = (uint64_t{1} << 16) | (uint64_t{2} << 8) | 3;
  EXPECT_EQ(result.ToUint64(), expected);
}

// =============================================================================
// §10.9 Assignment pattern evaluation
// =============================================================================
TEST(AssignmentPattern, PositionalTwoElements) {
  // '{a, b} with 8-bit variables → 16-bit packed result
  AggFixture f;
  auto* a = f.ctx.CreateVariable("a", 8);
  auto* b = f.ctx.CreateVariable("b", 8);
  a->value = MakeLogic4VecVal(f.arena, 8, 5);
  b->value = MakeLogic4VecVal(f.arena, 8, 10);
  auto* expr = ParseExprFrom("'{a, b}", f);
  ASSERT_NE(expr, nullptr);
  EXPECT_EQ(expr->kind, ExprKind::kAssignmentPattern);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  // {a=5, b=10} → MSB-first: 5 in [15:8], 10 in [7:0] = 16'h050A
  EXPECT_EQ(result.width, 16u);
  EXPECT_EQ(result.ToUint64(), 0x050Au);
}

TEST(AssignmentPattern, PositionalThreeElements) {
  AggFixture f;
  auto* a = f.ctx.CreateVariable("a", 4);
  auto* b = f.ctx.CreateVariable("b", 4);
  auto* c = f.ctx.CreateVariable("c", 4);
  a->value = MakeLogic4VecVal(f.arena, 4, 1);
  b->value = MakeLogic4VecVal(f.arena, 4, 2);
  c->value = MakeLogic4VecVal(f.arena, 4, 3);
  auto* expr = ParseExprFrom("'{a, b, c}", f);
  auto result = EvalExpr(expr, f.ctx, f.arena);
  // {1, 2, 3} → 12-bit: 0x123
  EXPECT_EQ(result.width, 12u);
  EXPECT_EQ(result.ToUint64(), 0x123u);
}

}  // namespace
