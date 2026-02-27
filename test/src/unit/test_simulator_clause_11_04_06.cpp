// §11.4.6: Wildcard equality operators


#include "parser/ast.h"
#include "simulation/eval.h"
#include "simulation/eval_array.h"

#include "fixture_simulator.h"

using namespace delta;

// =============================================================================
// Helper fixture
// =============================================================================
static Expr* MkEq(Arena& arena, std::string_view a, std::string_view b) {
  auto* expr = arena.Create<Expr>();
  expr->kind = ExprKind::kBinary;
  expr->op = TokenKind::kEqEq;
  auto* lhs = arena.Create<Expr>();
  lhs->kind = ExprKind::kIdentifier;
  lhs->text = a;
  auto* rhs = arena.Create<Expr>();
  rhs->kind = ExprKind::kIdentifier;
  rhs->text = b;
  expr->lhs = lhs;
  expr->rhs = rhs;
  return expr;
}

static void MakeArray4(SimFixture& f, std::string_view name) {
  f.ctx.RegisterArray(name, {0, 4, 8, false, false, false});
  for (uint32_t i = 0; i < 4; ++i) {
    auto tmp = std::string(name) + "[" + std::to_string(i) + "]";
    auto* s = f.arena.AllocString(tmp.c_str(), tmp.size());
    auto* v = f.ctx.CreateVariable(std::string_view(s, tmp.size()), 8);
    v->value = MakeLogic4VecVal(f.arena, 8, static_cast<uint64_t>(i + 1) * 10);
  }
}
namespace {

TEST(ArrayEquality, EqualArrays) {
  SimFixture f;
  MakeArray4(f, "a");
  MakeArray4(f, "b");
  auto result = EvalExpr(MkEq(f.arena, "a", "b"), f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(ArrayEquality, UnequalArrays) {
  SimFixture f;
  MakeArray4(f, "a");
  MakeArray4(f, "b");
  // Modify b[2] to differ.
  auto* v = f.ctx.FindVariable("b[2]");
  ASSERT_NE(v, nullptr);
  v->value = MakeLogic4VecVal(f.arena, 8, 99);
  auto result = EvalExpr(MkEq(f.arena, "a", "b"), f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

// Shared fixture for expression evaluation tests.
static Expr* MakeId(Arena& arena, std::string_view name) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIdentifier;
  e->text = name;
  return e;
}

static Expr* MakeBinary(Arena& arena, TokenKind op, Expr* lhs, Expr* rhs) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kBinary;
  e->op = op;
  e->lhs = lhs;
  e->rhs = rhs;
  return e;
}

static Variable* MakeVar4(SimFixture& f, std::string_view name,
                          uint32_t width, uint64_t aval, uint64_t bval) {
  auto* var = f.ctx.CreateVariable(name, width);
  var->value = MakeLogic4Vec(f.arena, width);
  var->value.words[0].aval = aval;
  var->value.words[0].bval = bval;
  return var;
}

TEST(EvalOpXZ, WildcardEqLeftX) {
  SimFixture f;
  // §11.4.6: 4'bx001 ==? 4'b0001 → x (left X in non-wildcard position)
  MakeVar4(f, "wl", 4, 0b0001, 0b1000);  // bit3=x
  auto* b = f.ctx.CreateVariable("wr", 4);
  b->value = MakeLogic4VecVal(f.arena, 4, 0b0001);
  auto* expr = MakeBinary(f.arena, TokenKind::kEqEqQuestion,
                          MakeId(f.arena, "wl"), MakeId(f.arena, "wr"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.words[0].bval, 0u);  // result is X
}

// § binary_operator — ==? (wildcard equality)
TEST(SimA86, BinaryWildcardEq) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd5 ==? 8'd5);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

// § binary_operator — !=? (wildcard inequality)
TEST(SimA86, BinaryWildcardNeq) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic x;\n"
      "  initial x = (8'd5 !=? 8'd3);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

}  // namespace
