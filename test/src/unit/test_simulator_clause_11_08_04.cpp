#include "builders_ast.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"
#include "simulator/statement_assign.h"

using namespace delta;

namespace {

static Variable* MakeVar4(SimFixture& f, std::string_view name, uint32_t width,
                          uint64_t aval, uint64_t bval) {
  auto* var = f.ctx.CreateVariable(name, width);
  var->value = MakeLogic4Vec(f.arena, width);
  var->value.words[0].aval = aval;
  var->value.words[0].bval = bval;
  return var;
}

TEST(SignedXZ, SignBitXFillsWithX) {
  SimFixture f;

  auto* var = MakeVar4(f, "sx", 4, 0b0001, 0b1000);
  var->is_signed = true;
  auto* expr = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "sx"),
                          MakeInt(f.arena, 0));
  auto result = EvalExpr(expr, f.ctx, f.arena, 8);

  EXPECT_NE(result.words[0].bval & 0xF0u, 0u);
}

TEST(SignedXZ, SignBitZFillsWithZ) {
  SimFixture f;

  auto* var = MakeVar4(f, "sz", 4, 0b1001, 0b1000);
  var->is_signed = true;
  auto* expr = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "sz"),
                          MakeInt(f.arena, 0));
  auto result = EvalExpr(expr, f.ctx, f.arena, 8);

  EXPECT_NE(result.words[0].bval & 0xF0u, 0u);
}

TEST(SignedXZ, KnownSignedNormalExtension) {
  SimFixture f;

  MakeSignedVarAdv(f, "ok", 4, 0xF);
  auto* expr = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "ok"),
                          MakeInt(f.arena, 0));
  auto result = EvalExpr(expr, f.ctx, f.arena, 8);

  EXPECT_EQ(result.words[0].bval, 0u);
}

TEST(SignedXZ, TernarySignExtXFillsWithX) {
  SimFixture f;

  auto* var = MakeVar4(f, "tx", 4, 0b1001, 0b1000);
  var->is_signed = true;

  MakeSignedVarAdv(f, "fv", 8, 0);
  auto* tern = f.arena.Create<Expr>();
  tern->kind = ExprKind::kTernary;
  tern->condition = MakeInt(f.arena, 1);
  tern->true_expr = MakeId(f.arena, "tx");
  tern->false_expr = MakeId(f.arena, "fv");
  auto result = EvalExpr(tern, f.ctx, f.arena);

  EXPECT_EQ(result.words[0].aval & 0xF0u, 0xF0u);
  EXPECT_EQ(result.words[0].bval & 0xF0u, 0xF0u);
}

TEST(SignedXZ, TernarySignExtZFillsWithZ) {
  SimFixture f;

  auto* var = MakeVar4(f, "tz", 4, 0b0001, 0b1000);
  var->is_signed = true;
  MakeSignedVarAdv(f, "fv2", 8, 0);
  auto* tern = f.arena.Create<Expr>();
  tern->kind = ExprKind::kTernary;
  tern->condition = MakeInt(f.arena, 1);
  tern->true_expr = MakeId(f.arena, "tz");
  tern->false_expr = MakeId(f.arena, "fv2");
  auto result = EvalExpr(tern, f.ctx, f.arena);

  EXPECT_EQ(result.words[0].aval & 0xF0u, 0x00u);
  EXPECT_EQ(result.words[0].bval & 0xF0u, 0xF0u);
}

// Claims 1 & 2 are also carried by the assignment-widening path
// (ResizeToWidth), distinct from the ternary/extension path (ExtendVec)
// exercised above. Drive that production helper directly so the resize
// sign-fill is observed there too.
TEST(SignedXZ, ResizeWidensSignBitXFillsWithX) {
  SimFixture f;

  auto val = MakeLogic4Vec(f.arena, 4);
  val.is_signed = true;
  val.words[0].aval = 0b1000;  // sign bit a=1, b=1 -> x
  val.words[0].bval = 0b1000;
  auto result = ResizeToWidth(val, 8, f.arena);

  EXPECT_EQ(result.words[0].aval & 0xF0u, 0xF0u);
  EXPECT_EQ(result.words[0].bval & 0xF0u, 0xF0u);
}

TEST(SignedXZ, ResizeWidensSignBitZFillsWithZ) {
  SimFixture f;

  auto val = MakeLogic4Vec(f.arena, 4);
  val.is_signed = true;
  val.words[0].aval = 0b0000;  // sign bit a=0, b=1 -> z
  val.words[0].bval = 0b1000;
  auto result = ResizeToWidth(val, 8, f.arena);

  EXPECT_EQ(result.words[0].aval & 0xF0u, 0x00u);
  EXPECT_EQ(result.words[0].bval & 0xF0u, 0xF0u);
}

TEST(SignedXZ, ArithmeticResultIsEntirelyX) {
  SimFixture f;

  auto* var = MakeVar4(f, "ax", 4, 0b0101, 0b0010);
  var->is_signed = true;
  MakeSignedVarAdv(f, "a1", 4, 1);
  auto* expr = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "ax"),
                          MakeId(f.arena, "a1"));
  auto result = EvalExpr(expr, f.ctx, f.arena);

  uint64_t mask = (uint64_t{1} << result.width) - 1;
  EXPECT_EQ(result.words[0].aval & mask, mask);
  EXPECT_EQ(result.words[0].bval & mask, mask);
}

TEST(SignedXZ, SubtractionWithXZYieldsAllX) {
  SimFixture f;

  auto* var = MakeVar4(f, "sx", 4, 0b0101, 0b0010);
  var->is_signed = true;
  MakeSignedVarAdv(f, "s1", 4, 1);
  auto* expr = MakeBinary(f.arena, TokenKind::kMinus, MakeId(f.arena, "sx"),
                          MakeId(f.arena, "s1"));
  auto result = EvalExpr(expr, f.ctx, f.arena);

  uint64_t mask = (uint64_t{1} << result.width) - 1;
  EXPECT_EQ(result.words[0].aval & mask, mask);
  EXPECT_EQ(result.words[0].bval & mask, mask);
}

TEST(SignedXZ, MultiplicationWithXZYieldsAllX) {
  SimFixture f;

  auto* var = MakeVar4(f, "mx", 4, 0b0101, 0b0010);
  var->is_signed = true;
  MakeSignedVarAdv(f, "m1", 4, 2);
  auto* expr = MakeBinary(f.arena, TokenKind::kStar, MakeId(f.arena, "mx"),
                          MakeId(f.arena, "m1"));
  auto result = EvalExpr(expr, f.ctx, f.arena);

  uint64_t mask = (uint64_t{1} << result.width) - 1;
  EXPECT_EQ(result.words[0].aval & mask, mask);
  EXPECT_EQ(result.words[0].bval & mask, mask);
}

TEST(SignedXZ, DivisionWithXZYieldsAllX) {
  SimFixture f;

  auto* var = MakeVar4(f, "dx", 4, 0b0101, 0b0010);
  var->is_signed = true;
  MakeSignedVarAdv(f, "d1", 4, 1);
  auto* expr = MakeBinary(f.arena, TokenKind::kSlash, MakeId(f.arena, "dx"),
                          MakeId(f.arena, "d1"));
  auto result = EvalExpr(expr, f.ctx, f.arena);

  uint64_t mask = (uint64_t{1} << result.width) - 1;
  EXPECT_EQ(result.words[0].aval & mask, mask);
  EXPECT_EQ(result.words[0].bval & mask, mask);
}

TEST(SignedXZ, ModulusWithXZYieldsAllX) {
  SimFixture f;

  auto* var = MakeVar4(f, "px", 4, 0b0101, 0b0010);
  var->is_signed = true;
  MakeSignedVarAdv(f, "p1", 4, 3);
  auto* expr = MakeBinary(f.arena, TokenKind::kPercent, MakeId(f.arena, "px"),
                          MakeId(f.arena, "p1"));
  auto result = EvalExpr(expr, f.ctx, f.arena);

  uint64_t mask = (uint64_t{1} << result.width) - 1;
  EXPECT_EQ(result.words[0].aval & mask, mask);
  EXPECT_EQ(result.words[0].bval & mask, mask);
}

TEST(SignedXZ, PowerWithXZYieldsAllX) {
  SimFixture f;

  auto* var = MakeVar4(f, "ex", 4, 0b0101, 0b0010);
  var->is_signed = true;
  MakeSignedVarAdv(f, "e1", 4, 2);
  auto* expr = MakeBinary(f.arena, TokenKind::kPower, MakeId(f.arena, "ex"),
                          MakeId(f.arena, "e1"));
  auto result = EvalExpr(expr, f.ctx, f.arena);

  uint64_t mask = (uint64_t{1} << result.width) - 1;
  EXPECT_EQ(result.words[0].aval & mask, mask);
  EXPECT_EQ(result.words[0].bval & mask, mask);
}

TEST(SignedXZ, UnaryMinusWithXZYieldsAllX) {
  SimFixture f;

  auto* var = MakeVar4(f, "ux", 4, 0b0101, 0b0010);
  var->is_signed = true;
  auto* expr = MakeUnary(f.arena, TokenKind::kMinus, MakeId(f.arena, "ux"));
  auto result = EvalExpr(expr, f.ctx, f.arena);

  uint64_t mask = (uint64_t{1} << result.width) - 1;
  EXPECT_EQ(result.words[0].aval & mask, mask);
  EXPECT_EQ(result.words[0].bval & mask, mask);
}

TEST(SignedXZ, RelationalWithSignedXZYieldsX) {
  SimFixture f;

  auto* var = MakeVar4(f, "rx", 4, 0b0101, 0b0010);
  var->is_signed = true;
  MakeSignedVarAdv(f, "r1", 4, 1);
  auto* expr = MakeBinary(f.arena, TokenKind::kLt, MakeId(f.arena, "rx"),
                          MakeId(f.arena, "r1"));
  auto result = EvalExpr(expr, f.ctx, f.arena);

  EXPECT_EQ(result.width, 1u);
  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(SignedXZ, NonlogicalOpResultPreservesSignedType) {
  SimFixture f;

  auto* var = MakeVar4(f, "ts", 4, 0b0101, 0b0010);
  var->is_signed = true;
  MakeSignedVarAdv(f, "t1", 4, 1);
  auto* expr = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "ts"),
                          MakeId(f.arena, "t1"));
  auto result = EvalExpr(expr, f.ctx, f.arena);

  EXPECT_TRUE(result.is_signed);
}

TEST(SignedXZ, XInLowBitStillYieldsAllX) {
  SimFixture f;

  auto* var = MakeVar4(f, "lx", 4, 0b0001, 0b0001);
  var->is_signed = true;
  MakeSignedVarAdv(f, "l1", 4, 1);
  auto* expr = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "lx"),
                          MakeId(f.arena, "l1"));
  auto result = EvalExpr(expr, f.ctx, f.arena);

  uint64_t mask = (uint64_t{1} << result.width) - 1;
  EXPECT_EQ(result.words[0].aval & mask, mask);
  EXPECT_EQ(result.words[0].bval & mask, mask);
}

TEST(SignedXZ, ZInLowBitStillYieldsAllX) {
  SimFixture f;

  auto* var = MakeVar4(f, "lz", 4, 0b0000, 0b0001);
  var->is_signed = true;
  MakeSignedVarAdv(f, "lz1", 4, 1);
  auto* expr = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "lz"),
                          MakeId(f.arena, "lz1"));
  auto result = EvalExpr(expr, f.ctx, f.arena);

  uint64_t mask = (uint64_t{1} << result.width) - 1;
  EXPECT_EQ(result.words[0].aval & mask, mask);
  EXPECT_EQ(result.words[0].bval & mask, mask);
}

}  // namespace
