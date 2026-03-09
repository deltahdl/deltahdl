#include "builders_ast.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"

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

TEST(SignedXZ, NonlogicalOpWithXZYieldsX) {
  SimFixture f;

  auto* var = MakeVar4(f, "nx", 4, 0b0101, 0b0010);
  var->is_signed = true;
  MakeSignedVarAdv(f, "n1", 4, 1);
  auto* expr = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "nx"),
                          MakeId(f.arena, "n1"));
  auto result = EvalExpr(expr, f.ctx, f.arena);

  EXPECT_NE(result.words[0].bval, 0u);
}

TEST(SignedXZ, KnownSignedNormalExtension) {
  SimFixture f;

  MakeSignedVarAdv(f, "ok", 4, 0xF);
  auto* expr = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "ok"),
                          MakeInt(f.arena, 0));
  auto result = EvalExpr(expr, f.ctx, f.arena, 8);

  EXPECT_EQ(result.words[0].bval, 0u);
}

}  // namespace
