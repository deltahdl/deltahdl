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

// §11.8.4: Sign bit is x → sign-extending fills with x.
TEST(SignedXZ, SignBitXFillsWithX) {
  SimFixture f;
  // 4 bits: aval=0001, bval=1000 → bit 3 is x. Signed.
  auto* var = MakeVar4(f, "sx", 4, 0b0001, 0b1000);
  var->is_signed = true;
  auto* expr = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "sx"),
                          MakeInt(f.arena, 0));
  auto result = EvalExpr(expr, f.ctx, f.arena, 8);
  // Upper bits should have x (bval != 0).
  EXPECT_NE(result.words[0].bval & 0xF0u, 0u);
}

// §11.8.4: Sign bit is z → sign-extending fills with z.
TEST(SignedXZ, SignBitZFillsWithZ) {
  SimFixture f;
  // 4 bits: aval=1001, bval=1000 → bit 3 has both aval=1 and bval=1 → z.
  auto* var = MakeVar4(f, "sz", 4, 0b1001, 0b1000);
  var->is_signed = true;
  auto* expr = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "sz"),
                          MakeInt(f.arena, 0));
  auto result = EvalExpr(expr, f.ctx, f.arena, 8);
  // Upper bits should have x/z (bval != 0).
  EXPECT_NE(result.words[0].bval & 0xF0u, 0u);
}

// §11.8.4: Nonlogical operation with any x/z in signed value → all x result.
TEST(SignedXZ, NonlogicalOpWithXZYieldsX) {
  SimFixture f;
  // aval=5, bval=2 → bit 1 is x. Signed.
  auto* var = MakeVar4(f, "nx", 4, 0b0101, 0b0010);
  var->is_signed = true;
  MakeSignedVarAdv(f, "n1", 4, 1);
  auto* expr = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "nx"),
                          MakeId(f.arena, "n1"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  // Any bit with x in an arithmetic op propagates x.
  EXPECT_NE(result.words[0].bval, 0u);
}

// §11.8.4: Known signed value — no x/z fill, normal sign extension.
TEST(SignedXZ, KnownSignedNormalExtension) {
  SimFixture f;
  // -1 in 4 signed bits = 0xF (all ones, no x/z).
  MakeSignedVarAdv(f, "ok", 4, 0xF);
  auto* expr = MakeBinary(f.arena, TokenKind::kPlus, MakeId(f.arena, "ok"),
                          MakeInt(f.arena, 0));
  auto result = EvalExpr(expr, f.ctx, f.arena, 8);
  // Should have no x/z bits.
  EXPECT_EQ(result.words[0].bval, 0u);
}

}  // namespace
