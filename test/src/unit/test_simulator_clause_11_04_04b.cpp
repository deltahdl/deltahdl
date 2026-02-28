// §11.4.4: Relational operators

#include <cstring>

#include "builders_ast.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/eval.h"
#include "simulator/sim_context.h"  // StructTypeInfo, StructFieldInfo

using namespace delta;

namespace {

// ==========================================================================
// Signed comparison — §11.4.4, §11.4.5, §11.8.1
// ==========================================================================
TEST(EvalAdv, SignedLtNeg) {
  SimFixture f;
  MakeSignedVarAdv(f, "sa", 8, 0xFF);
  MakeSignedVarAdv(f, "sb", 8, 0x01);
  auto* expr = MakeBinary(f.arena, TokenKind::kLt, MakeId(f.arena, "sa"),
                          MakeId(f.arena, "sb"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalAdv, SignedGtNeg) {
  SimFixture f;
  MakeSignedVarAdv(f, "sa", 8, 0x01);
  MakeSignedVarAdv(f, "sb", 8, 0xFF);
  auto* expr = MakeBinary(f.arena, TokenKind::kGt, MakeId(f.arena, "sa"),
                          MakeId(f.arena, "sb"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u);
}

TEST(EvalAdv, UnsignedLtUnchanged) {
  SimFixture f;
  auto* a = MakeVar(f, "ua", 8, 0xFF);
  (void)a;
  auto* b = MakeVar(f, "ub", 8, 0x01);
  (void)b;
  auto* expr = MakeBinary(f.arena, TokenKind::kLt, MakeId(f.arena, "ua"),
                          MakeId(f.arena, "ub"));
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

}  // namespace
