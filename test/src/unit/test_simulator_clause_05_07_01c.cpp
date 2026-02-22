// §5.7.1: Integer literal constants

#include <gtest/gtest.h>
#include <cstring>
#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/token.h"
#include "parser/ast.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h"  // StructTypeInfo, StructFieldInfo

using namespace delta;

// Shared fixture for advanced expression evaluation tests (§11 phases 22+).
struct EvalAdvFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static Expr* MakeSizedLiteral(Arena& arena, std::string_view text,
                              uint64_t val) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->text = text;
  e->int_val = val;
  return e;
}
namespace {

TEST(EvalAdv, SignedBaseLiteralIsSigned) {
  EvalAdvFixture f;
  // §11.3.3: 4'sd3 should produce is_signed=true on the Logic4Vec.
  auto* lit = MakeSizedLiteral(f.arena, "4'sd3", 3);
  auto result = EvalExpr(lit, f.ctx, f.arena);
  EXPECT_TRUE(result.is_signed);
  EXPECT_EQ(result.width, 4u);
  EXPECT_EQ(result.ToUint64(), 3u);
}

TEST(EvalAdv, UnsignedBaseLiteralNotSigned) {
  EvalAdvFixture f;
  // 4'd3 should produce is_signed=false.
  auto* lit = MakeSizedLiteral(f.arena, "4'd3", 3);
  auto result = EvalExpr(lit, f.ctx, f.arena);
  EXPECT_FALSE(result.is_signed);
  EXPECT_EQ(result.width, 4u);
  EXPECT_EQ(result.ToUint64(), 3u);
}

TEST(EvalAdv, SignedHexLiteralIsSigned) {
  EvalAdvFixture f;
  // 8'shFF should produce is_signed=true.
  auto* lit = MakeSizedLiteral(f.arena, "8'shFF", 0xFF);
  auto result = EvalExpr(lit, f.ctx, f.arena);
  EXPECT_TRUE(result.is_signed);
  EXPECT_EQ(result.width, 8u);
  EXPECT_EQ(result.ToUint64(), 0xFFu);
}

}  // namespace
