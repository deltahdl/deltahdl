// §11.5.1: Vector bit-select and part-select addressing

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

static Expr *MakeInt(Arena &arena, uint64_t val) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->int_val = val;
  return e;
}

static Expr *MakeId(Arena &arena, std::string_view name) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kIdentifier;
  e->text = name;
  return e;
}

static Variable *MakeVar(EvalAdvFixture &f, std::string_view name,
                         uint32_t width, uint64_t val) {
  auto *var = f.ctx.CreateVariable(name, width);
  var->value = MakeLogic4VecVal(f.arena, width, val);
  return var;
}

namespace {

// ==========================================================================
// Part-select partial OOB — §11.5.1
// ==========================================================================
TEST(EvalAdv, PartSelectPartialOOB) {
  EvalAdvFixture f;
  // §11.5.1: v[6 +: 4] on 8-bit var → bits 6,7 valid, bits 8,9 OOB → X.
  MakeVar(f, "ov", 8, 0xFF);
  auto *sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "ov");
  sel->index = MakeInt(f.arena, 6);
  sel->index_end = MakeInt(f.arena, 4);
  sel->is_part_select_plus = true;
  auto result = EvalExpr(sel, f.ctx, f.arena);
  EXPECT_EQ(result.width, 4u);
  // Bits 0,1 (= original bits 6,7) should be 1 (known).
  EXPECT_EQ(result.words[0].aval & 0x3u, 0x3u);
  // Bits 2,3 (= original bits 8,9) should be X (bval set).
  EXPECT_NE(result.words[0].bval & 0xCu, 0u);
}

// ==========================================================================
// §7.4.5: X/Z address on array gives OOB (X) value
// ==========================================================================
TEST(EvalAdv, ArrayXZAddrReturnsX) {
  EvalAdvFixture f;
  // arr[0]=0x11, arr[1]=0x22 (8-bit elements).
  MakeVar(f, "arr4[0]", 8, 0x11);
  MakeVar(f, "arr4[1]", 8, 0x22);
  ArrayInfo info{};
  info.lo = 0;
  info.size = 2;
  info.elem_width = 8;
  f.ctx.RegisterArray("arr4", info);

  // arr4[x] — X address should return X.
  auto *sel = f.arena.Create<Expr>();
  sel->kind = ExprKind::kSelect;
  sel->base = MakeId(f.arena, "arr4");
  // Create an X-valued index.
  auto *idx = MakeInt(f.arena, 0);
  sel->index = idx;
  // Manually set bval to make it X.
  // Evaluate: since we can't directly set bval on a literal,
  // create a variable with X value and use it.
  auto *xvar = f.ctx.CreateVariable("xidx", 8);
  xvar->value = MakeLogic4Vec(f.arena, 8);
  xvar->value.words[0].aval = 1;
  xvar->value.words[0].bval = 1;  // aval=1, bval=1 → X
  sel->index = MakeId(f.arena, "xidx");

  auto result = EvalExpr(sel, f.ctx, f.arena);
  // X/Z address → result should be X (bval != 0).
  EXPECT_NE(result.nwords, 0u);
  EXPECT_NE(result.words[0].bval, 0u);
}

}  // namespace
