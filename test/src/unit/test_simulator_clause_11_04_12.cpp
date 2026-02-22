// §11.4.12: Concatenation operators

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/token.h"
#include "parser/ast.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h"

using namespace delta;

// Shared fixture for expression evaluation tests.
struct EvalOpFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

// Helper: build a simple integer literal Expr node.
static Expr *MakeInt(Arena &arena, uint64_t val) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->int_val = val;
  return e;
}

// Helper: build an identifier Expr node.
static Expr *MakeId(Arena &arena, std::string_view name) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kIdentifier;
  e->text = name;
  return e;
}

static Variable *MakeVar4(EvalOpFixture &f, std::string_view name,
                          uint32_t width, uint64_t aval, uint64_t bval) {
  auto *var = f.ctx.CreateVariable(name, width);
  var->value = MakeLogic4Vec(f.arena, width);
  var->value.words[0].aval = aval;
  var->value.words[0].bval = bval;
  return var;
}
namespace {

// ==========================================================================
// Replication ({n{expr}})
// ==========================================================================
TEST(EvalOp, Replicate3Times) {
  EvalOpFixture f;
  // {3{4'b1010}} = 12'b1010_1010_1010 = 0xAAA
  auto *var = f.ctx.CreateVariable("v", 4);
  var->value = MakeLogic4VecVal(f.arena, 4, 0xA);

  auto *rep = f.arena.Create<Expr>();
  rep->kind = ExprKind::kReplicate;
  rep->repeat_count = MakeInt(f.arena, 3);
  rep->elements.push_back(MakeId(f.arena, "v"));
  auto result = EvalExpr(rep, f.ctx, f.arena);
  // 3 * 4 = 12 bits, value = 0xAAA
  EXPECT_EQ(result.width, 12u);
  EXPECT_EQ(result.ToUint64(), 0xAAAu);
}

TEST(EvalOp, ReplicateOnce) {
  EvalOpFixture f;
  // {1{8'd42}} = 42
  auto *rep = f.arena.Create<Expr>();
  rep->kind = ExprKind::kReplicate;
  rep->repeat_count = MakeInt(f.arena, 1);
  rep->elements.push_back(MakeInt(f.arena, 42));
  auto result = EvalExpr(rep, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}

// ==========================================================================
// Concatenation bval propagation — §11.4.12
// ==========================================================================
TEST(EvalOp, ConcatXZPropagation) {
  EvalOpFixture f;
  // {4'b1x0z, 4'b0101} = 8'b1x0z_0101
  // a = 4'b1x0z: aval=0b1001, bval=0b0101
  MakeVar4(f, "ca", 4, 0b1001, 0b0101);
  // b = 4'b0101: aval=0b0101, bval=0b0000
  auto *bv = f.ctx.CreateVariable("cb", 4);
  bv->value = MakeLogic4VecVal(f.arena, 4, 0b0101);

  auto *concat = f.arena.Create<Expr>();
  concat->kind = ExprKind::kConcatenation;
  concat->elements.push_back(MakeId(f.arena, "ca"));
  concat->elements.push_back(MakeId(f.arena, "cb"));

  auto result = EvalExpr(concat, f.ctx, f.arena);
  EXPECT_EQ(result.width, 8u);
  // 8'b1x0z_0101:
  //   bit7=1, bit6=x, bit5=0, bit4=z, bit3=0, bit2=1, bit1=0, bit0=1
  //   aval: 1,0,0,1, 0,1,0,1 = 0b10010101 = 0x95
  //   bval: 0,1,0,1, 0,0,0,0 = 0b01010000 = 0x50
  EXPECT_EQ(result.words[0].aval, 0x95u);
  EXPECT_EQ(result.words[0].bval, 0x50u);
}

TEST(EvalOp, ReplicateXZPropagation) {
  EvalOpFixture f;
  // {2{4'b1x0z}} = 8'b1x0z_1x0z
  // 4'b1x0z: aval=0b1001, bval=0b0101
  MakeVar4(f, "rv", 4, 0b1001, 0b0101);

  auto *rep = f.arena.Create<Expr>();
  rep->kind = ExprKind::kReplicate;
  rep->repeat_count = MakeInt(f.arena, 2);
  rep->elements.push_back(MakeId(f.arena, "rv"));

  auto result = EvalExpr(rep, f.ctx, f.arena);
  EXPECT_EQ(result.width, 8u);
  // 8'b1x0z_1x0z:
  //   aval: 1001_1001 = 0x99
  //   bval: 0101_0101 = 0x55
  EXPECT_EQ(result.words[0].aval, 0x99u);
  EXPECT_EQ(result.words[0].bval, 0x55u);
}

}  // namespace
