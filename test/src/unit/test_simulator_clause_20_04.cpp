// §20.4: Timescale system tasks and system functions


#include "parser/ast.h"
#include "simulation/eval.h"

#include "fixture_simulator.h"

using namespace delta;

static Expr* MkSysCall(Arena& arena, std::string_view name,
                       std::vector<Expr*> args) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kSystemCall;
  e->callee = name;
  e->args = std::move(args);
  return e;
}

static Expr* MkInt(Arena& arena, uint64_t val) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->int_val = val;
  return e;
}

static Expr* MkStr(Arena& arena, std::string_view text) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kStringLiteral;
  auto len = text.size() + 2;
  char* buf = static_cast<char*>(arena.Allocate(len + 1, 1));
  buf[0] = '"';
  for (size_t i = 0; i < text.size(); ++i) buf[i + 1] = text[i];
  buf[len - 1] = '"';
  buf[len] = '\0';
  e->text = std::string_view(buf, len);
  return e;
}

namespace {

TEST(SysTask, PrinttimescaleDoesNotCrash) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$printtimescale", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
}

TEST(SysTask, TimeformatDoesNotCrash) {
  SysTaskFixture f;
  auto* expr = MkSysCall(f.arena, "$timeformat",
                         {MkInt(f.arena, 0), MkInt(f.arena, 0),
                          MkStr(f.arena, " ns"), MkInt(f.arena, 10)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
}

}  // namespace
