// §20.17: Miscellaneous tasks and functions

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "parser/ast.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h"

using namespace delta;

struct SysTaskFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

static Expr *MkSysCall(Arena &arena, std::string_view name,
                       std::vector<Expr *> args) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kSystemCall;
  e->callee = name;
  e->args = std::move(args);
  return e;
}

static Expr *MkStr(Arena &arena, std::string_view text) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kStringLiteral;
  auto len = text.size() + 2;
  char *buf = static_cast<char *>(arena.Allocate(len + 1, 1));
  buf[0] = '"';
  for (size_t i = 0; i < text.size(); ++i)
    buf[i + 1] = text[i];
  buf[len - 1] = '"';
  buf[len] = '\0';
  e->text = std::string_view(buf, len);
  return e;
}

namespace {

TEST(SysTask, SystemReturnsExitCode) {
  SysTaskFixture f;
  auto *expr = MkSysCall(f.arena, "$system", {MkStr(f.arena, "true")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

TEST(SysTask, SystemFailureExitCode) {
  SysTaskFixture f;
  auto *expr = MkSysCall(f.arena, "$system", {MkStr(f.arena, "false")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_NE(result.ToUint64(), 0u);
}

TEST(SysTask, StacktraceDoesNotCrash) {
  SysTaskFixture f;
  auto *expr = MkSysCall(f.arena, "$stacktrace", {});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);
}

} // namespace
