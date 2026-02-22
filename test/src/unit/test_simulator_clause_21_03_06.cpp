// §21.3.6: Flushing output

#include <gtest/gtest.h>

#include <cstdio>
#include <string>

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

static Expr *MkInt(Arena &arena, uint64_t val) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->int_val = val;
  return e;
}

static Expr *MkStr(Arena &arena, std::string_view text) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kStringLiteral;
  auto len = text.size() + 2;
  char *buf = static_cast<char *>(arena.Allocate(len + 1, 1));
  buf[0] = '"';
  for (size_t i = 0; i < text.size(); ++i) buf[i + 1] = text[i];
  buf[len - 1] = '"';
  buf[len] = '\0';
  e->text = std::string_view(buf, len);
  return e;
}

namespace {

TEST(SysTask, FflushDoesNotCrash) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_test_fflush.txt";
  auto *open_expr =
      MkSysCall(f.arena, "$fopen", {MkStr(f.arena, tmp), MkStr(f.arena, "w")});
  auto fd_val = EvalExpr(open_expr, f.ctx, f.arena);

  auto *flush_expr =
      MkSysCall(f.arena, "$fflush", {MkInt(f.arena, fd_val.ToUint64())});
  auto result = EvalExpr(flush_expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);

  auto *close_expr =
      MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd_val.ToUint64())});
  EvalExpr(close_expr, f.ctx, f.arena);
  std::remove(tmp.c_str());
}

}  // namespace
