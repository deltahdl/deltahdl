// §21.3.5: File positioning

#include <gtest/gtest.h>

#include <cstdio>
#include <fstream>
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
  for (size_t i = 0; i < text.size(); ++i)
    buf[i + 1] = text[i];
  buf[len - 1] = '"';
  buf[len] = '\0';
  e->text = std::string_view(buf, len);
  return e;
}

namespace {

TEST(SysTask, FtellAndFseek) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_test_fseek.txt";
  {
    std::ofstream ofs(tmp);
    ofs << "abcdef";
  }

  auto *open_expr =
      MkSysCall(f.arena, "$fopen", {MkStr(f.arena, tmp), MkStr(f.arena, "r")});
  auto fd_val = EvalExpr(open_expr, f.ctx, f.arena);
  uint64_t fd = fd_val.ToUint64();

  auto *ftell_expr = MkSysCall(f.arena, "$ftell", {MkInt(f.arena, fd)});
  auto pos = EvalExpr(ftell_expr, f.ctx, f.arena);
  EXPECT_EQ(pos.ToUint64(), 0u);

  auto *fseek_expr =
      MkSysCall(f.arena, "$fseek",
                {MkInt(f.arena, fd), MkInt(f.arena, 3), MkInt(f.arena, 0)});
  EvalExpr(fseek_expr, f.ctx, f.arena);

  auto *ftell2_expr = MkSysCall(f.arena, "$ftell", {MkInt(f.arena, fd)});
  auto pos2 = EvalExpr(ftell2_expr, f.ctx, f.arena);
  EXPECT_EQ(pos2.ToUint64(), 3u);

  auto *fgetc_expr = MkSysCall(f.arena, "$fgetc", {MkInt(f.arena, fd)});
  auto ch = EvalExpr(fgetc_expr, f.ctx, f.arena);
  EXPECT_EQ(ch.ToUint64(), static_cast<uint64_t>('d'));

  auto *close_expr = MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd)});
  EvalExpr(close_expr, f.ctx, f.arena);
  std::remove(tmp.c_str());
}

TEST(SysTask, RewindResetsPosition) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_test_rewind.txt";
  {
    std::ofstream ofs(tmp);
    ofs << "ABCDEF";
  }

  auto *open_expr =
      MkSysCall(f.arena, "$fopen", {MkStr(f.arena, tmp), MkStr(f.arena, "r")});
  auto fd_val = EvalExpr(open_expr, f.ctx, f.arena);
  uint64_t fd = fd_val.ToUint64();

  auto *fgetc_expr = MkSysCall(f.arena, "$fgetc", {MkInt(f.arena, fd)});
  auto ch = EvalExpr(fgetc_expr, f.ctx, f.arena);
  EXPECT_EQ(ch.ToUint64(), static_cast<uint64_t>('A'));

  auto *rewind_expr = MkSysCall(f.arena, "$rewind", {MkInt(f.arena, fd)});
  EvalExpr(rewind_expr, f.ctx, f.arena);

  auto *fgetc2_expr = MkSysCall(f.arena, "$fgetc", {MkInt(f.arena, fd)});
  auto ch2 = EvalExpr(fgetc2_expr, f.ctx, f.arena);
  EXPECT_EQ(ch2.ToUint64(), static_cast<uint64_t>('A'));

  auto *close_expr = MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd)});
  EvalExpr(close_expr, f.ctx, f.arena);
  std::remove(tmp.c_str());
}

} // namespace
