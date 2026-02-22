// §21.3.4: Reading data from a file

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
  for (size_t i = 0; i < text.size(); ++i) buf[i + 1] = text[i];
  buf[len - 1] = '"';
  buf[len] = '\0';
  e->text = std::string_view(buf, len);
  return e;
}

static Expr *MkId(Arena &arena, std::string_view name) {
  auto *e = arena.Create<Expr>();
  e->kind = ExprKind::kIdentifier;
  e->text = name;
  return e;
}

namespace {

TEST(SysTask, FgetsReadsLine) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_test_fgets.txt";
  {
    std::ofstream ofs(tmp);
    ofs << "hello world\n";
  }

  auto *open_expr =
      MkSysCall(f.arena, "$fopen", {MkStr(f.arena, tmp), MkStr(f.arena, "r")});
  auto fd_val = EvalExpr(open_expr, f.ctx, f.arena);
  EXPECT_NE(fd_val.ToUint64(), 0u);

  auto *dest = f.ctx.CreateVariable("line_var", 256);
  dest->value = MakeLogic4VecVal(f.arena, 256, 0);

  auto *fgets_expr =
      MkSysCall(f.arena, "$fgets",
                {MkId(f.arena, "line_var"), MkInt(f.arena, fd_val.ToUint64())});
  auto result = EvalExpr(fgets_expr, f.ctx, f.arena);
  EXPECT_GT(result.ToUint64(), 0u);

  auto *close_expr =
      MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd_val.ToUint64())});
  EvalExpr(close_expr, f.ctx, f.arena);
  std::remove(tmp.c_str());
}

TEST(SysTask, FgetcReadsChar) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_test_fgetc.txt";
  {
    std::ofstream ofs(tmp);
    ofs << "A";
  }

  auto *open_expr =
      MkSysCall(f.arena, "$fopen", {MkStr(f.arena, tmp), MkStr(f.arena, "r")});
  auto fd_val = EvalExpr(open_expr, f.ctx, f.arena);

  auto *expr =
      MkSysCall(f.arena, "$fgetc", {MkInt(f.arena, fd_val.ToUint64())});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), static_cast<uint64_t>('A'));

  auto *close_expr =
      MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd_val.ToUint64())});
  EvalExpr(close_expr, f.ctx, f.arena);
  std::remove(tmp.c_str());
}

TEST(SysTask, UngetcPushesBack) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_test_ungetc.txt";
  {
    std::ofstream ofs(tmp);
    ofs << "XY";
  }

  auto *open_expr =
      MkSysCall(f.arena, "$fopen", {MkStr(f.arena, tmp), MkStr(f.arena, "r")});
  auto fd_val = EvalExpr(open_expr, f.ctx, f.arena);
  uint64_t fd = fd_val.ToUint64();

  auto *fgetc1 = MkSysCall(f.arena, "$fgetc", {MkInt(f.arena, fd)});
  auto ch1 = EvalExpr(fgetc1, f.ctx, f.arena);
  EXPECT_EQ(ch1.ToUint64(), static_cast<uint64_t>('X'));

  auto *ungetc_expr = MkSysCall(
      f.arena, "$ungetc",
      {MkInt(f.arena, static_cast<uint64_t>('Z')), MkInt(f.arena, fd)});
  EvalExpr(ungetc_expr, f.ctx, f.arena);

  auto *fgetc2 = MkSysCall(f.arena, "$fgetc", {MkInt(f.arena, fd)});
  auto ch2 = EvalExpr(fgetc2, f.ctx, f.arena);
  EXPECT_EQ(ch2.ToUint64(), static_cast<uint64_t>('Z'));

  auto *close_expr = MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd)});
  EvalExpr(close_expr, f.ctx, f.arena);
  std::remove(tmp.c_str());
}

TEST(SysTask, FscanfReadsFormatted) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_test_fscanf.txt";
  {
    std::ofstream ofs(tmp);
    ofs << "42 ff";
  }

  auto *open_expr =
      MkSysCall(f.arena, "$fopen", {MkStr(f.arena, tmp), MkStr(f.arena, "r")});
  auto fd_val = EvalExpr(open_expr, f.ctx, f.arena);
  uint64_t fd = fd_val.ToUint64();

  auto *var_d = f.ctx.CreateVariable("v_dec", 32);
  var_d->value = MakeLogic4VecVal(f.arena, 32, 0);
  auto *var_h = f.ctx.CreateVariable("v_hex", 32);
  var_h->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto *fscanf_expr =
      MkSysCall(f.arena, "$fscanf",
                {MkInt(f.arena, fd), MkStr(f.arena, "%d %h"),
                 MkId(f.arena, "v_dec"), MkId(f.arena, "v_hex")});
  auto result = EvalExpr(fscanf_expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 2u);
  EXPECT_EQ(var_d->value.ToUint64(), 42u);
  EXPECT_EQ(var_h->value.ToUint64(), 0xFFu);

  auto *close_expr = MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd)});
  EvalExpr(close_expr, f.ctx, f.arena);
  std::remove(tmp.c_str());
}

TEST(SysTask, FreadReadsBinary) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_test_fread.txt";
  {
    std::ofstream ofs(tmp, std::ios::binary);
    char data[] = {'\xDE', '\xAD', '\xBE', '\xEF'};
    ofs.write(data, 4);
  }

  auto *open_expr =
      MkSysCall(f.arena, "$fopen", {MkStr(f.arena, tmp), MkStr(f.arena, "rb")});
  auto fd_val = EvalExpr(open_expr, f.ctx, f.arena);
  uint64_t fd = fd_val.ToUint64();

  auto *var = f.ctx.CreateVariable("v_read", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto *fread_expr = MkSysCall(f.arena, "$fread",
                               {MkId(f.arena, "v_read"), MkInt(f.arena, fd)});
  auto result = EvalExpr(fread_expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 4u);

  auto *close_expr = MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd)});
  EvalExpr(close_expr, f.ctx, f.arena);
  std::remove(tmp.c_str());
}

}  // namespace
