// §21.3.5: File positioning

#include <cstdio>
#include <fstream>

#include "builders_systask.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/eval.h"

using namespace delta;

namespace {

TEST(SysTask, FtellAndFseek) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_test_fseek.txt";
  {
    std::ofstream ofs(tmp);
    ofs << "abcdef";
  }

  auto* open_expr =
      MkSysCall(f.arena, "$fopen", {MkStr(f.arena, tmp), MkStr(f.arena, "r")});
  auto fd_val = EvalExpr(open_expr, f.ctx, f.arena);
  uint64_t fd = fd_val.ToUint64();

  auto* ftell_expr = MkSysCall(f.arena, "$ftell", {MkInt(f.arena, fd)});
  auto pos = EvalExpr(ftell_expr, f.ctx, f.arena);
  EXPECT_EQ(pos.ToUint64(), 0u);

  auto* fseek_expr =
      MkSysCall(f.arena, "$fseek",
                {MkInt(f.arena, fd), MkInt(f.arena, 3), MkInt(f.arena, 0)});
  EvalExpr(fseek_expr, f.ctx, f.arena);

  auto* ftell2_expr = MkSysCall(f.arena, "$ftell", {MkInt(f.arena, fd)});
  auto pos2 = EvalExpr(ftell2_expr, f.ctx, f.arena);
  EXPECT_EQ(pos2.ToUint64(), 3u);

  auto* fgetc_expr = MkSysCall(f.arena, "$fgetc", {MkInt(f.arena, fd)});
  auto ch = EvalExpr(fgetc_expr, f.ctx, f.arena);
  EXPECT_EQ(ch.ToUint64(), static_cast<uint64_t>('d'));

  auto* close_expr = MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd)});
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

  auto* open_expr =
      MkSysCall(f.arena, "$fopen", {MkStr(f.arena, tmp), MkStr(f.arena, "r")});
  auto fd_val = EvalExpr(open_expr, f.ctx, f.arena);
  uint64_t fd = fd_val.ToUint64();

  auto* fgetc_expr = MkSysCall(f.arena, "$fgetc", {MkInt(f.arena, fd)});
  auto ch = EvalExpr(fgetc_expr, f.ctx, f.arena);
  EXPECT_EQ(ch.ToUint64(), static_cast<uint64_t>('A'));

  auto* rewind_expr = MkSysCall(f.arena, "$rewind", {MkInt(f.arena, fd)});
  EvalExpr(rewind_expr, f.ctx, f.arena);

  auto* fgetc2_expr = MkSysCall(f.arena, "$fgetc", {MkInt(f.arena, fd)});
  auto ch2 = EvalExpr(fgetc2_expr, f.ctx, f.arena);
  EXPECT_EQ(ch2.ToUint64(), static_cast<uint64_t>('A'));

  auto* close_expr = MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd)});
  EvalExpr(close_expr, f.ctx, f.arena);
  std::remove(tmp.c_str());
}

static Expr* MakeStrLit(Arena& arena, std::string_view text) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kStringLiteral;
  // Store with surrounding quotes, matching parser convention.
  auto len = text.size() + 2;
  char* buf = static_cast<char*>(arena.Allocate(len + 1, 1));
  buf[0] = '"';
  for (size_t i = 0; i < text.size(); ++i) buf[i + 1] = text[i];
  buf[len - 1] = '"';
  buf[len] = '\0';
  e->text = std::string_view(buf, len);
  return e;
}

// ============================================================================
// §21.3 — $rewind(fd)
// ============================================================================
TEST(Section21, Rewind) {
  SimFixture f;
  std::string tmp_path = "/tmp/deltahdl_test_rewind.txt";
  {
    std::ofstream ofs(tmp_path);
    ofs << "ABCD";
  }
  auto* open_expr = MakeSysCall(
      f.arena, "$fopen",
      {MakeStrLit(f.arena, tmp_path.c_str()), MakeStrLit(f.arena, "r")});
  auto fd_val = EvalExpr(open_expr, f.ctx, f.arena);
  uint64_t fd = fd_val.ToUint64();
  ASSERT_NE(fd, 0u);

  // Read first char.
  auto* getc1 = MakeSysCall(f.arena, "$fgetc", {MakeInt(f.arena, fd)});
  auto ch1 = EvalExpr(getc1, f.ctx, f.arena);
  EXPECT_EQ(ch1.ToUint64(), static_cast<uint64_t>('A'));

  // Rewind.
  auto* rw = MakeSysCall(f.arena, "$rewind", {MakeInt(f.arena, fd)});
  EvalExpr(rw, f.ctx, f.arena);

  // Read first char again — should be 'A' after rewind.
  auto* getc2 = MakeSysCall(f.arena, "$fgetc", {MakeInt(f.arena, fd)});
  auto ch2 = EvalExpr(getc2, f.ctx, f.arena);
  EXPECT_EQ(ch2.ToUint64(), static_cast<uint64_t>('A'));

  auto* close_expr = MakeSysCall(f.arena, "$fclose", {MakeInt(f.arena, fd)});
  EvalExpr(close_expr, f.ctx, f.arena);
  std::remove(tmp_path.c_str());
}

}  // namespace
