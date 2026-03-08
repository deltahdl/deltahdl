#include <cstdio>
#include <fstream>

#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

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

TEST(Section21, Rewind) {
  SimFixture f;
  std::string tmp_path = "/tmp/deltahdl_test_rewind.txt";
  {
    std::ofstream ofs(tmp_path);
    ofs << "ABCD";
  }
  auto* open_expr =
      MakeSysCall(f.arena, "$fopen",
                  {MkStr(f.arena, tmp_path.c_str()), MkStr(f.arena, "r")});
  auto fd_val = EvalExpr(open_expr, f.ctx, f.arena);
  uint64_t fd = fd_val.ToUint64();
  ASSERT_NE(fd, 0u);

  auto* getc1 = MakeSysCall(f.arena, "$fgetc", {MakeInt(f.arena, fd)});
  auto ch1 = EvalExpr(getc1, f.ctx, f.arena);
  EXPECT_EQ(ch1.ToUint64(), static_cast<uint64_t>('A'));

  auto* rw = MakeSysCall(f.arena, "$rewind", {MakeInt(f.arena, fd)});
  EvalExpr(rw, f.ctx, f.arena);

  auto* getc2 = MakeSysCall(f.arena, "$fgetc", {MakeInt(f.arena, fd)});
  auto ch2 = EvalExpr(getc2, f.ctx, f.arena);
  EXPECT_EQ(ch2.ToUint64(), static_cast<uint64_t>('A'));

  auto* close_expr = MakeSysCall(f.arena, "$fclose", {MakeInt(f.arena, fd)});
  EvalExpr(close_expr, f.ctx, f.arena);
  std::remove(tmp_path.c_str());
}

}
