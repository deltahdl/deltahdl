// §21.3.8: Detecting EOF

#include <cstdio>
#include <fstream>

#include "builders_systask.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/eval.h"

using namespace delta;

namespace {

TEST(SysTask, FeofAtEnd) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_test_feof.txt";
  {
    std::ofstream ofs(tmp);
    ofs << "x";
  }

  auto* open_expr =
      MkSysCall(f.arena, "$fopen", {MkStr(f.arena, tmp), MkStr(f.arena, "r")});
  auto fd_val = EvalExpr(open_expr, f.ctx, f.arena);

  auto* fgetc_expr =
      MkSysCall(f.arena, "$fgetc", {MkInt(f.arena, fd_val.ToUint64())});
  EvalExpr(fgetc_expr, f.ctx, f.arena);

  auto* fgetc2_expr =
      MkSysCall(f.arena, "$fgetc", {MkInt(f.arena, fd_val.ToUint64())});
  auto eof_ch = EvalExpr(fgetc2_expr, f.ctx, f.arena);
  EXPECT_EQ(eof_ch.ToUint64(), 0xFFFFFFFF);

  auto* eof_expr =
      MkSysCall(f.arena, "$feof", {MkInt(f.arena, fd_val.ToUint64())});
  auto result = EvalExpr(eof_expr, f.ctx, f.arena);
  EXPECT_NE(result.ToUint64(), 0u);

  auto* close_expr =
      MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd_val.ToUint64())});
  EvalExpr(close_expr, f.ctx, f.arena);
  std::remove(tmp.c_str());
}

}  // namespace
