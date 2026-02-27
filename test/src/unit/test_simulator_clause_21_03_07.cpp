// §21.3.7: I/O error status

#include <cstdio>
#include <fstream>

#include "parser/ast.h"
#include "simulation/eval.h"

#include "fixture_simulator.h"
#include "builders_systask.h"

using namespace delta;

namespace {

TEST(SysTask, FerrorReturns0OnGoodFd) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_test_ferror.txt";
  {
    std::ofstream ofs(tmp);
    ofs << "ok";
  }

  auto* open_expr =
      MkSysCall(f.arena, "$fopen", {MkStr(f.arena, tmp), MkStr(f.arena, "r")});
  auto fd_val = EvalExpr(open_expr, f.ctx, f.arena);

  auto* dest = f.ctx.CreateVariable("errmsg", 256);
  dest->value = MakeLogic4VecVal(f.arena, 256, 0);

  auto* err_expr =
      MkSysCall(f.arena, "$ferror",
                {MkInt(f.arena, fd_val.ToUint64()), MkId(f.arena, "errmsg")});
  auto result = EvalExpr(err_expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);

  auto* close_expr =
      MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd_val.ToUint64())});
  EvalExpr(close_expr, f.ctx, f.arena);
  std::remove(tmp.c_str());
}

}  // namespace
