// §21.3.6: Flushing output

#include <cstdio>

#include "builders_systask.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/eval.h"

using namespace delta;

namespace {

TEST(SysTask, FflushDoesNotCrash) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_test_fflush.txt";
  auto* open_expr =
      MkSysCall(f.arena, "$fopen", {MkStr(f.arena, tmp), MkStr(f.arena, "w")});
  auto fd_val = EvalExpr(open_expr, f.ctx, f.arena);

  auto* flush_expr =
      MkSysCall(f.arena, "$fflush", {MkInt(f.arena, fd_val.ToUint64())});
  auto result = EvalExpr(flush_expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 1u);

  auto* close_expr =
      MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd_val.ToUint64())});
  EvalExpr(close_expr, f.ctx, f.arena);
  std::remove(tmp.c_str());
}

}  // namespace
