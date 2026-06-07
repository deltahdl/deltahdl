#include <cstdio>
#include <fstream>

#include "builders_systask.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

// §21.3.7: when the most recent operation did not result in an error, $ferror
// returns an error code of zero and the str argument shall be cleared. A
// previously populated string variable must not be left holding stale data
// after a successful $ferror call.
TEST(SysTask, FerrorClearsStrWhenNoError) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_test_ferror_clear.txt";
  {
    std::ofstream ofs(tmp);
    ofs << "ok";
  }

  auto* open_expr =
      MkSysCall(f.arena, "$fopen", {MkStr(f.arena, tmp), MkStr(f.arena, "r")});
  auto fd_val = EvalExpr(open_expr, f.ctx, f.arena);

  // Seed the string variable with a non-zero value so the clearing behavior is
  // observable.
  auto* dest = f.ctx.CreateVariable("errmsg", 256);
  dest->value = MakeLogic4VecVal(f.arena, 256, 0xDEADBEEFull);
  ASSERT_NE(dest->value.ToUint64(), 0u);

  auto* err_expr =
      MkSysCall(f.arena, "$ferror",
                {MkInt(f.arena, fd_val.ToUint64()), MkId(f.arena, "errmsg")});
  auto result = EvalExpr(err_expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
  EXPECT_EQ(dest->value.ToUint64(), 0u);

  auto* close_expr =
      MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd_val.ToUint64())});
  EvalExpr(close_expr, f.ctx, f.arena);
  std::remove(tmp.c_str());
}

// §21.3.7: when the most recent file I/O operation fails, $ferror returns a
// non-zero error code and writes a textual description of the error into str.
TEST(SysTask, FerrorWritesDescriptionOnError) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_test_ferror_err.txt";

  // Open write-only, then attempt a read: reading from a write-only stream sets
  // the stream's error indicator.
  auto* open_expr =
      MkSysCall(f.arena, "$fopen", {MkStr(f.arena, tmp), MkStr(f.arena, "w")});
  auto fd_val = EvalExpr(open_expr, f.ctx, f.arena);

  auto* read_expr =
      MkSysCall(f.arena, "$fgetc", {MkInt(f.arena, fd_val.ToUint64())});
  EvalExpr(read_expr, f.ctx, f.arena);

  auto* dest = f.ctx.CreateVariable("errmsg", 640);
  dest->value = MakeLogic4VecVal(f.arena, 640, 0);

  auto* err_expr =
      MkSysCall(f.arena, "$ferror",
                {MkInt(f.arena, fd_val.ToUint64()), MkId(f.arena, "errmsg")});
  auto result = EvalExpr(err_expr, f.ctx, f.arena);
  EXPECT_NE(result.ToUint64(), 0u);
  // A description was written into the string variable.
  EXPECT_NE(dest->value.ToUint64(), 0u);

  auto* close_expr =
      MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd_val.ToUint64())});
  EvalExpr(close_expr, f.ctx, f.arena);
  std::remove(tmp.c_str());
}

}  // namespace
