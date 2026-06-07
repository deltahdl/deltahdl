#include <cstdio>
#include <fstream>

#include "builders_systask.h"
#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/evaluation.h"

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

// §21.3.8: EOF is reported only after it "has previously been detected
// reading" -- consuming the last byte leaves the file pointer at the end, but
// because no read has yet failed, $feof still reports zero. This distinguishes
// the detected-EOF flag from mere positioning at end of file.
TEST(SysTask, FeofZeroAtEndBeforeFailedRead) {
  SysTaskFixture f;
  std::string tmp = "/tmp/deltahdl_test_feof_atend.txt";
  {
    std::ofstream ofs(tmp);
    ofs << "x";
  }

  auto* open_expr =
      MkSysCall(f.arena, "$fopen", {MkStr(f.arena, tmp), MkStr(f.arena, "r")});
  auto fd_val = EvalExpr(open_expr, f.ctx, f.arena);

  // Read the single byte successfully; this does not yet trigger EOF.
  auto* fgetc_expr =
      MkSysCall(f.arena, "$fgetc", {MkInt(f.arena, fd_val.ToUint64())});
  auto ch = EvalExpr(fgetc_expr, f.ctx, f.arena);
  EXPECT_EQ(ch.ToUint64(), static_cast<uint64_t>('x'));

  auto* eof_expr =
      MkSysCall(f.arena, "$feof", {MkInt(f.arena, fd_val.ToUint64())});
  auto result = EvalExpr(eof_expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);

  auto* close_expr =
      MkSysCall(f.arena, "$fclose", {MkInt(f.arena, fd_val.ToUint64())});
  EvalExpr(close_expr, f.ctx, f.arena);
  std::remove(tmp.c_str());
}

}
