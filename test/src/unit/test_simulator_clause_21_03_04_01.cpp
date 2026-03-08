#include <fstream>

#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "helpers_parser_verify.h"
#include "simulator/evaluation.h"

using namespace delta;
namespace {

TEST(Section21, Ungetc) {
  SimFixture f;
  std::string tmp_path = "/tmp/deltahdl_test_ungetc.txt";
  {
    std::ofstream ofs(tmp_path);
    ofs << "XY";
  }
  auto* open_expr =
      MakeSysCall(f.arena, "$fopen",
                  {MkStr(f.arena, tmp_path.c_str()), MkStr(f.arena, "r")});
  auto fd_val = EvalExpr(open_expr, f.ctx, f.arena);
  uint64_t fd = fd_val.ToUint64();
  ASSERT_NE(fd, 0u);

  auto* ug = MakeSysCall(f.arena, "$ungetc",
                         {MakeInt(f.arena, 'Z'), MakeInt(f.arena, fd)});
  EvalExpr(ug, f.ctx, f.arena);

  auto* getc1 = MakeSysCall(f.arena, "$fgetc", {MakeInt(f.arena, fd)});
  auto ch1 = EvalExpr(getc1, f.ctx, f.arena);
  EXPECT_EQ(ch1.ToUint64(), static_cast<uint64_t>('Z'));

  auto* getc2 = MakeSysCall(f.arena, "$fgetc", {MakeInt(f.arena, fd)});
  auto ch2 = EvalExpr(getc2, f.ctx, f.arena);
  EXPECT_EQ(ch2.ToUint64(), static_cast<uint64_t>('X'));

  auto* close_expr = MakeSysCall(f.arena, "$fclose", {MakeInt(f.arena, fd)});
  EvalExpr(close_expr, f.ctx, f.arena);
  std::remove(tmp_path.c_str());
}

}  // namespace
