#include <fstream>

#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "helpers_parser_verify.h"
#include "simulator/evaluation.h"

using namespace delta;
namespace {

TEST(Section21, FopenFclose) {
  SimFixture f;

  std::string tmp_path = "/tmp/deltahdl_test_fopen.txt";
  {
    std::ofstream ofs(tmp_path);
    ofs << "hello\n";
  }
  auto* open_expr =
      MakeSysCall(f.arena, "$fopen",
                  {MkStr(f.arena, tmp_path.c_str()), MkStr(f.arena, "r")});
  auto fd_val = EvalExpr(open_expr, f.ctx, f.arena);
  EXPECT_NE(fd_val.ToUint64(), 0u);

  auto* close_expr =
      MakeSysCall(f.arena, "$fclose", {MakeInt(f.arena, fd_val.ToUint64())});
  EvalExpr(close_expr, f.ctx, f.arena);

  std::remove(tmp_path.c_str());
}

TEST(Section21, FopenInvalidFile) {
  SimFixture f;
  auto* expr = MakeSysCall(
      f.arena, "$fopen",
      {MkStr(f.arena, "/nonexistent/path/file.txt"), MkStr(f.arena, "r")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

}  // namespace
