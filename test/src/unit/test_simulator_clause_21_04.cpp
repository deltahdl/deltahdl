// §21.4: Loading memory array data from a file

#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

// ============================================================================
// §21.4 — $readmemh, $readmemb
// ============================================================================
TEST(Section21, ReadmemhBasic) {
  SimFixture f;
  std::string tmp_path = "/tmp/deltahdl_test_readmemh.txt";
  {
    std::ofstream ofs(tmp_path);
    ofs << "0A\n14\n1E\n";
  }

  // Create an array variable (simulate as a 32-bit var for simplicity;
  // the implementation stores values to array indices via the context).
  auto* arr = f.ctx.CreateVariable("mem", 32);
  arr->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* expr =
      MakeSysCall(f.arena, "$readmemh",
                  {MkStr(f.arena, tmp_path.c_str()), MakeId(f.arena, "mem")});
  EvalExpr(expr, f.ctx, f.arena);

  // The first value (0x0A = 10) should be in mem[0] = "mem".
  // For a flat variable, readmemh stores the first value.
  EXPECT_EQ(arr->value.ToUint64(), 0x0Au);

  std::remove(tmp_path.c_str());
}

TEST(Section21, ReadmembBasic) {
  SimFixture f;
  std::string tmp_path = "/tmp/deltahdl_test_readmemb.txt";
  {
    std::ofstream ofs(tmp_path);
    ofs << "1010\n0110\n";
  }

  auto* arr = f.ctx.CreateVariable("bmem", 32);
  arr->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* expr =
      MakeSysCall(f.arena, "$readmemb",
                  {MkStr(f.arena, tmp_path.c_str()), MakeId(f.arena, "bmem")});
  EvalExpr(expr, f.ctx, f.arena);

  // First value: 1010 binary = 10 decimal.
  EXPECT_EQ(arr->value.ToUint64(), 0b1010u);

  std::remove(tmp_path.c_str());
}

}  // namespace
