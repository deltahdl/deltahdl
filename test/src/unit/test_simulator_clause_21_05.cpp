#include <fstream>

#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "helpers_parser_verify.h"
#include "simulator/evaluation.h"

using namespace delta;
namespace {

TEST(IoSystemTaskTest, WritememhBasic) {
  SimFixture f;
  std::string tmp_path = "/tmp/deltahdl_test_writememh.txt";

  auto* var = f.ctx.CreateVariable("wmem", 32);
  var->value = MakeLogic4VecVal(f.arena, 32, 0xFF);

  auto* expr =
      MakeSysCall(f.arena, "$writememh",
                  {MkStr(f.arena, tmp_path.c_str()), MakeId(f.arena, "wmem")});
  EvalExpr(expr, f.ctx, f.arena);

  std::ifstream ifs(tmp_path);
  std::string contents((std::istreambuf_iterator<char>(ifs)),
                       std::istreambuf_iterator<char>());
  EXPECT_FALSE(contents.empty());

  EXPECT_NE(contents.find("ff"), std::string::npos);

  std::remove(tmp_path.c_str());
}

TEST(IoSystemTaskTest, WritemembBasic) {
  SimFixture f;
  std::string tmp_path = "/tmp/deltahdl_test_writememb.txt";

  auto* var = f.ctx.CreateVariable("wbmem", 8);
  var->value = MakeLogic4VecVal(f.arena, 8, 0b10101010);

  auto* expr =
      MakeSysCall(f.arena, "$writememb",
                  {MkStr(f.arena, tmp_path.c_str()), MakeId(f.arena, "wbmem")});
  EvalExpr(expr, f.ctx, f.arena);

  std::ifstream ifs(tmp_path);
  std::string contents((std::istreambuf_iterator<char>(ifs)),
                       std::istreambuf_iterator<char>());
  EXPECT_FALSE(contents.empty());
  EXPECT_NE(contents.find("10101010"), std::string::npos);

  std::remove(tmp_path.c_str());
}

}  // namespace
