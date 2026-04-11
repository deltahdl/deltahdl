#include <cstdint>
#include <vector>

#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/dpi.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(Dpi, CallFunction) {
  DpiContext ctx;
  DpiFunction func;
  func.c_name = "c_add";
  func.sv_name = "sv_add";
  func.impl = [](const std::vector<uint64_t>& args) -> uint64_t {
    return args[0] + args[1];
  };
  ctx.RegisterImport(func);

  auto result = ctx.Call("sv_add", {10, 20});
  EXPECT_EQ(result, 30u);
}

TEST(Dpi, CallMissingReturnsZero) {
  DpiContext ctx;
  auto result = ctx.Call("nonexistent", {1, 2});
  EXPECT_EQ(result, 0u);
}

}  // namespace
