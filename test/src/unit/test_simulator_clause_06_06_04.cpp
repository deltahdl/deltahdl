#include <gtest/gtest.h>

#include "common/arena.h"
#include "simulator/net.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(TriregResolution, TriregDrivenNormally) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 42);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 99));
  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(TriregResolution, MultipleDrivenDriversResolve) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4VecVal(arena, 8, 0);
  Net net;
  net.type = NetType::kTrireg;
  net.resolved = var;

  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0xAA));
  net.drivers.push_back(MakeLogic4VecVal(arena, 8, 0xAA));
  net.Resolve(arena);
  EXPECT_EQ(var->value.ToUint64(), 0xAAu);
}

}  // namespace
