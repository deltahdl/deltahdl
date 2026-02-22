// §6.6.5: Tri0 and tri1 nets

#include <gtest/gtest.h>
#include "common/arena.h"
#include "simulation/net.h"
#include "simulation/scheduler.h"
#include "simulation/variable.h"

using namespace delta;

namespace {

TEST(NetResolution, Tri0ResolvesToZero) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kTri0;
  net.resolved = var;
  // Single driver with z → resolves to 0 for tri0.
  auto drv = MakeLogic4Vec(arena, 8);
  drv.words[0].aval = ~uint64_t{0};  // All z.
  drv.words[0].bval = ~uint64_t{0};
  net.drivers.push_back(drv);
  net.Resolve(arena);
  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0u);
  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0u);
}

TEST(NetResolution, Tri1ResolvesToOne) {
  Arena arena;
  auto* var = arena.Create<Variable>();
  var->value = MakeLogic4Vec(arena, 8);
  Net net;
  net.type = NetType::kTri1;
  net.resolved = var;
  // Single driver with z → resolves to 1 for tri1.
  auto drv = MakeLogic4Vec(arena, 8);
  drv.words[0].aval = ~uint64_t{0};
  drv.words[0].bval = ~uint64_t{0};
  net.drivers.push_back(drv);
  net.Resolve(arena);
  EXPECT_EQ(var->value.words[0].aval & 0xFF, 0xFFu);
  EXPECT_EQ(var->value.words[0].bval & 0xFF, 0u);
}

}  // namespace
