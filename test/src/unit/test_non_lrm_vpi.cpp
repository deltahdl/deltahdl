// Non-LRM internal VPI infrastructure tests.

#include <gtest/gtest.h>

#include "simulation/vpi.h"

namespace delta {
namespace {

TEST(NonLrmVpi, DefaultContextIsAvailable) {
  SetGlobalVpiContext(nullptr);
  VpiContext& ctx = GetGlobalVpiContext();
  (void)ctx;
}

}  // namespace
}  // namespace delta
