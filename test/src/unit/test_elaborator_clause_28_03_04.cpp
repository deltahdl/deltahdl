#include <gtest/gtest.h>

#include "model_gate_declaration.h"

namespace {

TEST(GateDecl, ArrayRequiresName) {
  GateDeclInfo info;
  info.has_range = true;
  info.has_name = false;
  EXPECT_FALSE(ValidateGateDecl(info));
}

TEST(GateDecl, ArrayWithNameIsValid) {
  GateDeclInfo info;
  info.has_range = true;
  info.has_name = true;
  info.range_lhi = 0;
  info.range_rhi = 3;
  info.terminal_count = 3;
  EXPECT_TRUE(ValidateGateDecl(info));
}

}
