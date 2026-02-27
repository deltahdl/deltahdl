// §28.3.4: The primitive instance identifier

#include <gtest/gtest.h>

#include "model_gate_declaration.h"

namespace {

// §28.3.3: "Gates and switches in declarations with no delay
//  specification shall have no propagation delay."
// --- §28.3.4: Instance identifier ---
// §28.3.4: "If multiple instances are declared as an array of instances,
//  an identifier shall be used to name the instances."
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

}  // namespace
