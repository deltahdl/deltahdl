#pragma once

#include <gtest/gtest.h>

#include "fixture_elaborator.h"

using namespace delta;

// Elaborates a module containing `localparam int DEPTH = 32;` and verifies that
// the DEPTH parameter resolves to a localparam with value 32.
inline void ExpectLocalparamDepth32ResolvesAsLocal(ElabFixture& f) {
  auto* design = Elaborate(
      "module m;\n"
      "  localparam int DEPTH = 32;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& p : mod->params) {
    if (p.name == "DEPTH") {
      EXPECT_TRUE(p.is_resolved);
      EXPECT_EQ(p.resolved_value, 32);
      EXPECT_TRUE(p.is_localparam);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}
