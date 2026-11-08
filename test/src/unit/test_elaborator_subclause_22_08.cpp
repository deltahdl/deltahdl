#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(DefaultNettypeElaboration, WireModuleElaboratesCorrectly) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`default_nettype wire\n"
      "module t;\n"
      "  parameter P = 7;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DefaultNettypeElaboration, NoneWithExplicitDeclsElaborates) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`default_nettype none\n"
      "module t;\n"
      "  wire w;\n"
      "  parameter P = 5;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(DefaultNettypeElaboration, DirectiveControlsImplicitNetType) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`default_nettype wand\n"
      "module top;\n"
      "  assign w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& n : mod->nets) {
    if (n.name == "w") {
      found = true;
      EXPECT_EQ(n.net_type, NetType::kWand);
    }
  }
  EXPECT_TRUE(found) << "implicit net 'w' not created";
}

TEST(DefaultNettypeElaboration, DirectiveControlsPrimitiveTerminalNetType) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`default_nettype tri\n"
      "module top;\n"
      "  and g1(y, a, b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  int checked = 0;
  for (const auto& n : mod->nets) {
    if (n.name == "y" || n.name == "a" || n.name == "b") {
      ++checked;
      EXPECT_EQ(n.net_type, NetType::kTri);
    }
  }
  EXPECT_EQ(checked, 3) << "implicit gate-terminal nets not all created";
}

}  // namespace
