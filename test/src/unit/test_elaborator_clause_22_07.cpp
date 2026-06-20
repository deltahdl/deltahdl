#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(TimescaleElaboration, TimescaleModuleElaboratesWithoutError) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`timescale 1ns / 1ps\n"
      "module t;\n"
      "  parameter P = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& p : mod->params) {
    if (p.name == "P") {
      EXPECT_EQ(p.resolved_value, 42);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(TimescaleElaboration, MultipleTimescaleModulesElaborate) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`timescale 1ns / 1ps\n"
      "module m1;\n"
      "  parameter P = 10;\n"
      "endmodule\n"
      "`timescale 1us / 1ns\n"
      "module m2;\n"
      "  parameter P = 20;\n"
      "endmodule\n",
      f, "m2");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& p : mod->params) {
    if (p.name == "P") {
      EXPECT_EQ(p.resolved_value, 20);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(TimescaleElaboration, LaterTimescaleOverrideElaboratesCorrectly) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "`timescale 1ns / 1ps\n"
      "`timescale 10us / 1us\n"
      "module t;\n"
      "  parameter P = 99;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& p : mod->params) {
    if (p.name == "P") {
      EXPECT_EQ(p.resolved_value, 99);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

}  // namespace
