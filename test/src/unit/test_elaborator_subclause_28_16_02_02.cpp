#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"

using namespace delta;

namespace {

TEST(ChargeDecaySpecElaboration, ThirdDelayFlowsToDecayTicks) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg #(7, 11, 13) cap;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& net : mod->nets) {
    if (net.name == "cap") {
      EXPECT_EQ(net.decay_ticks, 13u);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(ChargeDecaySpecElaboration, SingleDelayDoesNotPopulateDecayTicks) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg #50 cap;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& net : mod->nets) {
    if (net.name == "cap") {
      EXPECT_EQ(net.decay_ticks, 0u);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(ChargeDecaySpecElaboration, ParameterThirdDelayResolvesToDecayTicks) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  parameter integer DECAY = 21;\n"
      "  trireg #(0, 0, DECAY) cap;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& net : mod->nets) {
    if (net.name == "cap") {
      EXPECT_EQ(net.decay_ticks, 21u);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(ChargeDecaySpecElaboration, LocalparamThirdDelayResolvesToDecayTicks) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  localparam integer DECAY = 34;\n"
      "  trireg #(0, 0, DECAY) cap;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& net : mod->nets) {
    if (net.name == "cap") {
      EXPECT_EQ(net.decay_ticks, 34u);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(ChargeDecaySpecElaboration, TwoDelaysDoNotPopulateDecayTicks) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg #(4, 9) cap;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& net : mod->nets) {
    if (net.name == "cap") {
      EXPECT_EQ(net.decay_ticks, 0u);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(ChargeDecaySpecElaboration, ThirdDelayTripleTakesTheTypicalMember) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg #(1, 2, 3:4:5) cap;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* cap = FindNet(design, "t", "cap");
  ASSERT_NE(cap, nullptr);
  EXPECT_EQ(cap->decay_ticks, 4u);
}

TEST(ChargeDecaySpecElaboration,
     ThirdDelayThatDoesNotFoldIsWarnedAboutRatherThanZeroed) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] leak;\n"
      "  trireg #(1, 2, leak) cap;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "trireg charge decay time does not fold", 3,
                              "28.16.2.2"));
}

TEST(ChargeDecaySpecElaboration, ZeroDecayTimeIsRecordedAsDecaying) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg #(0, 0, 0) cap;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& net : mod->nets) {
    if (net.name == "cap") {
      EXPECT_EQ(net.decay_ticks, 0u);
      EXPECT_TRUE(net.decays);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(ChargeDecaySpecElaboration, AbsentThirdDelayIsRecordedAsNotDecaying) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  trireg #50 cap;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& net : mod->nets) {
    if (net.name == "cap") {
      EXPECT_EQ(net.decay_ticks, 0u);
      EXPECT_FALSE(net.decays);
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

}  // namespace
