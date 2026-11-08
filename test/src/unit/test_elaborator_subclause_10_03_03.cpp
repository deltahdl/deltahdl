#include <gtest/gtest.h>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(AssignmentDelayElaboration, NettypeRejectsMultiDelay) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  nettype logic mytype;\n"
      "  mytype n;\n"
      "  assign #(5, 10) n = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "continuous assignment to a nettype net shall have at most",
                    4, "10.3.3"));
}

TEST(AssignmentDelayElaboration, NettypeAcceptsSingleDelay) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  nettype logic mytype;\n"
      "  mytype n;\n"
      "  assign #5 n = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssignmentDelayElaboration, SingleDelayValue) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire a, b;\n"
      "  assign #10 a = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  ASSERT_NE(mod->assigns[0].delay, nullptr);
  EXPECT_EQ(mod->assigns[0].delay->int_val, 10u);
}

TEST(AssignmentDelayElaboration, RiseFallDelayValues) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire a, b;\n"
      "  assign #(5, 10) a = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  ASSERT_NE(mod->assigns[0].delay, nullptr);
  EXPECT_EQ(mod->assigns[0].delay->int_val, 5u);
  ASSERT_NE(mod->assigns[0].delay_fall, nullptr);
  EXPECT_EQ(mod->assigns[0].delay_fall->int_val, 10u);
}

TEST(AssignmentDelayElaboration, ThreeDelayValues) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire a, b;\n"
      "  assign #(5, 10, 15) a = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  ASSERT_NE(mod->assigns[0].delay, nullptr);
  EXPECT_EQ(mod->assigns[0].delay->int_val, 5u);
  ASSERT_NE(mod->assigns[0].delay_fall, nullptr);
  EXPECT_EQ(mod->assigns[0].delay_fall->int_val, 10u);
  ASSERT_NE(mod->assigns[0].delay_decay, nullptr);
  EXPECT_EQ(mod->assigns[0].delay_decay->int_val, 15u);
}

TEST(AssignmentDelayElaboration, NoDelay) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire a, b;\n"
      "  assign a = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  EXPECT_EQ(mod->assigns[0].delay, nullptr);
  EXPECT_EQ(mod->assigns[0].delay_fall, nullptr);
  EXPECT_EQ(mod->assigns[0].delay_decay, nullptr);
}

TEST(AssignmentDelayElaboration, NetDeclSingleDelayOnImplicitAssign) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire #10 w = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  ASSERT_NE(mod->assigns[0].delay, nullptr);
  EXPECT_EQ(mod->assigns[0].delay->int_val, 10u);
}

TEST(AssignmentDelayElaboration, NetDeclThreeDelayOnImplicitAssign) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire #(3, 6, 9) w = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  ASSERT_NE(mod->assigns[0].delay, nullptr);
  EXPECT_EQ(mod->assigns[0].delay->int_val, 3u);
  ASSERT_NE(mod->assigns[0].delay_fall, nullptr);
  EXPECT_EQ(mod->assigns[0].delay_fall->int_val, 6u);
  ASSERT_NE(mod->assigns[0].delay_decay, nullptr);
  EXPECT_EQ(mod->assigns[0].delay_decay->int_val, 9u);
}

TEST(AssignmentDelayElaboration, NetDeclTwoDelayOnImplicitAssign) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire #(5, 10) w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  ASSERT_NE(mod->assigns[0].delay, nullptr);
  EXPECT_EQ(mod->assigns[0].delay->int_val, 5u);
  ASSERT_NE(mod->assigns[0].delay_fall, nullptr);
  EXPECT_EQ(mod->assigns[0].delay_fall->int_val, 10u);
  EXPECT_EQ(mod->assigns[0].delay_decay, nullptr);
}

TEST(AssignmentDelayElaboration, NetDeclDelayWithoutAssignStaysOnTheNet) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg a;\n"
      "  wire #5 w;\n"
      "  assign w = a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->assigns.size(), 1u);
  EXPECT_EQ(mod->assigns[0].delay, nullptr);
  const RtlirNet* w = nullptr;
  for (const auto& net : mod->nets) {
    if (net.name == "w") w = &net;
  }
  ASSERT_NE(w, nullptr);
  ASSERT_NE(w->delay_rise, nullptr);
  EXPECT_EQ(w->delay_rise->int_val, 5u);
}

TEST(AssignmentDelayElaboration, NettypeArrayRejectsMultiDelay) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  nettype logic mytype;\n"
      "  mytype n[3];\n"
      "  assign #(5, 10) n = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "continuous assignment to a nettype net shall have at most",
                    4, "10.3.3"));
}

TEST(AssignmentDelayElaboration, NettypeArrayAcceptsSingleDelay) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  nettype logic mytype;\n"
      "  mytype n[3];\n"
      "  assign #5 n = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssignmentDelayElaboration, NettypeNetDeclRejectsMultiDelay) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  nettype logic T;\n"
      "  logic a;\n"
      "  T #(1,2) n = a;\n"
      "  T #3 m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "a net of a user-defined nettype is declared with "
                            "at most a single delay",
                            4, "10.3.3"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "a net of a user-defined nettype is declared with "
                             "at most a single delay",
                             5, "10.3.3"));
}

}  // namespace
