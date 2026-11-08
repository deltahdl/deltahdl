#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

const RtlirModule* FirstChild(const RtlirModule* mod) {
  if (mod == nullptr || mod->children.empty()) return nullptr;
  return mod->children[0].resolved;
}

int64_t ParamValue(const RtlirModule* mod, std::string_view name) {
  if (mod == nullptr) return -1;
  for (const auto& p : mod->params) {
    if (p.name == name) return p.resolved_value;
  }
  return -1;
}

TEST(DefparamSupport, DefparamBeforeTheInstanceApplies) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module leaf #(parameter int P = 1)(); endmodule\n"
      "module top;\n"
      "  defparam u.P = 5;\n"
      "  leaf u();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ParamValue(FirstChild(design->top_modules[0]), "P"), 5);
}

TEST(DefparamSupport, DefparamInASeparateTopModuleReachesTheInstance) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module leaf #(parameter int P = 1)(); endmodule\n"
      "module top;\n"
      "  leaf u1();\n"
      "endmodule\n"
      "module annotate;\n"
      "  defparam top.u1.P = 7;\n"
      "endmodule\n",
      f, "", true);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 2u);
  EXPECT_EQ(ParamValue(FirstChild(design->top_modules[0]), "P"), 7);
}

TEST(DefparamSupport, DefparamInASeparateTopModuleReachesTheTopsParameter) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module top #(parameter int P = 1)(); endmodule\n"
      "module annotate;\n"
      "  defparam top.P = 9;\n"
      "endmodule\n",
      f, "", true);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 2u);
  EXPECT_EQ(ParamValue(design->top_modules[0], "P"), 9);
}

TEST(DefparamSupport, DefparamThroughTheTopLevelModuleReachesTheWriter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  m1 n();\n"
      "endmodule\n"
      "module m1;\n"
      "  parameter p = 2;\n"
      "  defparam m.n.p = 1;\n"
      "  if (p == 1) begin : gen_unique\n"
      "    m2 n();\n"
      "  end\n"
      "endmodule\n"
      "module m2;\n"
      "  parameter p = 3;\n"
      "endmodule\n",
      f, "m");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const RtlirModule* m1 = FirstChild(design->top_modules[0]);
  EXPECT_EQ(ParamValue(m1, "p"), 1);
  EXPECT_NE(FirstChild(m1), nullptr);
}

TEST(DefparamSupport, DefparamValueFlowsIntoAnotherDefparam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module leaf #(parameter int P = 1)(); endmodule\n"
      "module mid #(parameter int Q = 2);\n"
      "  leaf u();\n"
      "  defparam u.P = Q;\n"
      "endmodule\n"
      "module top;\n"
      "  mid v();\n"
      "  defparam v.Q = 8;\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const RtlirModule* mid = FirstChild(design->top_modules[0]);
  EXPECT_EQ(ParamValue(mid, "Q"), 8);
  EXPECT_EQ(ParamValue(FirstChild(mid), "P"), 8);
}

TEST(DefparamSupport, DefparamNamingNoParameterOfTheTopWarns) {
  ElabFixture f;
  ElaborateSrc(
      "module top #(parameter int P = 1)(); endmodule\n"
      "module annotate;\n"
      "  defparam top.NOPE = 9;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(), "defparam target not found",
                              3, "23.10.1"));
}

TEST(DefparamSupport, DefparamInGenerateBlockCannotReachOutThroughTheTop) {
  ElabFixture f;
  ElaborateSrc(
      "module leaf #(parameter int P = 1)(); endmodule\n"
      "module top;\n"
      "  leaf u1();\n"
      "  if (1) begin : g\n"
      "    defparam top.u1.P = 7;\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "defparam inside a generate block or an array of instances "
                    "reaches a parameter outside that hierarchy",
                    5, "23.10.1"));
}

}  // namespace
