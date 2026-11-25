#include <gtest/gtest.h>

#include <string_view>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

const RtlirParamDecl* FindParam(const RtlirModule* mod, std::string_view name) {
  for (const auto& pd : mod->params) {
    if (pd.name == name) return &pd;
  }
  return nullptr;
}

TEST(GenerateBlockLocalparam, IfGenerateParameterTreatedAsLocalparam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter Q = 7;\n"
      "  if (1) begin\n"
      "    parameter P = 5;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  const RtlirModule* mod = design->top_modules[0];

  const RtlirParamDecl* p = FindParam(mod, "P");
  ASSERT_NE(p, nullptr);
  EXPECT_TRUE(p->is_localparam);

  const RtlirParamDecl* q = FindParam(mod, "Q");
  ASSERT_NE(q, nullptr);
  EXPECT_FALSE(q->is_localparam);
}

TEST(GenerateBlockLocalparam, ForGenerateParameterTreatedAsLocalparam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 1; i = i + 1) begin\n"
      "    parameter P = 5;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  const RtlirModule* mod = design->top_modules[0];

  const RtlirParamDecl* p = FindParam(mod, "P");
  ASSERT_NE(p, nullptr);
  EXPECT_TRUE(p->is_localparam);
}

TEST(GenerateBlockLocalparam, CaseGenerateParameterTreatedAsLocalparam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  case (1)\n"
      "    1: begin parameter P = 5; end\n"
      "    default: ;\n"
      "  endcase\n"
      "endmodule\n",
      f);
  ASSERT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  const RtlirModule* mod = design->top_modules[0];

  const RtlirParamDecl* p = FindParam(mod, "P");
  ASSERT_NE(p, nullptr);
  EXPECT_TRUE(p->is_localparam);
}

TEST(GenerateBlockLocalparam, DefparamOfAGenerateBlockParameterIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module c;\n"
      "  parameter int B = 1;\n"
      "  if (1) begin : g\n"
      "    parameter int P = 3;\n"
      "  end\n"
      "  for (genvar k = 0; k < 1; k++) begin : h\n"
      "    parameter int P = 3;\n"
      "  end\n"
      "endmodule\n"
      "interface ii;\n"
      "  if (1) begin : g\n"
      "    parameter int P = 3;\n"
      "  end\n"
      "endinterface\n"
      "program pp;\n"
      "  if (1) begin : g\n"
      "    parameter int P = 3;\n"
      "  end\n"
      "endprogram\n"
      "module top;\n"
      "  c u();\n"
      "  ii v();\n"
      "  pp w();\n"
      "  defparam u.g.P = 6;\n"
      "  defparam u.h[0].P = 6;\n"
      "  defparam v.g.P = 6;\n"
      "  defparam w.g.P = 6;\n"
      "endmodule\n",
      f);
  for (int line = 24; line <= 27; ++line) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "defparam cannot override a local parameter",
                              line, "23.10.1"));
  }
}

TEST(GenerateBlockLocalparam, DefparamOfABodyParameterIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module c;\n"
      "  parameter int B = 1;\n"
      "endmodule\n"
      "interface ii;\n"
      "  parameter int B = 1;\n"
      "endinterface\n"
      "program pp;\n"
      "  parameter int B = 1;\n"
      "endprogram\n"
      "module top;\n"
      "  c u();\n"
      "  ii v();\n"
      "  pp w();\n"
      "  defparam u.B = 5;\n"
      "  defparam v.B = 6;\n"
      "  defparam w.B = 7;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.Diagnostics().empty());
}

}  // namespace
