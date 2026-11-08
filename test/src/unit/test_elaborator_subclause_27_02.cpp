#include <gtest/gtest.h>

#include <string_view>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"

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

}  // namespace
