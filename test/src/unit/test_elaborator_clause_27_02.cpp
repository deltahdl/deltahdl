#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §27.2 states that a parameter declared inside a generate block shall be
// treated as a localparam (the localparam machinery itself lives in §6.20.4).
// The parser records this by forcing `is_localparam` whenever a `parameter`
// declaration is seen inside a generate block, and the elaborator carries the
// flag into the module's RtlirParamDecl. These tests drive real source through
// parse + elaborate and observe the flag on the elaborated parameter, using a
// plain module-body `parameter` (which stays overridable) as the contrast.

const RtlirParamDecl* FindParam(const RtlirModule* mod, std::string_view name) {
  for (const auto& pd : mod->params) {
    if (pd.name == name) return &pd;
  }
  return nullptr;
}

TEST(GenerateBlockLocalparam, IfGenerateParameterTreatedAsLocalparam) {
  ElabFixture f;
  // Same `parameter` keyword in two positions: the module body (overridable,
  // not a localparam) and inside an if-generate block (forced to localparam).
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
