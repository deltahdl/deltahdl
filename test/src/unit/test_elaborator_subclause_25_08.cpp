#include <gtest/gtest.h>

#include <cstdint>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

uint32_t MemberWidth(const RtlirModule* inst) {
  for (const auto& v : inst->variables)
    if (v.name == "data") return v.width;
  return 0u;
}

TEST(ParameterizedInterface, DefaultParameterUsedWhenNotOverridden) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface ifc #(parameter int WIDTH = 8);\n"
      "  logic [WIDTH-1:0] data;\n"
      "endinterface\n"
      "module top;\n"
      "  ifc u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  ASSERT_EQ(design->top_modules[0]->children.size(), 1u);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 1u);
  EXPECT_TRUE(u0->params[0].is_resolved);
  EXPECT_EQ(u0->params[0].resolved_value, 8);
}

TEST(ParameterizedInterface, NamedOverrideAppliedToInterfaceInstance) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface ifc #(parameter int WIDTH = 8);\n"
      "  logic [WIDTH-1:0] data;\n"
      "endinterface\n"
      "module top;\n"
      "  ifc #(.WIDTH(32)) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 1u);
  EXPECT_EQ(u0->params[0].name, "WIDTH");
  EXPECT_EQ(u0->params[0].resolved_value, 32);
}

TEST(ParameterizedInterface, MemberWidthTracksDefaultAndRedefinition) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface ifc #(parameter int DWIDTH = 8);\n"
      "  logic [DWIDTH-1:0] data;\n"
      "endinterface\n"
      "module top;\n"
      "  ifc narrow();\n"
      "  ifc #(.DWIDTH(16)) wide();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules[0]->children.size(), 2u);

  auto member_width = [](const RtlirModule* inst) -> uint32_t {
    for (const auto& v : inst->variables)
      if (v.name == "data") return v.width;
    return 0u;
  };

  auto* narrow = design->top_modules[0]->children[0].resolved;
  auto* wide = design->top_modules[0]->children[1].resolved;
  ASSERT_NE(narrow, nullptr);
  ASSERT_NE(wide, nullptr);
  EXPECT_EQ(member_width(narrow), 8u);
  EXPECT_EQ(member_width(wide), 16u);
}

TEST(ParameterizedInterface, RedefinitionValueMayBeParentParameter) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface ifc #(parameter int WIDTH = 8);\n"
      "  logic [WIDTH-1:0] data;\n"
      "endinterface\n"
      "module top #(parameter int P = 20);\n"
      "  ifc #(.WIDTH(P)) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 1u);
  EXPECT_EQ(u0->params[0].resolved_value, 20);
  EXPECT_EQ(MemberWidth(u0), 20u);
}

TEST(ParameterizedInterface, RedefinitionValueMayBeParentLocalparam) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface ifc #(parameter int WIDTH = 8);\n"
      "  logic [WIDTH-1:0] data;\n"
      "endinterface\n"
      "module top;\n"
      "  localparam int L = 24;\n"
      "  ifc #(.WIDTH(L)) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 1u);
  EXPECT_EQ(u0->params[0].resolved_value, 24);
  EXPECT_EQ(MemberWidth(u0), 24u);
}

TEST(ParameterizedInterface, PositionalRedefinitionAppliedToInterfaceInstance) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface ifc #(parameter int WIDTH = 8);\n"
      "  logic [WIDTH-1:0] data;\n"
      "endinterface\n"
      "module top;\n"
      "  ifc #(28) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* u0 = design->top_modules[0]->children[0].resolved;
  ASSERT_NE(u0, nullptr);
  ASSERT_EQ(u0->params.size(), 1u);
  EXPECT_EQ(u0->params[0].resolved_value, 28);
  EXPECT_EQ(MemberWidth(u0), 28u);
}

TEST(ParameterizedInterface, UnknownParameterOverrideNameRejected) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface ifc #(parameter int WIDTH = 8);\n"
      "  logic [WIDTH-1:0] data;\n"
      "endinterface\n"
      "module top;\n"
      "  ifc #(.NOPE(4)) u0();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "has no parameter 'NOPE'", 5,
                            "23.10.2.2"));
}

}  // namespace
