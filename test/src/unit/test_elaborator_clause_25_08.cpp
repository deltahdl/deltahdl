#include "fixture_elaborator.h"

using namespace delta;

namespace {

// Section 25.8 owns one capability claim: an interface definition may take
// advantage of parameters and parameter redefinition in the same manner as a
// module definition. The elaborator is where this claim is concretely applied
// to an interface instance, reusing the generic module-parameter machinery.
// Two facets, one observer each:
//   (a) parameters with defaults  -> default applies when not overridden
//   (b) redefinition              -> an override is applied to the instance
// The named-override form matches the worked example in the LRM text
// (simple_bus #(.DWIDTH(16)) wide_intf). Other override mechanics (positional
// form, multiple/reordered names, empty list, parent-scope expressions,
// unknown-name errors) are owned by 6.20 / 23.10.2 / 23.10.2.2 and exercised
// there; re-testing them here would only restate those clauses. What IS worth
// exercising here is that this reuse holds across the distinct input forms a
// redefinition value can take -- a literal, a parent parameter, a parent
// localparam -- and across the positional as well as the named position, each
// of which drives a different resolution path, plus that the reused machinery
// still rejects a bad override on an interface exactly as it would on a module.

// Width of the interface member named `data` in an elaborated instance; 0 if
// absent. `logic [W-1:0] data` lands in the instance's variables list.
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

// The claim's demonstrated effect: because an interface uses parameters "in the
// same manner as a module," a member declared in terms of a parameter is sized
// from that parameter, and a redefinition re-sizes it -- the interface analog
// of a module's parameterized port width (23.2.3). This mirrors the LRM worked
// example, which instantiates one default interface alongside a #(.DWIDTH(16))
// override and describes the latter as "16-bit wide." Both instances live under
// the same top, so a single elaboration observes the default and the override
// sizing the same member differently.
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

// Redefinition value form: a parent-module PARAMETER. The override expression
// is a name that resolves in the instantiating scope, a different const-eval
// path than a plain literal. Built from 23.10.2.2 named-override syntax and
// driven end to end; the interface member must be sized from the parameter's
// value.
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

// Redefinition value form: a parent-module LOCALPARAM. Same override surface, a
// value produced by a localparam declaration in the instantiating module. Built
// from real source and driven end to end.
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

// Redefinition position: the POSITIONAL form `#(v)`. The LRM example shows the
// named form; the "same manner as a module" claim equally covers a positional
// override, which takes the ordered-assignment path rather than the by-name
// one. Observed on an interface instance end to end.
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

// Negative form: because interface parameterization reuses the module override
// machinery, a by-name override that targets a parameter the interface does not
// declare is rejected during elaboration, just as it would be for a module.
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
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
