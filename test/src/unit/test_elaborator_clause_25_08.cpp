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
// there; re-testing them here would only restate those clauses.

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

}  // namespace
