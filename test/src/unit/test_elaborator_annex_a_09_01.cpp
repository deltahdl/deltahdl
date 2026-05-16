// §A.9.1: elaborator-stage coverage of attribute instances. The parser
// captures the §A.9.1 BNF into a vector<Attribute>; the elaborator's
// ResolveAttributes pass folds each attr_spec's constant_expression and
// surfaces the result as a ResolvedAttribute on the corresponding RTLIR node.

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §A.9.1: attribute_instance ::= (* attr_spec { , attr_spec } *) — a single
// attr_spec with no value resolves to value 1 (the §5.12 default).
TEST(AttributeInstanceElaboration, SingleAttrNoValueResolves) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "(* synthesis *)\n"
      "module m;\n"
      "  logic x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_FALSE(design->top_modules.empty());
  auto& m = *design->top_modules[0];
  ASSERT_GE(m.attrs.size(), 1u);
  EXPECT_EQ(m.attrs[0].name, "synthesis");
  ASSERT_TRUE(m.attrs[0].resolved_value.has_value());
  EXPECT_EQ(*m.attrs[0].resolved_value, 1);
}

// §A.9.1: attr_spec ::= attr_name [ = constant_expression ] — a value form
// folds through ConstEvalInt during ResolveAttributes.
TEST(AttributeInstanceElaboration, AttrSpecConstantExpressionFolds) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "(* depth = 2 + 3 *)\n"
      "module m;\n"
      "  logic x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto& m = *design->top_modules[0];
  ASSERT_GE(m.attrs.size(), 1u);
  EXPECT_EQ(m.attrs[0].name, "depth");
  ASSERT_TRUE(m.attrs[0].resolved_value.has_value());
  EXPECT_EQ(*m.attrs[0].resolved_value, 5);
}

// §A.9.1: attribute_instance with multiple attr_specs separated by ',' —
// every attr_spec lands as its own ResolvedAttribute in BNF order.
TEST(AttributeInstanceElaboration, MultipleAttrSpecsResolveInOrder) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "(* full_case, parallel_case *)\n"
      "module m;\n"
      "  logic x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto& m = *design->top_modules[0];
  ASSERT_GE(m.attrs.size(), 2u);
  EXPECT_EQ(m.attrs[0].name, "full_case");
  EXPECT_EQ(m.attrs[1].name, "parallel_case");
}

// §A.9.1 ↔ §A.8.3 cross-link: attr_spec's optional value is a §A.8.3
// constant_expression. A non-trivial expression must fold to a constant at
// elaboration.
TEST(AttributeInstanceElaboration, AttrValueConstantExpressionCrossLink) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter P = 4;\n"
      "  (* weight = (P > 0) ? 8 : 16 *)\n"
      "  logic x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto& m = *design->top_modules[0];
  // The attribute is on the logic variable, which lives in variables.
  bool found = false;
  for (auto& v : m.variables) {
    for (auto& a : v.attrs) {
      if (a.name == "weight") {
        found = true;
        ASSERT_TRUE(a.resolved_value.has_value());
        EXPECT_EQ(*a.resolved_value, 8);
      }
    }
  }
  EXPECT_TRUE(found);
}

// §A.9.1 ↔ §A.2.2.1 cross-link: an attribute_instance prefixes a §A.2.2.1
// struct_union_member. The attribute is captured in the AST and survives
// elaboration without diagnostics.
TEST(AttributeInstanceElaboration, AttributeOnStructMemberCrossLink) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef struct packed {\n"
      "    (* keep = 1 *) logic [3:0] a;\n"
      "    logic [3:0] b;\n"
      "  } s_t;\n"
      "  s_t s;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §A.9.1: attr_spec ::= attr_name [ = constant_expression ] — a string
// literal is a valid constant_expression and surfaces as the string_value
// slot on the ResolvedAttribute.
TEST(AttributeInstanceElaboration, AttrStringValueResolves) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "(* tool = \"synplify\" *)\n"
      "module m;\n"
      "  logic x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto& m = *design->top_modules[0];
  ASSERT_GE(m.attrs.size(), 1u);
  EXPECT_EQ(m.attrs[0].name, "tool");
  EXPECT_EQ(m.attrs[0].string_value, "synplify");
}

}  // namespace
