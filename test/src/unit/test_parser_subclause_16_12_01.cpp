#include "fixture_parser.h"

using namespace delta;

namespace {

bool HasItemKind(ParseResult& r, ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return true;
  }
  return false;
}

const ModuleItem* FindPropertyDecl(ParseResult& r, std::string_view name) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kPropertyDecl && item->name == name) {
      return item;
    }
  }
  return nullptr;
}

bool RefersToInstance(const ModuleItem* decl, std::string_view name) {
  for (auto ref : decl->prop_instance_refs) {
    if (ref == name) return true;
  }
  return false;
}

TEST(AssertionSemanticsParsing, PropertyReference) {
  auto r = Parse(
      "module m;\n"
      "  property p_base;\n"
      "    @(posedge clk) a |-> b;\n"
      "  endproperty\n"
      "  assert property (p_base);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kPropertyDecl));
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

// §16.12.1: an instance of a named property may be used not only as a
// top-level property_spec (see PropertyReference above) but also as a
// property_expr — that is, as the operand of a property-building operator.
// Here `leaf` is instantiated as the operand of `not` inside `outer`; the
// parser accepts that property_expr position and records the instance among
// the declaring property's instance references.
TEST(AssertionSemanticsParsing, PropertyInstanceUsedAsPropertyExprOperand) {
  auto r = Parse(
      "module m;\n"
      "  property leaf;\n"
      "    @(posedge clk) a |-> b;\n"
      "  endproperty\n"
      "  property outer;\n"
      "    @(posedge clk) not leaf();\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.has_errors);
  const ModuleItem* outer = FindPropertyDecl(r, "outer");
  ASSERT_NE(outer, nullptr);
  EXPECT_TRUE(RefersToInstance(outer, "leaf"));
}

}  // namespace
