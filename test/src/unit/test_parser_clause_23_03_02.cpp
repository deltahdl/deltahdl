// §23.3.2: Module instantiation syntax

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// =============================================================================
// A.4.1.1 -- Module instantiation
//
// module_instantiation ::=
//   module_identifier [ parameter_value_assignment ]
//     hierarchical_instance { , hierarchical_instance } ;
// =============================================================================
// --- module_instantiation: basic ---
TEST(ParserAnnexA0411, BasicModuleInst) {
  auto r = Parse("module m; sub u0(a, b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "sub");
  EXPECT_EQ(item->inst_name, "u0");
}

// --- module_instantiation: multiple hierarchical_instance ---
// module_identifier [#(...)] inst1(...), inst2(...), inst3(...) ;
TEST(ParserAnnexA0411, MultipleHierarchicalInstances) {
  auto r = Parse("module m; sub u0(a), u1(b), u2(c); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 3u);
  auto* i0 = r.cu->modules[0]->items[0];
  auto* i1 = r.cu->modules[0]->items[1];
  auto* i2 = r.cu->modules[0]->items[2];
  EXPECT_EQ(i0->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(i0->inst_module, "sub");
  EXPECT_EQ(i0->inst_name, "u0");
  EXPECT_EQ(i1->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(i1->inst_module, "sub");
  EXPECT_EQ(i1->inst_name, "u1");
  EXPECT_EQ(i2->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(i2->inst_module, "sub");
  EXPECT_EQ(i2->inst_name, "u2");
}

TEST(ParserAnnexA0411, MultipleInstancesWithParams) {
  auto r = Parse("module m; sub #(8) u0(a), u1(b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
  auto* i0 = r.cu->modules[0]->items[0];
  auto* i1 = r.cu->modules[0]->items[1];
  EXPECT_EQ(i0->inst_module, "sub");
  EXPECT_EQ(i1->inst_module, "sub");
  EXPECT_EQ(i0->inst_params.size(), 1u);
  EXPECT_EQ(i1->inst_params.size(), 1u);
}

// =============================================================================
// parameter_value_assignment ::= # ( [ list_of_parameter_value_assignments ] )
// list_of_parameter_value_assignments ::=
//   ordered_parameter_assignment { , ordered_parameter_assignment }
//   | named_parameter_assignment { , named_parameter_assignment }
// ordered_parameter_assignment ::= param_expression
// named_parameter_assignment ::= . parameter_identifier ( [ param_expression ]
// )
// =============================================================================
TEST(ParserAnnexA0411, EmptyParameterValueAssignment) {
  // #() — empty parameter list
  auto r = Parse("module m; sub #() u0(a); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_params.size(), 0u);
}

}  // namespace
