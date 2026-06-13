#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

// Annex A.4.1.2 Interface instantiation.
//
// The subclause defines a single BNF production:
//
//   interface_instantiation ::=
//       interface_identifier [ parameter_value_assignment ]
//           hierarchical_instance { , hierarchical_instance } ;
//
// Every sub-symbol is owned by another subclause: interface_identifier by
// A.9.3, and parameter_value_assignment plus hierarchical_instance by A.4.1.1.
// The only thing A.4.1.2 itself contributes is the rule assembling them: an
// interface identifier, an optional parameter value assignment, one or more
// hierarchical instances separated by commas, and a terminating semicolon.
//
// This production is syntactically identical to module_instantiation
// (A.4.1.1), so the parser cannot tell from the grammar whether the leading
// identifier names a module, an interface, or a program. All three share the
// same parse path (Parser::ParseModuleInstList) and produce a kModuleInst
// item; the distinction is resolved later, during elaboration. These tests
// therefore observe that an interface identifier used in an instantiation is
// accepted through that shared path with the A.4.1.2 shape.

namespace {

ModuleItem* FindInstantiation(const std::vector<ModuleItem*>& items) {
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kModuleInst) return item;
  }
  return nullptr;
}

// interface_identifier hierarchical_instance ;
// The minimal form: an interface name, a single instance, a semicolon, with
// the optional parameter_value_assignment slot omitted (empty parameters).
TEST(InterfaceInstantiationGrammar, BasicInterfaceInstantiation) {
  auto r = Parse(
      "interface ifc; endinterface\n"
      "module m;\n"
      "  ifc u0();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* inst = FindInstantiation(r.cu->modules[0]->items);
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(inst->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(inst->inst_module, "ifc");
  EXPECT_EQ(inst->inst_name, "u0");
  EXPECT_EQ(inst->inst_params.size(), 0u);
}

// interface_identifier [ parameter_value_assignment ] hierarchical_instance ;
// The optional parameter_value_assignment slot is present.
TEST(InterfaceInstantiationGrammar, WithParameterValueAssignment) {
  auto r = Parse(
      "interface ifc; endinterface\n"
      "module m;\n"
      "  ifc #(8) u0();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* inst = FindInstantiation(r.cu->modules[0]->items);
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(inst->inst_module, "ifc");
  EXPECT_EQ(inst->inst_params.size(), 1u);
}

// interface_identifier ... hierarchical_instance { , hierarchical_instance } ;
// The comma-separated repetition yields several instances sharing one
// interface identifier.
TEST(InterfaceInstantiationGrammar, MultipleHierarchicalInstances) {
  auto r = Parse(
      "interface ifc; endinterface\n"
      "module m;\n"
      "  ifc u0(), u1(), u2();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 3u);
  auto* i0 = r.cu->modules[0]->items[0];
  auto* i1 = r.cu->modules[0]->items[1];
  auto* i2 = r.cu->modules[0]->items[2];
  EXPECT_EQ(i0->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(i0->inst_module, "ifc");
  EXPECT_EQ(i0->inst_name, "u0");
  EXPECT_EQ(i1->inst_module, "ifc");
  EXPECT_EQ(i1->inst_name, "u1");
  EXPECT_EQ(i2->inst_module, "ifc");
  EXPECT_EQ(i2->inst_name, "u2");
}

// The parameter value assignment, when present, is shared across every
// instance in the comma-separated list.
TEST(InterfaceInstantiationGrammar, MultipleInstancesShareParameters) {
  auto r = Parse(
      "interface ifc; endinterface\n"
      "module m;\n"
      "  ifc #(16) u0(), u1();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
  auto* i0 = r.cu->modules[0]->items[0];
  auto* i1 = r.cu->modules[0]->items[1];
  EXPECT_EQ(i0->inst_params.size(), 1u);
  EXPECT_EQ(i1->inst_params.size(), 1u);
}

// The production is terminated by a semicolon; omitting it is an error.
TEST(InterfaceInstantiationGrammar, ErrorMissingSemicolon) {
  auto r = Parse(
      "interface ifc; endinterface\n"
      "module m;\n"
      "  ifc u0()\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// In the { , hierarchical_instance } repetition each comma must be followed by
// another instance; a trailing comma with no instance after it is an error.
TEST(InterfaceInstantiationGrammar, ErrorTrailingCommaInInstanceList) {
  auto r = Parse(
      "interface ifc; endinterface\n"
      "module m;\n"
      "  ifc u0(), ;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
