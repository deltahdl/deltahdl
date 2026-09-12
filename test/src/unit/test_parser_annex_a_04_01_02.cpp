#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"

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
  VerifyHierarchicalInstanceList(r.cu->modules[0]->items, "ifc",
                                 {"u0", "u1", "u2"});
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
  // Parser::ParseModuleInstList files the shared instantiation reports under
  // §23.3.2, the module_instantiation subclause A.4.1.2 duplicates.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got 'endmodule'", 4, "23.3.2"));
}

// In the { , hierarchical_instance } repetition each comma must be followed by
// another instance; a trailing comma with no instance after it is an error.
TEST(InterfaceInstantiationGrammar, ErrorTrailingCommaInInstanceList) {
  auto r = Parse(
      "interface ifc; endinterface\n"
      "module m;\n"
      "  ifc u0(), ;\n"
      "endmodule\n");
  // §23.3.2 owns the hierarchical_instance name the parser demands after the
  // comma.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got ';'", 3, "23.3.2"));
}

// hierarchical_instance is A.4.1.1's, `name_of_instance ( [
// list_of_port_connections ] )` with name_of_instance `instance_identifier {
// unpacked_dimension }`, and A.9.3 gives the identifier `simple_identifier |
// escaped_identifier`: an interface instance takes an escaped name, an
// unpacked dimension, and the `.*` named_port_connection.
TEST(InterfaceInstantiationGrammar, InstanceNameDimensionAndWildcard) {
  auto r = Parse(
      "interface ifc(input logic clk); endinterface\n"
      "module m(input logic clk);\n"
      "  ifc \\b.0 (.*);\n"
      "  ifc bs[0:3] (clk);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 2u);
  EXPECT_EQ(items[0]->inst_name, "b.0");
  EXPECT_TRUE(items[0]->inst_wildcard);
  EXPECT_EQ(items[1]->inst_name, "bs");
  EXPECT_NE(items[1]->inst_range_left, nullptr);
  EXPECT_NE(items[1]->inst_range_right, nullptr);
}

// parameter_value_assignment is A.4.1.1's, whose param_expression A.8.3 spells
// `mintypmax_expression | data_type | $`.
TEST(InterfaceInstantiationGrammar, ParameterValueForms) {
  auto r = Parse(
      "interface ifc #(parameter int W = 8, parameter type T = logic);\n"
      "endinterface\n"
      "module m;\n"
      "  ifc #(1:2:3, bit) u0();\n"
      "  ifc #(.W($), .T(int)) u1();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  const auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 2u);
  ASSERT_EQ(items[0]->inst_params.size(), 2u);
  EXPECT_EQ(items[0]->inst_params[0].second->kind, ExprKind::kMinTypMax);
  ASSERT_EQ(items[1]->inst_params.size(), 2u);
  EXPECT_EQ(items[1]->inst_params[0].first, "W");
  EXPECT_EQ(items[1]->inst_params[1].first, "T");
}

// A.1.4's module_common_item admits interface_instantiation, and A.1.6's
// interface_or_generate_item reaches module_common_item, so an interface is
// instantiated inside a module, inside an interface, and inside a generate
// block of either.
TEST(InterfaceInstantiationGrammar, InstantiatedInsideInterfaceAndGenerate) {
  auto r = Parse(
      "interface leaf; endinterface\n"
      "interface bus;\n"
      "  leaf l0();\n"
      "  if (1) begin : g\n"
      "    leaf l1();\n"
      "  end\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 2u);
  auto* inst = FindInstantiation(r.cu->interfaces[1]->items);
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(inst->inst_module, "leaf");
  EXPECT_EQ(inst->inst_name, "l0");
}

}  // namespace
