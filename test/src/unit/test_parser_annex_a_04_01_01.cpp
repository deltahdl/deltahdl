#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ModuleInstantiationGrammar, OrderedParameterAssignment) {
  auto r = Parse("module m; sub #(8, 4) u0(a); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_params.size(), 2u);

  EXPECT_EQ(item->inst_params[0].first, "");
  EXPECT_EQ(item->inst_params[1].first, "");
}

TEST(ModuleInstantiationGrammar, NamedParameterAssignment) {
  auto r = Parse("module m; sub #(.WIDTH(8), .DEPTH(4)) u0(a); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_params.size(), 2u);
  EXPECT_EQ(item->inst_params[0].first, "WIDTH");
  EXPECT_NE(item->inst_params[0].second, nullptr);
  EXPECT_EQ(item->inst_params[1].first, "DEPTH");
  EXPECT_NE(item->inst_params[1].second, nullptr);
}

TEST(ModuleInstantiationGrammar, NamedParameterEmptyExpression) {
  auto r = Parse("module m; sub #(.WIDTH()) u0(a); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_params.size(), 1u);
  EXPECT_EQ(item->inst_params[0].first, "WIDTH");
  EXPECT_EQ(item->inst_params[0].second, nullptr);
}

TEST(ModuleInstantiationGrammar, SingleOrderedParam) {
  auto r = Parse("module m; sub #(16) u0(); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_params.size(), 1u);
}

TEST(ModuleInstantiationGrammar, InstanceArrayWithSize) {
  auto r = Parse("module m; sub u0[4](.a(a)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_name, "u0");
  EXPECT_NE(item->inst_range_left, nullptr);
  EXPECT_EQ(item->inst_range_right, nullptr);
}

TEST(ModuleInstantiationGrammar, EmptyPortList) {
  auto r = Parse("module m; sub u0(); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_ports.size(), 0u);
}

TEST(ModuleInstantiationGrammar, NamedParamsAndNamedPorts) {
  auto r = Parse(
      "module m;\n"
      "  sub #(.W(8), .D(4)) u0(.clk(clk), .data(d));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_params.size(), 2u);
  EXPECT_EQ(item->inst_params[0].first, "W");
  EXPECT_EQ(item->inst_params[1].first, "D");
  EXPECT_EQ(item->inst_ports.size(), 2u);
}

ModuleItem* FindModuleInst(const std::vector<ModuleItem*>& items) {
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kModuleInst) return item;
  }
  return nullptr;
}

TEST(ModuleInstantiationGrammar, InstanceArrayWithRangeAndPorts) {
  auto r = Parse(
      "module sub(input a, output b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  wire [3:0] x, y;\n"
      "  sub u0[3:0](.a(x), .b(y));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* inst = FindModuleInst(r.cu->modules[1]->items);
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(inst->inst_name, "u0");
  EXPECT_NE(inst->inst_range_left, nullptr);
  EXPECT_NE(inst->inst_range_right, nullptr);
}

TEST(ModuleInstantiationGrammar, BasicModuleInst) {
  auto r = Parse("module m; sub u0(a, b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "sub");
  EXPECT_EQ(item->inst_name, "u0");
}

TEST(ModuleInstantiationGrammar, MultipleHierarchicalInstances) {
  auto r = Parse("module m; sub u0(a), u1(b), u2(c); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  VerifyHierarchicalInstanceList(r.cu->modules[0]->items, "sub",
                                 {"u0", "u1", "u2"});
}

TEST(ModuleInstantiationGrammar, MultipleInstancesWithParams) {
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

TEST(ModuleInstantiationGrammar, EmptyParameterValueAssignment) {
  auto r = Parse("module m; sub #() u0(a); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_params.size(), 0u);
}

TEST(ModuleInstantiationGrammar, AttributeOnPortConnection) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sub u1(.a(x), (* no_connect *) .b(y));\n"
              "endmodule"));
}

// ordered_port_connection ::= { attribute_instance } [ expression ]
// The attribute_instance prefix is also permitted on a positional (ordered)
// connection, not only on a named one; the connection still parses as ordered.
TEST(ModuleInstantiationGrammar, AttributeOnOrderedPortConnection) {
  auto r = Parse(
      "module m; sub u0((* full_case *) x, (* parallel *) y); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_ports.size(), 2u);
  EXPECT_EQ(item->inst_ports[0].first, "");
  EXPECT_NE(item->inst_ports[0].second, nullptr);
  EXPECT_EQ(item->inst_ports[1].first, "");
  EXPECT_NE(item->inst_ports[1].second, nullptr);
}

TEST(ModuleInstantiationGrammar, InstanceArrayMultipleDimensions) {
  auto r = Parse("module m; sub u0[3:0][7:0](.a(a)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_name, "u0");
  ASSERT_EQ(item->inst_dims.size(), 2u);
  EXPECT_NE(item->inst_dims[0].first, nullptr);
  EXPECT_NE(item->inst_dims[0].second, nullptr);
  EXPECT_NE(item->inst_dims[1].first, nullptr);
  EXPECT_NE(item->inst_dims[1].second, nullptr);
  EXPECT_EQ(item->inst_range_left, item->inst_dims[0].first);
  EXPECT_EQ(item->inst_range_right, item->inst_dims[0].second);
}

// named_port_connection ::= ... | { attribute_instance } . *
// The .* wildcard is a distinct alternative of named_port_connection; it sets
// the instance's wildcard flag rather than appending an explicit connection.
TEST(ModuleInstantiationGrammar, WildcardPortConnection) {
  auto r = Parse("module m; sub u0(.*); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_TRUE(item->inst_wildcard);
  EXPECT_EQ(item->inst_ports.size(), 0u);
}

// A second .* in the same port-connection list is rejected.
TEST(ModuleInstantiationGrammar, ErrorDuplicateWildcardPort) {
  auto r = Parse("module m; sub u0(.*, .*); endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// named_port_connection ::= { attribute_instance } . port_identifier
//                           [ ( [ expression ] ) ]
// With the parenthesized expression omitted, the port name is connected
// implicitly; the parser records this via the implicit flag.
TEST(ModuleInstantiationGrammar, ImplicitNamedPortConnection) {
  auto r = Parse("module m; sub u0(.clk, .data); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_ports.size(), 2u);
  EXPECT_EQ(item->inst_ports[0].first, "clk");
  EXPECT_EQ(item->inst_ports[1].first, "data");
  ASSERT_EQ(item->inst_ports_implicit.size(), 2u);
  EXPECT_TRUE(item->inst_ports_implicit[0]);
  EXPECT_TRUE(item->inst_ports_implicit[1]);
}

// named_port_connection with the optional expression present but empty:
// . port_identifier ( ) leaves the connection expression null.
TEST(ModuleInstantiationGrammar, EmptyNamedPortExpression) {
  auto r = Parse("module m; sub u0(.clk()); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_ports.size(), 1u);
  EXPECT_EQ(item->inst_ports[0].first, "clk");
  EXPECT_EQ(item->inst_ports[0].second, nullptr);
  ASSERT_EQ(item->inst_ports_implicit.size(), 1u);
  EXPECT_FALSE(item->inst_ports_implicit[0]);
}

// ordered_port_connection ::= { attribute_instance } [ expression ]
// The expression is optional, so an empty positional slot is permitted and
// yields a null connection expression.
TEST(ModuleInstantiationGrammar, OrderedPortConnectionEmptyExpression) {
  auto r = Parse("module m; sub u0(a, , c); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_ports.size(), 3u);
  EXPECT_EQ(item->inst_ports[0].first, "");
  EXPECT_NE(item->inst_ports[0].second, nullptr);
  EXPECT_EQ(item->inst_ports[1].first, "");
  EXPECT_EQ(item->inst_ports[1].second, nullptr);
  EXPECT_NE(item->inst_ports[2].second, nullptr);
}

// list_of_port_connections ::= ordered_port_connection { ,
// ordered_port_connection }
//                            | named_port_connection { , named_port_connection
//                            }
// The two alternatives are mutually exclusive: a single list cannot combine
// ordered and named port connections.
TEST(ModuleInstantiationGrammar, ErrorOrderedAndNamedPortsCannotMix) {
  auto r = Parse("module m; sub u0(a, .b(c)); endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// list_of_parameter_value_assignments has the same two-alternative shape, so
// ordered and named parameter value assignments cannot be combined either.
TEST(ModuleInstantiationGrammar, ErrorOrderedAndNamedParamsCannotMix) {
  auto r = Parse("module m; sub #(8, .D(4)) u0(a); endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ModuleInstantiationGrammar, ErrorMissingInstanceName) {
  auto r = Parse("module m; sub(a, b); endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ModuleInstantiationGrammar, ErrorMissingPortParentheses) {
  auto r = Parse("module m; sub u0; endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// module_instantiation is terminated by a semicolon; omitting it is an error.
TEST(ModuleInstantiationGrammar, ErrorMissingSemicolon) {
  auto r = Parse("module m; sub u0(a) endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
