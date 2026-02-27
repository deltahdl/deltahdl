// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

namespace {

// =============================================================================
// Combined: all 7 productions in a single module
// =============================================================================
TEST(ParserA304, AllGateAndSwitchTypes) {
  auto r = Parse(
      "module m;\n"
      "  // cmos_switchtype\n"
      "  cmos (o1, i1, nc1, pc1);\n"
      "  rcmos (o2, i2, nc2, pc2);\n"
      "  // enable_gatetype\n"
      "  bufif0 (o3, i3, e3);\n"
      "  bufif1 (o4, i4, e4);\n"
      "  notif0 (o5, i5, e5);\n"
      "  notif1 (o6, i6, e6);\n"
      "  // mos_switchtype\n"
      "  nmos (o7, i7, c7);\n"
      "  pmos (o8, i8, c8);\n"
      "  rnmos (o9, i9, c9);\n"
      "  rpmos (o10, i10, c10);\n"
      "  // n_input_gatetype\n"
      "  and (o11, a11, b11);\n"
      "  nand (o12, a12, b12);\n"
      "  or (o13, a13, b13);\n"
      "  nor (o14, a14, b14);\n"
      "  xor (o15, a15, b15);\n"
      "  xnor (o16, a16, b16);\n"
      "  // n_output_gatetype\n"
      "  buf (o17, i17);\n"
      "  not (o18, i18);\n"
      "  // pass_en_switchtype\n"
      "  tranif0 (a19, b19, c19);\n"
      "  tranif1 (a20, b20, c20);\n"
      "  rtranif0 (a21, b21, c21);\n"
      "  rtranif1 (a22, b22, c22);\n"
      "  // pass_switchtype\n"
      "  tran (a23, b23);\n"
      "  rtran (a24, b24);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);

  // Verify all 24 gate kinds are present
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kCmos), nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kRcmos), nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kBufif0),
            nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kBufif1),
            nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kNotif0),
            nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kNotif1),
            nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kNmos), nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kPmos), nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kRnmos), nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kRpmos), nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kAnd), nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kNand), nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kOr), nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kNor), nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kXor), nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kXnor), nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kBuf), nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kNot), nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kTranif0),
            nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kTranif1),
            nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kRtranif0),
            nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kRtranif1),
            nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kTran), nullptr);
  EXPECT_NE(FindGateByKind(r.cu->modules[0]->items, GateKind::kRtran), nullptr);
}

// =============================================================================
// A.4 -- Instantiations
// =============================================================================
TEST(ParserAnnexA, A4ModuleInstPositional) {
  auto r = Parse("module m; sub u0(a, b, c); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "sub");
  EXPECT_EQ(item->inst_name, "u0");
}

TEST(ParserAnnexA, A4ModuleInstNamed) {
  auto r = Parse("module m; sub u0(.clk(clk), .data(data)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_ports.size(), 2u);
}

TEST(ParserAnnexA, A4ModuleInstWithParams) {
  auto r = Parse("module m; sub #(8, 4) u0(.clk(clk)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_params.size(), 2u);
}

TEST(ParserAnnexA, A4GenerateForBlock) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 4; i = i + 1) begin\n"
      "    wire w;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kGenerateFor) found = true;
  }
  EXPECT_TRUE(found);
}

TEST(ParserAnnexA, A4GenerateIfElse) {
  auto r = Parse(
      "module m;\n"
      "  if (WIDTH > 8) begin\n"
      "    wire [15:0] bus;\n"
      "  end else begin\n"
      "    wire [7:0] bus;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kGenerateIf) {
      found = true;
      EXPECT_NE(item->gen_else, nullptr);
    }
  }
  EXPECT_TRUE(found);
}

TEST(ParserAnnexA, A4GenerateCase) {
  auto r = Parse(
      "module m;\n"
      "  case (WIDTH)\n"
      "    8: begin\n"
      "      wire [7:0] d;\n"
      "    end\n"
      "    default: begin\n"
      "      wire [31:0] d;\n"
      "    end\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kGenerateCase);
  EXPECT_EQ(item->gen_case_items.size(), 2u);
}

TEST(ParserAnnexA, A4GenerateRegion) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "    wire w;\n"
      "  endgenerate\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

ModuleItem* FindModuleInst(const std::vector<ModuleItem*>& items) {
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kModuleInst) return item;
  }
  return nullptr;
}

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

TEST(ParserAnnexA0411, OrderedParameterAssignment) {
  auto r = Parse("module m; sub #(8, 4) u0(a); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_params.size(), 2u);
  // Ordered params have empty name
  EXPECT_EQ(item->inst_params[0].first, "");
  EXPECT_EQ(item->inst_params[1].first, "");
}

TEST(ParserAnnexA0411, NamedParameterAssignment) {
  // . parameter_identifier ( [ param_expression ] )
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

TEST(ParserAnnexA0411, NamedParameterEmptyExpression) {
  // . parameter_identifier ( ) — empty param_expression
  auto r = Parse("module m; sub #(.WIDTH()) u0(a); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_params.size(), 1u);
  EXPECT_EQ(item->inst_params[0].first, "WIDTH");
  EXPECT_EQ(item->inst_params[0].second, nullptr);
}

TEST(ParserAnnexA0411, SingleOrderedParam) {
  auto r = Parse("module m; sub #(16) u0(); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_params.size(), 1u);
}

// =============================================================================
// hierarchical_instance ::= name_of_instance ( [ list_of_port_connections ] )
// name_of_instance ::= instance_identifier { unpacked_dimension }
// =============================================================================
TEST(ParserAnnexA0411, InstanceArrayWithRange) {
  // instance_identifier [ left : right ]
  auto r = Parse("module m; sub u0[3:0](.a(a)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_name, "u0");
  EXPECT_NE(item->inst_range_left, nullptr);
  EXPECT_NE(item->inst_range_right, nullptr);
}

TEST(ParserAnnexA0411, InstanceArrayWithSize) {
  // instance_identifier [ size ]
  auto r = Parse("module m; sub u0[4](.a(a)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_name, "u0");
  EXPECT_NE(item->inst_range_left, nullptr);
  EXPECT_EQ(item->inst_range_right, nullptr);
}

TEST(ParserAnnexA0411, EmptyPortList) {
  // hierarchical_instance ::= name_of_instance ( )
  auto r = Parse("module m; sub u0(); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_ports.size(), 0u);
}

// =============================================================================
// list_of_port_connections34 ::=
//   ordered_port_connection { , ordered_port_connection }
//   | named_port_connection { , named_port_connection }
// ordered_port_connection ::= { attribute_instance } [ expression ]
// named_port_connection ::=
//   { attribute_instance } . port_identifier [ ( [ expression ] ) ]
//   | { attribute_instance } . *
// A.10 note 34: .* shall appear at most once
// =============================================================================
TEST(ParserAnnexA0411, OrderedPortConnections) {
  auto r = Parse("module m; sub u0(a, b, c); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_ports.size(), 3u);
  // Ordered ports have empty name
  EXPECT_EQ(item->inst_ports[0].first, "");
  EXPECT_EQ(item->inst_ports[1].first, "");
  EXPECT_EQ(item->inst_ports[2].first, "");
}

TEST(ParserAnnexA0411, OrderedPortBlankPosition) {
  // ordered_port_connection ::= { attribute_instance } [ expression ]
  // A blank position (empty optional expression) is valid
  auto r = Parse("module m; sub u0(a, , c); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_ports.size(), 3u);
  EXPECT_NE(item->inst_ports[0].second, nullptr);  // a
  EXPECT_EQ(item->inst_ports[1].second, nullptr);  // blank
  EXPECT_NE(item->inst_ports[2].second, nullptr);  // c
}

TEST(ParserAnnexA0411, NamedPortConnections) {
  auto r = Parse("module m; sub u0(.clk(clk), .data(d)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_ports.size(), 2u);
  EXPECT_EQ(item->inst_ports[0].first, "clk");
  EXPECT_EQ(item->inst_ports[1].first, "data");
}

TEST(ParserAnnexA0411, NamedPortEmptyExpression) {
  // . port_identifier ( ) — unconnected named port
  auto r = Parse("module m; sub u0(.clk(clk), .nc()); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_ports.size(), 2u);
  EXPECT_EQ(item->inst_ports[1].first, "nc");
  EXPECT_EQ(item->inst_ports[1].second, nullptr);
}

TEST(ParserAnnexA0411, NamedPortWithoutParens) {
  // . port_identifier — no (expr), implicit connection shorthand
  auto r = Parse("module m; sub u0(.clk, .data); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_ports.size(), 2u);
  EXPECT_EQ(item->inst_ports[0].first, "clk");
  EXPECT_EQ(item->inst_ports[1].first, "data");
}

TEST(ParserAnnexA0411, WildcardPortConnection) {
  // . * — wildcard port connection
  auto r = Parse("module m; sub u0(.*); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->inst_wildcard);
}

TEST(ParserAnnexA0411, WildcardWithNamedPorts) {
  // Named ports mixed with .*
  auto r = Parse("module m; sub u0(.clk(clk), .*); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->inst_wildcard);
  EXPECT_EQ(item->inst_ports.size(), 1u);
  EXPECT_EQ(item->inst_ports[0].first, "clk");
}

// =============================================================================
// Combined: parameter_value_assignment + port connections
// =============================================================================
TEST(ParserAnnexA0411, NamedParamsAndNamedPorts) {
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

TEST(ParserAnnexA0411, OrderedParamsNamedPorts) {
  auto r = Parse("module m; sub #(8) u0(.clk(clk)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_params.size(), 1u);
  EXPECT_EQ(item->inst_params[0].first, "");
  EXPECT_EQ(item->inst_ports.size(), 1u);
}

TEST(ParserAnnexA0411, FullCombination) {
  // Named params, instance array, named ports, wildcard
  auto r = Parse(
      "module m;\n"
      "  sub #(.W(8)) u0[3:0](.clk(clk), .*);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_module, "sub");
  EXPECT_EQ(item->inst_name, "u0");
  EXPECT_EQ(item->inst_params.size(), 1u);
  EXPECT_EQ(item->inst_params[0].first, "W");
  EXPECT_NE(item->inst_range_left, nullptr);
  EXPECT_NE(item->inst_range_right, nullptr);
  EXPECT_EQ(item->inst_ports.size(), 1u);
  EXPECT_TRUE(item->inst_wildcard);
}

// =============================================================================
// Elaboration: module instantiation creates hierarchy and binds ports
// =============================================================================
TEST(ParserAnnexA0411, ElaborationModuleInstPortBinding) {
  auto r = Parse(
      "module child(input a, output b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module parent;\n"
      "  wire x, y;\n"
      "  child u0(.a(x), .b(y));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules.size(), 2u);
  auto* inst = FindModuleInst(r.cu->modules[1]->items);
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(inst->inst_module, "child");
  EXPECT_EQ(inst->inst_name, "u0");
  EXPECT_EQ(inst->inst_ports.size(), 2u);
}

TEST(ParserAnnexA0411, ElaborationParamOverrideOrdered) {
  auto r = Parse(
      "module sub #(parameter W = 1)(input [W-1:0] d);\n"
      "endmodule\n"
      "module top;\n"
      "  sub #(8) u0(.d(8'd0));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* inst = FindModuleInst(r.cu->modules[1]->items);
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(inst->inst_params.size(), 1u);
  EXPECT_EQ(inst->inst_params[0].first, "");
  EXPECT_NE(inst->inst_params[0].second, nullptr);
}

TEST(ParserAnnexA0411, ElaborationParamOverrideNamed) {
  auto r = Parse(
      "module sub #(parameter W = 1)(input [W-1:0] d);\n"
      "endmodule\n"
      "module top;\n"
      "  sub #(.W(16)) u0(.d(16'd0));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* inst = FindModuleInst(r.cu->modules[1]->items);
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(inst->inst_params.size(), 1u);
  EXPECT_EQ(inst->inst_params[0].first, "W");
  EXPECT_NE(inst->inst_params[0].second, nullptr);
}

TEST(ParserAnnexA0411, ElaborationInstanceArray) {
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

TEST(ParserAnnexA0411, ElaborationWildcardPortConnection) {
  auto r = Parse(
      "module sub(input a, output b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  wire a, b;\n"
      "  sub u0(.*);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* inst = FindModuleInst(r.cu->modules[1]->items);
  ASSERT_NE(inst, nullptr);
  EXPECT_TRUE(inst->inst_wildcard);
  EXPECT_EQ(inst->inst_ports.size(), 0u);
}

TEST(ParserAnnexA0411, MultipleInstancesSharedParams) {
  auto r = Parse(
      "module sub #(parameter W = 1)(input [W-1:0] d);\n"
      "endmodule\n"
      "module top;\n"
      "  sub #(.W(8)) u0(.d(8'd0)), u1(.d(8'd1));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[1]->items.size(), 2u);
  auto* i0 = r.cu->modules[1]->items[0];
  auto* i1 = r.cu->modules[1]->items[1];
  EXPECT_EQ(i0->inst_module, "sub");
  EXPECT_EQ(i0->inst_params.size(), 1u);
  EXPECT_EQ(i0->inst_params[0].first, "W");
  EXPECT_EQ(i1->inst_module, "sub");
  EXPECT_EQ(i1->inst_params.size(), 1u);
  EXPECT_EQ(i1->inst_params[0].first, "W");
}

RtlirDesign* Elaborate(const std::string& src, ElabFixture& f,
                       std::string_view top = "") {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  auto name = top.empty() ? cu->modules.back()->name : top;
  return elab.Elaborate(name);
}

// =============================================================================
// A.4.1.2 -- Interface instantiation
//
// interface_instantiation ::=
//   interface_identifier [ parameter_value_assignment ]
//     hierarchical_instance { , hierarchical_instance } ;
// =============================================================================
// --- interface_instantiation: basic ---
TEST(ParserAnnexA0412, BasicInterfaceInst) {
  auto r = Parse("module m; my_if u0(.a(a), .b(b)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "my_if");
  EXPECT_EQ(item->inst_name, "u0");
}

// --- interface_instantiation: with parameter_value_assignment ---
TEST(ParserAnnexA0412, InterfaceInstWithParams) {
  auto r = Parse("module m; my_if #(8) u0(.a(a)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "my_if");
  EXPECT_EQ(item->inst_name, "u0");
  ASSERT_EQ(item->inst_params.size(), 1u);
}

// --- interface_instantiation: with named parameter_value_assignment ---
TEST(ParserAnnexA0412, InterfaceInstWithNamedParams) {
  auto r = Parse("module m; my_if #(.W(16)) u0(.a(a)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "my_if");
  ASSERT_EQ(item->inst_params.size(), 1u);
  EXPECT_EQ(item->inst_params[0].first, "W");
}

// --- interface_instantiation: multiple hierarchical_instance ---
TEST(ParserAnnexA0412, MultipleInterfaceInstances) {
  auto r = Parse("module m; my_if u0(.a(a)), u1(.a(b)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
  auto* i0 = r.cu->modules[0]->items[0];
  auto* i1 = r.cu->modules[0]->items[1];
  EXPECT_EQ(i0->inst_module, "my_if");
  EXPECT_EQ(i0->inst_name, "u0");
  EXPECT_EQ(i1->inst_module, "my_if");
  EXPECT_EQ(i1->inst_name, "u1");
}

// --- interface_instantiation: with instance array ---
TEST(ParserAnnexA0412, InterfaceInstArray) {
  auto r = Parse("module m; my_if u0 [3:0] (.a(a)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_module, "my_if");
  EXPECT_NE(item->inst_range_left, nullptr);
  EXPECT_NE(item->inst_range_right, nullptr);
}

// --- interface_instantiation: empty port list ---
TEST(ParserAnnexA0412, InterfaceInstEmptyPorts) {
  auto r = Parse("module m; my_if u0(); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_TRUE(item->inst_ports.empty());
}

// --- interface_instantiation: wildcard port ---
TEST(ParserAnnexA0412, InterfaceInstWildcardPort) {
  auto r = Parse("module m; my_if u0(.*); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->inst_wildcard);
}

// --- interface_instantiation: ordered port connections ---
TEST(ParserAnnexA0412, InterfaceInstOrderedPorts) {
  auto r = Parse("module m; my_if u0(a, b, c); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_ports.size(), 3u);
}

// --- interface_instantiation: interface instantiated inside interface ---
TEST(ParserAnnexA0412, InterfaceInstInsideInterface) {
  auto r = Parse(
      "interface outer_if;\n"
      "  inner_if u0(.clk(clk));\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  ASSERT_GE(r.cu->interfaces[0]->items.size(), 1u);
  auto* item = r.cu->interfaces[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "inner_if");
  EXPECT_EQ(item->inst_name, "u0");
}

// --- interface_instantiation: with empty parameter ---
TEST(ParserAnnexA0412, InterfaceInstEmptyParam) {
  auto r = Parse("module m; my_if #() u0(.a(a)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_module, "my_if");
  EXPECT_TRUE(item->inst_params.empty());
}

// --- interface_instantiation: named port without parentheses ---
TEST(ParserAnnexA0412, InterfaceInstNamedPortNoParens) {
  auto r = Parse("module m; my_if u0(.clk, .rst); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_ports.size(), 2u);
  EXPECT_EQ(item->inst_ports[0].first, "clk");
  EXPECT_EQ(item->inst_ports[1].first, "rst");
}

// =============================================================================
// Elaboration tests -- interface instantiation resolved through elaborator
// =============================================================================
// --- Elaborator resolves interface instantiation within a module ---
TEST(ParserAnnexA0412, ElaborationInterfaceInstInModule) {
  ElabFixture f;
  auto* design = Elaborate(
      "interface my_bus(input logic clk, input logic rst);\n"
      "endinterface\n"
      "module top;\n"
      "  logic clk, rst;\n"
      "  my_bus bus0(.clk(clk), .rst(rst));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  auto* top = design->top_modules[0];
  ASSERT_GE(top->children.size(), 1u);
  EXPECT_EQ(top->children[0].module_name, "my_bus");
  EXPECT_EQ(top->children[0].inst_name, "bus0");
  EXPECT_NE(top->children[0].resolved, nullptr);
}

// --- Elaborator resolves interface instantiation with port bindings ---
TEST(ParserAnnexA0412, ElaborationInterfaceInstPortBindings) {
  ElabFixture f;
  auto* design = Elaborate(
      "interface simple_if(input logic data);\n"
      "endinterface\n"
      "module top;\n"
      "  logic d;\n"
      "  simple_if u0(.data(d));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* top = design->top_modules[0];
  ASSERT_GE(top->children.size(), 1u);
  EXPECT_GE(top->children[0].port_bindings.size(), 1u);
  EXPECT_EQ(top->children[0].port_bindings[0].port_name, "data");
}

// --- Elaborator resolves interface inside interface ---
TEST(ParserAnnexA0412, ElaborationInterfaceInsideInterface) {
  ElabFixture f;
  auto* design = Elaborate(
      "interface inner_if(input logic sig);\n"
      "endinterface\n"
      "interface outer_if;\n"
      "  logic sig;\n"
      "  inner_if u0(.sig(sig));\n"
      "endinterface\n"
      "module top;\n"
      "  outer_if oi();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* top = design->top_modules[0];
  ASSERT_GE(top->children.size(), 1u);
  EXPECT_EQ(top->children[0].module_name, "outer_if");
  auto* outer = top->children[0].resolved;
  ASSERT_NE(outer, nullptr);
  ASSERT_GE(outer->children.size(), 1u);
  EXPECT_EQ(outer->children[0].module_name, "inner_if");
  EXPECT_NE(outer->children[0].resolved, nullptr);
}

// =============================================================================
// A.4.1.3 -- Program instantiation
//
// program_instantiation ::=
//   program_identifier [ parameter_value_assignment ]
//     hierarchical_instance { , hierarchical_instance } ;
// =============================================================================
// --- program_instantiation: basic ---
TEST(ParserAnnexA0413, BasicProgramInst) {
  auto r = Parse(
      "program my_prog(input logic clk);\n"
      "endprogram\n"
      "module m; my_prog u0(.clk(clk)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "my_prog");
  EXPECT_EQ(item->inst_name, "u0");
}

// --- program_instantiation: with parameter_value_assignment (ordered) ---
TEST(ParserAnnexA0413, ProgramInstWithOrderedParams) {
  auto r = Parse(
      "program my_prog #(parameter int W = 8)(input logic [W-1:0] data);\n"
      "endprogram\n"
      "module m; my_prog #(16) u0(.data(d)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "my_prog");
  EXPECT_EQ(item->inst_name, "u0");
  ASSERT_EQ(item->inst_params.size(), 1u);
}

// --- program_instantiation: with named parameter_value_assignment ---
TEST(ParserAnnexA0413, ProgramInstWithNamedParams) {
  auto r = Parse(
      "program my_prog #(parameter int W = 8)(input logic [W-1:0] data);\n"
      "endprogram\n"
      "module m; my_prog #(.W(16)) u0(.data(d)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_module, "my_prog");
  ASSERT_EQ(item->inst_params.size(), 1u);
  EXPECT_EQ(item->inst_params[0].first, "W");
}

// --- program_instantiation: multiple hierarchical_instance ---
TEST(ParserAnnexA0413, MultipleProgramInstances) {
  auto r = Parse(
      "program my_prog(input logic clk);\n"
      "endprogram\n"
      "module m; my_prog u0(.clk(a)), u1(.clk(b)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
  auto* i0 = r.cu->modules[0]->items[0];
  auto* i1 = r.cu->modules[0]->items[1];
  EXPECT_EQ(i0->inst_module, "my_prog");
  EXPECT_EQ(i0->inst_name, "u0");
  EXPECT_EQ(i1->inst_module, "my_prog");
  EXPECT_EQ(i1->inst_name, "u1");
}

// --- program_instantiation: with instance array ---
TEST(ParserAnnexA0413, ProgramInstArray) {
  auto r = Parse(
      "program my_prog(input logic clk);\n"
      "endprogram\n"
      "module m; my_prog u0 [3:0] (.clk(clk)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_module, "my_prog");
  EXPECT_NE(item->inst_range_left, nullptr);
  EXPECT_NE(item->inst_range_right, nullptr);
}

// --- program_instantiation: empty port list ---
TEST(ParserAnnexA0413, ProgramInstEmptyPorts) {
  auto r = Parse(
      "program my_prog;\n"
      "endprogram\n"
      "module m; my_prog u0(); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_TRUE(item->inst_ports.empty());
}

// --- program_instantiation: wildcard port ---
TEST(ParserAnnexA0413, ProgramInstWildcardPort) {
  auto r = Parse(
      "program my_prog(input logic clk);\n"
      "endprogram\n"
      "module m; my_prog u0(.*); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->inst_wildcard);
}

// --- program_instantiation: ordered port connections ---
TEST(ParserAnnexA0413, ProgramInstOrderedPorts) {
  auto r = Parse(
      "program my_prog(input logic a, input logic b, input logic c);\n"
      "endprogram\n"
      "module m; my_prog u0(a, b, c); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_ports.size(), 3u);
}

// --- program_instantiation: named port without parentheses ---
TEST(ParserAnnexA0413, ProgramInstNamedPortNoParens) {
  auto r = Parse(
      "program my_prog(input logic clk, input logic rst);\n"
      "endprogram\n"
      "module m; my_prog u0(.clk, .rst); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_ports.size(), 2u);
  EXPECT_EQ(item->inst_ports[0].first, "clk");
  EXPECT_EQ(item->inst_ports[1].first, "rst");
}

// --- program_instantiation: empty parameter list ---
TEST(ParserAnnexA0413, ProgramInstEmptyParam) {
  auto r = Parse(
      "program my_prog(input logic clk);\n"
      "endprogram\n"
      "module m; my_prog #() u0(.clk(clk)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_module, "my_prog");
  EXPECT_TRUE(item->inst_params.empty());
}

// =============================================================================
// Elaboration tests -- program instantiation resolved through elaborator
// =============================================================================
// --- Elaborator resolves program instantiation within a module ---
TEST(ParserAnnexA0413, ElaborationProgramInstInModule) {
  ElabFixture f;
  auto* design = Elaborate(
      "program my_prog(input logic clk, input logic rst);\n"
      "endprogram\n"
      "module top;\n"
      "  logic clk, rst;\n"
      "  my_prog p0(.clk(clk), .rst(rst));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  auto* top = design->top_modules[0];
  ASSERT_GE(top->children.size(), 1u);
  EXPECT_EQ(top->children[0].module_name, "my_prog");
  EXPECT_EQ(top->children[0].inst_name, "p0");
  EXPECT_NE(top->children[0].resolved, nullptr);
}

}  // namespace
