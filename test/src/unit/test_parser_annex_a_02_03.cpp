#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(DeclarationListParsing, ListOfVariablePortIdentifiersSingle) {
  auto r = Parse("module m(output logic q = 1'b0); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& port = r.cu->modules[0]->ports[0];
  EXPECT_EQ(port.direction, Direction::kOutput);
  EXPECT_NE(port.default_value, nullptr);
}

TEST(DeclarationListParsing, ListOfTfVariableIdentifiersMultiple) {
  auto r = Parse(
      "module m;\n"
      "  function int add;\n"
      "    input int a, b;\n"
      "    add = a + b;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(item->func_args.size(), 2u);
  EXPECT_EQ(item->func_args[0].name, "a");
  EXPECT_EQ(item->func_args[1].name, "b");
}

TEST(DeclarationListParsing, ListOfTfVariableIdentifiersSingle) {
  auto r = Parse(
      "module m;\n"
      "  function int f;\n"
      "    input int a;\n"
      "    f = a;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(item->func_args.size(), 1u);
}

TEST(DeclarationListParsing, ListOfTypeAssignmentsMultiple) {
  auto r = Parse(
      "module m; parameter type T1 = int, T2 = real, T3 = string; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kParamDecl) count++;
  }
  EXPECT_GE(count, 3);
}

TEST(DeclarationListParsing, ListOfUdpPortIdentifiersSingle) {
  auto r = Parse(
      "primitive buf_p(output out, input in);\n"
      "  table 0 : 0; 1 : 1; endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(DeclarationListParsing, ListOfUdpPortIdentifiersMultiple) {
  auto r = Parse(
      "primitive mux_p(output out, input a, b, sel);\n"
      "  table 1 0 0 : 1; 0 1 1 : 1; endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(DeclarationListParsing, ListOfDefparamAssignments) {
  auto r = Parse(
      "module m;\n"
      "  defparam u.A = 1, u.B = 2, u.C = 3;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kDefparam);
  EXPECT_EQ(item->defparam_assigns.size(), 3u);
}

TEST(DeclarationListParsing, ListOfDefparamAssignmentsSingle) {
  auto r = Parse(
      "module m;\n"
      "  defparam u.P = 10;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->defparam_assigns.size(), 1u);
}

TEST(DeclarationListParsing, ListOfGenvarIdentifiersMultiple) {
  auto r = Parse("module m; genvar i, j, k; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->name == "i" || item->name == "j" || item->name == "k") count++;
  }
  EXPECT_EQ(count, 3);
}

TEST(DeclarationListParsing, ListOfGenvarIdentifiersSingle) {
  auto r = Parse("module m; genvar i; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(DeclarationListParsing, ListOfNetDeclAssignmentsMultiple) {
  auto r = Parse("module m; wire a, b, c; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kNetDecl) count++;
  }
  EXPECT_EQ(count, 3);
}

TEST(DeclarationListParsing, ListOfParamAssignmentsMultiple) {
  auto r = Parse("module m; parameter A = 1, B = 2, C = 3; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kParamDecl) count++;
  }
  EXPECT_EQ(count, 3);
}

TEST(DeclarationListParsing, ListOfParamAssignmentsSingle) {
  auto r = Parse("module m; parameter X = 42; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(DeclarationListParsing, ListOfPortIdentifiersMultiple) {
  auto r = Parse("module m(input logic a, input logic b); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "a");
  EXPECT_EQ(r.cu->modules[0]->ports[1].name, "b");
}

TEST(DeclarationListParsing, ListOfVariablePortIdentifiersMultiple) {
  auto r = Parse(
      "module m(output logic a = 1'b0, output logic b = 1'b1); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 2u);
  EXPECT_NE(r.cu->modules[0]->ports[0].default_value, nullptr);
  EXPECT_NE(r.cu->modules[0]->ports[1].default_value, nullptr);
}

TEST(DeclarationListParsing, ListOfSpecparamAssignmentsMultiple) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam A = 1, B = 2, C = 3;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->kind, ModuleItemKind::kSpecifyBlock);
  int count = 0;
  for (auto* sp : item->specify_items) {
    if (sp->kind == SpecifyItemKind::kSpecparam) count++;
  }
  EXPECT_EQ(count, 3);
}

TEST(DeclarationListParsing, ListOfVariableDeclAssignmentsMultiple) {
  auto r = Parse(
      "module m;\n"
      "  int a = 1, b = 2, c = 3;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kVarDecl && item->init_expr != nullptr) {
      count++;
    }
  }
  EXPECT_EQ(count, 3);
}

TEST(DeclarationListParsing, ListOfVariableIdentifiersBareMultiple) {
  auto r = Parse(
      "module m;\n"
      "  logic x, y, z;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kVarDecl && item->init_expr == nullptr) {
      count++;
    }
  }
  EXPECT_EQ(count, 3);
}

TEST(DeclarationListParsing, ListOfInterfaceIdentifiersMultiple) {
  auto r = Parse(
      "module m(interface a, interface b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 2u);
  EXPECT_TRUE(r.cu->modules[0]->ports[0].is_interface_port);
  EXPECT_TRUE(r.cu->modules[0]->ports[1].is_interface_port);
}

TEST(DeclarationListParsing, ListOfNetDeclAssignmentsWithInit) {
  auto r = Parse("module m; wire a = 1'b0, b = 1'b1; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int with_init = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kNetDecl && item->init_expr != nullptr) {
      with_init++;
    }
  }
  EXPECT_EQ(with_init, 2);
}

TEST(DeclarationListParsing, ListOfVariableIdentifiersWithDims) {
  auto r = Parse(
      "module m;\n"
      "  logic x [3:0], y [1:0];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int sized = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kVarDecl &&
        !item->unpacked_dims.empty()) {
      sized++;
    }
  }
  EXPECT_EQ(sized, 2);
}

TEST(DeclarationListParsing, ListOfTfVariableIdentifiersWithDefault) {
  auto r = Parse(
      "module m;\n"
      "  function int f;\n"
      "    input int a = 1, b = 2;\n"
      "    f = a + b;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* fn = r.cu->modules[0]->items[0];
  ASSERT_EQ(fn->kind, ModuleItemKind::kFunctionDecl);
  ASSERT_EQ(fn->func_args.size(), 2u);
  EXPECT_NE(fn->func_args[0].default_value, nullptr);
  EXPECT_NE(fn->func_args[1].default_value, nullptr);
}

TEST(DeclarationListParsing, ListOfSpecparamAssignmentsSingle) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    specparam X = 1;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->kind, ModuleItemKind::kSpecifyBlock);
  int count = 0;
  for (auto* sp : item->specify_items) {
    if (sp->kind == SpecifyItemKind::kSpecparam) count++;
  }
  EXPECT_EQ(count, 1);
}

TEST(DeclarationListParsing, ListOfTypeAssignmentsSingle) {
  auto r = Parse("module m; parameter type T = int; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kParamDecl && item->name == "T") count++;
  }
  EXPECT_EQ(count, 1);
}

TEST(DeclarationListParsing, ListOfPortIdentifiersPerElementUnpackedDim) {
  auto r = Parse("module m(input logic a [3:0], b [1:0]); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 2u);
  EXPECT_FALSE(r.cu->modules[0]->ports[0].unpacked_dims.empty());
  EXPECT_FALSE(r.cu->modules[0]->ports[1].unpacked_dims.empty());
}

// list_of_interface_identifiers admits `{ unpacked_dimension }` on each
// interface identifier; observe the per-element dim being carried through.
TEST(DeclarationListParsing, ListOfInterfaceIdentifiersWithUnpackedDim) {
  auto r = Parse("module m(interface a [3:0], interface b [1:0]); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 2u);
  EXPECT_TRUE(r.cu->modules[0]->ports[0].is_interface_port);
  EXPECT_FALSE(r.cu->modules[0]->ports[0].unpacked_dims.empty());
  EXPECT_TRUE(r.cu->modules[0]->ports[1].is_interface_port);
  EXPECT_FALSE(r.cu->modules[0]->ports[1].unpacked_dims.empty());
}

// list_of_tf_variable_identifiers admits `{ variable_dimension }` on each
// port_identifier; observe a dim carried on a list element of a tf arg list.
TEST(DeclarationListParsing, ListOfTfVariableIdentifiersWithDim) {
  auto r = Parse(
      "module m;\n"
      "  function int f;\n"
      "    input int a [2], b;\n"
      "    f = a[0];\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* fn = r.cu->modules[0]->items[0];
  ASSERT_EQ(fn->kind, ModuleItemKind::kFunctionDecl);
  ASSERT_EQ(fn->func_args.size(), 2u);
  EXPECT_FALSE(fn->func_args[0].unpacked_dims.empty());
  EXPECT_TRUE(fn->func_args[1].unpacked_dims.empty());
}

TEST(DeclarationListParsing, ListOfDefparamAssignmentsTrailingCommaErrors) {
  auto r = Parse(
      "module m;\n"
      "  defparam u.A = 1, ;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
