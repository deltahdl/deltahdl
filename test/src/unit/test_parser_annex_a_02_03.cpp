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

TEST(DeclarationListParsing, ListOfNetDeclAssignmentsWithInit) {
  auto r = Parse("module m; wire a = 1'b0, b = 1'b1; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* a = r.cu->modules[0]->items[0];
  auto* b = r.cu->modules[0]->items[1];
  EXPECT_NE(a->init_expr, nullptr);
  EXPECT_NE(b->init_expr, nullptr);
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

TEST(DeclarationListParsing, ListOfVariableDeclAssignmentsMultiple) {
  auto r = Parse("module m; logic a, b, c; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kVarDecl) count++;
  }
  EXPECT_EQ(count, 3);
}

TEST(DeclarationListParsing, ListOfVariableDeclAssignmentsWithInit) {
  auto r = Parse("module m; int x = 0, y = 1; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* x = r.cu->modules[0]->items[0];
  auto* y = r.cu->modules[0]->items[1];
  EXPECT_NE(x->init_expr, nullptr);
  EXPECT_NE(y->init_expr, nullptr);
}

TEST(DeclarationListParsing, ListOfVariableIdentifiersWithDims) {
  auto r = Parse("module m; logic [7:0] a [3:0], b [1:0]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* a = r.cu->modules[0]->items[0];
  auto* b = r.cu->modules[0]->items[1];
  EXPECT_FALSE(a->unpacked_dims.empty());
  EXPECT_FALSE(b->unpacked_dims.empty());
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

}  // namespace
