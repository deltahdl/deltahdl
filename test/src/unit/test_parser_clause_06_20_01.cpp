#include "fixture_elaborator.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

const ModuleItem* FindParamInGenerate(const ModuleItem* item) {
  if (!item) return nullptr;
  for (const auto* child : item->gen_body) {
    if (child->kind == ModuleItemKind::kParamDecl) return child;
    if (const auto* found = FindParamInGenerate(child)) return found;
  }
  if (item->gen_else) {
    if (const auto* found = FindParamInGenerate(item->gen_else)) return found;
  }
  for (const auto& ci : item->gen_case_items) {
    for (const auto* child : ci.body) {
      if (child->kind == ModuleItemKind::kParamDecl) return child;
      if (const auto* found = FindParamInGenerate(child)) return found;
    }
  }
  return nullptr;
}

TEST(ParameterPortListParsing, ParamPortDataTypeForm) {
  auto r = Parse("module m #(int WIDTH = 8); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->params.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->params[0].first, "WIDTH");
}

TEST(ParameterPortListParsing, ParamPortMixedForms) {
  auto r = Parse(
      "module m #(parameter int A = 1, localparam int B = 2,\n"
      "           type T = logic, int C = 3);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->params.size(), 4u);
  EXPECT_EQ(r.cu->modules[0]->params[0].first, "A");
  EXPECT_EQ(r.cu->modules[0]->params[1].first, "B");
  EXPECT_EQ(r.cu->modules[0]->params[2].first, "T");
  EXPECT_EQ(r.cu->modules[0]->params[3].first, "C");
}

TEST(ExpressionParsing, ParamExprBinaryOp) {
  auto r = Parse(
      "module m #(parameter int P = 2 * 8);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->params[0].second->kind, ExprKind::kBinary);
}

TEST(DeclarationListParsing, ListOfParamAssignmentsSingle) {
  auto r = Parse("module m; parameter int A = 1; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kParamDecl);
}

TEST(DeclarationListParsing, ListOfParamAssignmentsMultiple) {
  auto r = Parse("module m; parameter int A = 1, B = 2, C = 3; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kParamDecl) count++;
  }
  EXPECT_GE(count, 3);
}

TEST(DeclarationAssignmentParsing, ParamAssignmentNoDefault) {
  auto r = Parse("module m #(parameter int P); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(DeclarationAssignmentParsing, TypeAssignmentWithDefault) {
  auto r = Parse("module m; parameter type T = int; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(item->name, "T");
}

TEST(ParameterPortListParsing, ParamPortLocalparam) {
  auto r = Parse("module m #(localparam int X = 5); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->params.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->params[0].first, "X");
}

TEST(ModuleParamsParsing, TypedParamPort) {
  auto r = Parse(
      "module m #(parameter int W = 8, int D = 4)(\n"
      "  input logic [W-1:0] data\n"
      ");\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->params.size(), 2u);
}

TEST(ParameterPortListParsing, EmptyParameterPortListParses) {
  auto r = Parse("module m #(); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->params.size(), 0u);
}

TEST(ParameterDeclarations, ClassBodyParameterPromotedToLocalparam) {
  auto r = Parse(
      "class c;\n"
      "  parameter int A = 1;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  ClassMember* prop = nullptr;
  for (auto* m : r.cu->classes[0]->members) {
    if (m->kind == ClassMemberKind::kProperty && m->name == "A") {
      prop = m;
      break;
    }
  }
  ASSERT_NE(prop, nullptr);
}

TEST(ParameterDeclarations, PackageBodyParameterPromotedToLocalparam) {
  auto r = Parse(
      "package p;\n"
      "  parameter int K = 7;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  ModuleItem* item = nullptr;
  for (auto* it : r.cu->packages[0]->items) {
    if (it->kind == ModuleItemKind::kParamDecl && it->name == "K") {
      item = it;
      break;
    }
  }
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->is_localparam);
}

TEST(ParameterDeclarations, CompilationUnitParameterPromotedToLocalparam) {
  auto r = Parse("parameter int X = 42;\nmodule m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->cu_items.size(), 1u);
  EXPECT_EQ(r.cu->cu_items[0]->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(r.cu->cu_items[0]->name, "X");
  EXPECT_TRUE(r.cu->cu_items[0]->is_localparam);
}

TEST(ParameterPortListParsing, LocalparamPortRequiresDefaultValue) {
  auto r = Parse("module m #(localparam int X); endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ParameterPortListParsing, LocalparamTypePortRequiresDefaultType) {
  auto r = Parse("module m #(localparam type T); endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ParameterDeclarations, ParameterPromotedToLocalparamInGenerateIf) {
  auto r = Parse(
      "module m;\n"
      "  if (1) begin : blk\n"
      "    parameter int P = 7;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  ASSERT_EQ(gen->kind, ModuleItemKind::kGenerateIf);
  const auto* p = FindParamInGenerate(gen);
  ASSERT_NE(p, nullptr);
  EXPECT_TRUE(p->is_localparam);
}

TEST(ParameterDeclarations, ParameterPromotedToLocalparamInGenerateFor) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 2; i = i + 1) begin\n"
      "    parameter int Q = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[1];
  ASSERT_EQ(gen->kind, ModuleItemKind::kGenerateFor);
  const auto* p = FindParamInGenerate(gen);
  ASSERT_NE(p, nullptr);
  EXPECT_TRUE(p->is_localparam);
}

TEST(ParameterDeclarations, ParameterPromotedToLocalparamInGenerateCase) {
  auto r = Parse(
      "module m;\n"
      "  case (1)\n"
      "    1: begin parameter int R = 2; end\n"
      "    default: ;\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  ASSERT_EQ(gen->kind, ModuleItemKind::kGenerateCase);
  const auto* p = FindParamInGenerate(gen);
  ASSERT_NE(p, nullptr);
  EXPECT_TRUE(p->is_localparam);
}

TEST(ParameterDeclarations, ParameterPromotedInNestedGenerateBlock) {
  auto r = Parse(
      "module m;\n"
      "  if (1) begin\n"
      "    if (1) begin\n"
      "      parameter int S = 3;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* outer = r.cu->modules[0]->items[0];
  const auto* p = FindParamInGenerate(outer);
  ASSERT_NE(p, nullptr);
  EXPECT_TRUE(p->is_localparam);
}

TEST(ParameterDeclarations, ParameterPromotedInSingleItemGenerateBody) {
  auto r = Parse(
      "module m;\n"
      "  if (1) parameter int P = 4;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  ASSERT_EQ(gen->kind, ModuleItemKind::kGenerateIf);
  const auto* p = FindParamInGenerate(gen);
  ASSERT_NE(p, nullptr);
  EXPECT_TRUE(p->is_localparam);
}

TEST(ParameterDeclarations, ParameterAtModuleScopeNotPromoted) {
  auto r = Parse(
      "module m;\n"
      "  parameter int P = 5;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_FALSE(item->is_localparam);
}

TEST(ParameterDeclarations, InterfaceBodyParameterParses) {
  auto r = Parse(
      "interface i;\n"
      "  parameter int K = 4;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  ModuleItem* item = nullptr;
  for (auto* it : r.cu->interfaces[0]->items) {
    if (it->kind == ModuleItemKind::kParamDecl && it->name == "K") {
      item = it;
      break;
    }
  }
  ASSERT_NE(item, nullptr);
  EXPECT_FALSE(item->is_localparam);
}

TEST(ParameterDeclarations, ProgramBodyParameterParses) {
  auto r = Parse(
      "program p;\n"
      "  parameter int Q = 9;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  ModuleItem* item = nullptr;
  for (auto* it : r.cu->programs[0]->items) {
    if (it->kind == ModuleItemKind::kParamDecl && it->name == "Q") {
      item = it;
      break;
    }
  }
  ASSERT_NE(item, nullptr);
  EXPECT_FALSE(item->is_localparam);
}

TEST(ParameterPortListParsing, TypeAssignmentNoDefaultParses) {
  auto r = Parse("module m #(parameter type T)(); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->params.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->params[0].first, "T");
}

TEST(DeclarationAssignmentParsing, BodyTypeAssignmentRequiresDefault) {
  auto r = Parse(
      "module m;\n"
      "  parameter type T;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(DeclarationAssignmentParsing, BodyForwardTypeParameterParses) {
  auto r = Parse("module m; parameter type enum ET = int; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(item->name, "ET");
  EXPECT_EQ(item->forward_type_kind, DataTypeKind::kEnum);
}

TEST(ParameterPortListParsing, ForwardTypeParameterPortVariants) {
  auto r = Parse(
      "module m #(parameter type enum ET, type struct ST, type union UT,\n"
      "           type class CT, type interface class IT)();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->params.size(), 5u);
  for (const char* n : {"ET", "ST", "UT", "CT", "IT"}) {
    EXPECT_EQ(mod->type_param_names.count(n), 1u);
  }
}

// local_parameter_declaration ::= localparam type_parameter_declaration
TEST(DeclarationListParsing, LocalparamTypeParameterDeclaration) {
  auto r = Parse("module m; localparam type T = int; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(item->name, "T");
  EXPECT_TRUE(item->is_localparam);
}

// list_of_type_assignments ::= type_assignment { , type_assignment }
TEST(DeclarationListParsing, ListOfTypeAssignmentsMultiple) {
  auto r = Parse("module m; parameter type T = int, U = logic; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kParamDecl &&
        (item->name == "T" || item->name == "U"))
      count++;
  }
  EXPECT_EQ(count, 2);
}

// param_assignment ::= parameter_identifier { variable_dimension }
//                      [ = constant_param_expression ]
TEST(DeclarationAssignmentParsing, ParamAssignmentWithVariableDimension) {
  auto r =
      Parse("module m; localparam int arr [0:2] = '{1, 2, 3}; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kParamDecl);
  EXPECT_EQ(item->name, "arr");
  EXPECT_GE(item->unpacked_dims.size(), 1u);
}

// specparam_declaration ::= specparam [ packed_dimension ]
//                           list_of_specparam_assignments ;
// list_of_specparam_assignments ::= specparam_assignment { ,
// specparam_assignment } specparam_assignment ::= specparam_identifier =
// constant_mintypmax_expression
TEST(DeclarationListParsing, SpecparamDeclarationWithPackedDimAndList) {
  auto r = Parse("module m; specparam [3:0] d1 = 5, d2 = 10; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int specparam_count = 0;
  ModuleItem* first = nullptr;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kSpecparam) {
      if (!first) first = item;
      specparam_count++;
    }
  }
  EXPECT_EQ(specparam_count, 2);
  ASSERT_NE(first, nullptr);
  EXPECT_NE(first->data_type.packed_dim_left, nullptr);
  EXPECT_NE(first->init_expr, nullptr);
}

// parameter_port_declaration ::= data_type list_of_param_assignments — a port
// parameter may omit its own type and inherit an implicit type, a later
// parameter may depend on an earlier one, and a value parameter may be typed
// by a preceding type parameter. Mirrors the multi-parameter port-list example
// in the clause text.
TEST(ParameterPortListParsing, ImplicitTypeAndTypeParameterPorts) {
  auto r = Parse(
      "module mc #(int N = 5, M = N * 16, type T = int, T x = 0)();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->params.size(), 4u);
  EXPECT_EQ(mod->params[0].first, "N");
  EXPECT_EQ(mod->params[1].first, "M");
  EXPECT_EQ(mod->params[2].first, "T");
  EXPECT_EQ(mod->params[3].first, "x");
  EXPECT_EQ(mod->type_param_names.count("T"), 1u);
  // The implicit-typed parameter still carries a dependent default expression.
  EXPECT_NE(mod->params[1].second, nullptr);
}

// Footnote to the parameter declaration syntax: omitting the default type of a
// localparam type parameter is only illegal inside a parameter_port_list, so
// the same declaration is legal once a default is supplied.
TEST(ParameterPortListParsing, LocalparamTypePortWithDefaultParses) {
  auto r = Parse("module m #(localparam type T = int)(); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  EXPECT_EQ(mod->type_param_names.count("T"), 1u);
  EXPECT_EQ(mod->localparam_port_names.count("T"), 1u);
}

}  // namespace
