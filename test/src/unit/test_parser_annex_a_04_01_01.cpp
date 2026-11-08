#include <gtest/gtest.h>

#include <utility>
#include <vector>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

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

TEST(ModuleInstantiationGrammar, WildcardPortConnection) {
  auto r = Parse("module m; sub u0(.*); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_TRUE(item->inst_wildcard);
  EXPECT_EQ(item->inst_ports.size(), 0u);
}

TEST(ModuleInstantiationGrammar, ErrorDuplicateWildcardPort) {
  auto r = Parse("module m; sub u0(.*, .*); endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, ".* already appears earlier in this port connection list", 1,
      "23.3.2"));
}

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

TEST(ModuleInstantiationGrammar, ErrorOrderedAndNamedPortsCannotMix) {
  auto r = Parse("module m; sub u0(a, .b(c)); endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "ordered and named port connections cannot be mixed", 1,
      "23.3.2"));
}

TEST(ModuleInstantiationGrammar, ErrorOrderedAndNamedParamsCannotMix) {
  auto r = Parse("module m; sub #(8, .D(4)) u0(a); endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "ordered and named parameter value assignments cannot be mixed",
      1, "23.3.2"));
}

TEST(ModuleInstantiationGrammar, NoInstanceNameReadsAsAnUnresolvedUdpInstance) {
  auto r = Parse("module m; sub(a, b); endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules[0]->items.size(), 1u);
  const auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kUdpInst);
  EXPECT_TRUE(item->udp_undeclared_at_parse);
}

TEST(ModuleInstantiationGrammar, MissingPortParenthesesLeavesADataDeclaration) {
  auto r = Parse("module m; sub u0; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->data_type.type_name, "sub");
  EXPECT_TRUE(item->type_name_undeclared_at_parse);
}

TEST(ModuleInstantiationGrammar, ErrorMissingSemicolon) {
  auto r = Parse("module m; sub u0(a) endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got 'endmodule'", 1, "23.3.2"));
}

TEST(ModuleInstantiationParsing, EscapedInstanceName) {
  auto r = Parse(
      "module sub(input a, output b); endmodule\n"
      "module m;\n"
      "  sub \\u.1 (x, y);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* inst =
      FindItemByKind(r.cu->modules[1]->items, ModuleItemKind::kModuleInst);
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(inst->inst_name, "u.1");
}

TEST(ModuleInstantiationParsing, ParamExpressionMinTypMax) {
  auto r = Parse(
      "module sub #(parameter int W = 1) (); endmodule\n"
      "module m;\n"
      "  sub #(1:2:3) u1();\n"
      "  sub #(.W(4:5:6)) u2();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  std::vector<ModuleItem*> insts;
  for (auto* item : r.cu->modules[1]->items) {
    if (item->kind == ModuleItemKind::kModuleInst) insts.push_back(item);
  }
  ASSERT_EQ(insts.size(), 2u);
  ASSERT_EQ(insts[0]->inst_params.size(), 1u);
  ASSERT_NE(insts[0]->inst_params[0].second, nullptr);
  EXPECT_EQ(insts[0]->inst_params[0].second->kind, ExprKind::kMinTypMax);
  ASSERT_EQ(insts[1]->inst_params.size(), 1u);
  EXPECT_EQ(insts[1]->inst_params[0].first, "W");
  ASSERT_NE(insts[1]->inst_params[0].second, nullptr);
  EXPECT_EQ(insts[1]->inst_params[0].second->kind, ExprKind::kMinTypMax);
}

TEST(ModuleInstantiationParsing, ParamExpressionDataTypeNoExpressionSpells) {
  auto r = Parse(
      "module m;\n"
      "  sub #(int unsigned) u1();\n"
      "  sub #(.T(struct packed { bit a; byte b; })) u2();\n"
      "  initial x = C#(enum {A, B})::x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  std::vector<ModuleItem*> insts;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kModuleInst) insts.push_back(item);
  }
  ASSERT_EQ(insts.size(), 2u);
  const std::pair<const ModuleItem*, DataTypeKind> kWanted[] = {
      {insts[0], DataTypeKind::kInt}, {insts[1], DataTypeKind::kStruct}};
  for (const auto& [inst, kind] : kWanted) {
    ASSERT_EQ(inst->inst_params.size(), 1u);
    const Expr* value = inst->inst_params[0].second;
    ASSERT_NE(value, nullptr);
    ASSERT_EQ(value->kind, ExprKind::kTypeRef);
    ASSERT_NE(value->type_value, nullptr);
    EXPECT_EQ(value->type_value->kind, kind);
  }
  const Expr* rhs = FirstInitialRHS(r);
  ASSERT_NE(rhs, nullptr);
  ASSERT_EQ(rhs->kind, ExprKind::kMemberAccess);
  ASSERT_EQ(rhs->lhs->elements.size(), 1u);
  ASSERT_EQ(rhs->lhs->elements[0]->kind, ExprKind::kTypeRef);
  ASSERT_NE(rhs->lhs->elements[0]->type_value, nullptr);
  EXPECT_EQ(rhs->lhs->elements[0]->type_value->kind, DataTypeKind::kEnum);
}

}  // namespace
