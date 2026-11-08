#include <gtest/gtest.h>

#include <vector>

#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

ModuleItem* FindModuleInst(const std::vector<ModuleItem*>& items) {
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kModuleInst) return item;
  }
  return nullptr;
}

TEST(ModuleInstantiationGrammar, NamedPortConnections) {
  auto r = Parse("module m; sub u0(.clk(clk), .data(d)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_ports.size(), 2u);
  EXPECT_EQ(item->inst_ports[0].first, "clk");
  EXPECT_EQ(item->inst_ports[1].first, "data");
}

TEST(ModuleInstantiationGrammar, NamedPortConnectionWithChildModule) {
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

TEST(ModuleInstantiationGrammar, NamedPortEmptyConnection) {
  auto r = Parse(
      "module top;\n"
      "  sub u1 (.a(x), .b());\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_ports.size(), 2);
  EXPECT_EQ(item->inst_ports[0].first, "a");
  EXPECT_NE(item->inst_ports[0].second, nullptr);
  EXPECT_EQ(item->inst_ports[1].first, "b");
  EXPECT_EQ(item->inst_ports[1].second, nullptr);
}

TEST(ModuleInstantiationGrammar, NamedPortNameCannotBeBitSelect) {
  auto r = Parse(
      "module top;\n"
      "  sub u1 (.a[0](x));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags, "expected ')', got '['", 2, "23.3.2"));
}

TEST(ModuleInstantiationGrammar, NamedPortNameCannotBePartSelect) {
  auto r = Parse(
      "module top;\n"
      "  sub u1 (.a[1:0](x));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags, "expected ')', got '['", 2, "23.3.2"));
}

TEST(ModuleInstantiationGrammar, NamedPortNameCannotBeConcatenation) {
  auto r = Parse(
      "module top;\n"
      "  sub u1 (.{a, b}(x));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got '{'", 2, "23.3.2.2"));
}

TEST(ModuleInstantiationGrammar, NamedPortWithConcatenation) {
  auto r = Parse(
      "module top;\n"
      "  sub u1 (.data({a, b, c}));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_ports.size(), 1);
  EXPECT_EQ(item->inst_ports[0].first, "data");
  ASSERT_NE(item->inst_ports[0].second, nullptr);
  EXPECT_EQ(item->inst_ports[0].second->kind, ExprKind::kConcatenation);
}

}  // namespace
