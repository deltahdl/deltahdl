#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserClause03, Cl3_13_ModuleAndPackageInDefinitionNameSpace) {
  auto r = ParseWithPreprocessor(
      "package my_pkg;\n"
      "  typedef int myint;\n"
      "endpackage\n"
      "module my_mod;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "my_pkg");
  EXPECT_EQ(r.cu->modules[0]->name, "my_mod");
}

static bool HasItemOfKindAndName(const std::vector<ModuleItem*>& items,
                                 ModuleItemKind kind, const std::string& name) {
  for (const auto* item : items)
    if (item->kind == kind && item->name == name) return true;
  return false;
}

TEST(ParserClause03, Cl3_13_SameNameVarsInDifferentModules) {
  auto r = ParseWithPreprocessor(
      "module a;\n"
      "  logic [7:0] data;\n"
      "endmodule\n"
      "module b;\n"
      "  logic [7:0] data;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 2u);

  EXPECT_TRUE(HasItemOfKindAndName(r.cu->modules[0]->items,
                                   ModuleItemKind::kVarDecl, "data"));
  EXPECT_TRUE(HasItemOfKindAndName(r.cu->modules[1]->items,
                                   ModuleItemKind::kVarDecl, "data"));
}

TEST(ParserClause03, Cl3_13_TaskAndFunctionInSameModule) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  function int add(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "  task do_work(input int x);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  bool found_func = false;
  bool found_task = false;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kFunctionDecl && item->name == "add")
      found_func = true;
    if (item->kind == ModuleItemKind::kTaskDecl && item->name == "do_work")
      found_task = true;
  }
  EXPECT_TRUE(found_func);
  EXPECT_TRUE(found_task);
}

TEST(ParserClause03, Cl3_13_PortNamesInModuleScope) {
  auto r = ParseWithPreprocessor(
      "module m (input logic clk, input logic rst_n, output logic [7:0] q);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 3u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "clk");
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInput);
  EXPECT_EQ(r.cu->modules[0]->ports[1].name, "rst_n");
  EXPECT_EQ(r.cu->modules[0]->ports[1].direction, Direction::kInput);
  EXPECT_EQ(r.cu->modules[0]->ports[2].name, "q");
  EXPECT_EQ(r.cu->modules[0]->ports[2].direction, Direction::kOutput);
}

static bool HasAttrNamed(const std::vector<ModuleItem*>& items,
                         const std::string& name) {
  for (const auto* item : items)
    for (const auto& attr : item->attrs)
      if (attr.name == name) return true;
  return false;
}

TEST(ParserClause03, Cl3_13_AllEightNameSpaces) {
  auto r = ParseWithPreprocessor(

      "`define VAL 1\n"

      "package pkg; int x; endpackage\n"

      "function automatic int cu_fn(int a); return a; endfunction\n"

      "module m (input logic clk, output logic q);\n"
      "  (* keep *) logic flag;\n"
      "  import pkg::*;\n"
      "  always_ff @(posedge clk) begin : blk\n"
      "    int cnt;\n"
      "    cnt = `VAL;\n"
      "    q <= flag;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "pkg");

  ASSERT_GE(r.cu->cu_items.size(), 1u);
  EXPECT_EQ(r.cu->cu_items[0]->name, "cu_fn");

  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "m");

  ASSERT_EQ(r.cu->modules[0]->ports.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "clk");

  EXPECT_TRUE(HasAttrNamed(r.cu->modules[0]->items, "keep"));
}

}  // namespace
