// §3.13: Name spaces

#include <gtest/gtest.h>
#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

struct ParseResult313 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

static ParseResult313 Parse(const std::string &src) {
  ParseResult313 result;
  DiagEngine diag(result.mgr);
  auto fid = result.mgr.AddFile("<test>", src);
  Preprocessor preproc(result.mgr, diag, {});
  auto pp = preproc.Preprocess(fid);
  auto pp_fid = result.mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(result.mgr.FileContent(pp_fid), pp_fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static bool ParseOk(const std::string &src) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", src);
  Preprocessor preproc(mgr, diag, {});
  auto pp = preproc.Preprocess(fid);
  auto pp_fid = mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(mgr.FileContent(pp_fid), pp_fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

static bool HasItemOfKindAndName(const std::vector<ModuleItem *> &items,
                                 ModuleItemKind kind, const std::string &name) {
  for (const auto *item : items)
    if (item->kind == kind && item->name == name) return true;
  return false;
}

static bool HasAttrNamed(const std::vector<ModuleItem *> &items,
                         const std::string &name) {
  for (const auto *item : items)
    for (const auto &attr : item->attrs)
      if (attr.name == name) return true;
  return false;
}

namespace {

// =============================================================================
// LRM §3.13 — Name spaces
// =============================================================================
// 1. Module and package in definition name space (can coexist without conflict)
TEST(ParserClause03, Cl3_13_ModuleAndPackageInDefinitionNameSpace) {
  auto r = Parse(
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

// 2. Same-name variables in different modules (separate scopes)
TEST(ParserClause03, Cl3_13_SameNameVarsInDifferentModules) {
  auto r = Parse(
      "module a;\n"
      "  logic [7:0] data;\n"
      "endmodule\n"
      "module b;\n"
      "  logic [7:0] data;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 2u);
  // Both modules should have a 'data' variable in their own scope.
  EXPECT_TRUE(HasItemOfKindAndName(r.cu->modules[0]->items,
                                   ModuleItemKind::kVarDecl, "data"));
  EXPECT_TRUE(HasItemOfKindAndName(r.cu->modules[1]->items,
                                   ModuleItemKind::kVarDecl, "data"));
}

// 6. Task and function names in same module scope
TEST(ParserClause03, Cl3_13_TaskAndFunctionInSameModule) {
  auto r = Parse(
      "module m;\n"
      "  function int add(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "  task do_work(input int x);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *mod = r.cu->modules[0];
  bool found_func = false;
  bool found_task = false;
  for (auto *item : mod->items) {
    if (item->kind == ModuleItemKind::kFunctionDecl && item->name == "add")
      found_func = true;
    if (item->kind == ModuleItemKind::kTaskDecl && item->name == "do_work")
      found_task = true;
  }
  EXPECT_TRUE(found_func);
  EXPECT_TRUE(found_task);
}

// 7. Variable name same as module name (different name spaces)
TEST(ParserClause03, Cl3_13_VarNameSameAsModuleName) {
  // A variable named 'top' inside module 'top' is legal because
  // the definition name space and the local scope are distinct.
  EXPECT_TRUE(
      ParseOk("module top;\n"
              "  logic top;\n"
              "endmodule\n"));
}

// 18. $unit scope -- declarations outside any module/package
TEST(ParserClause03, Cl3_13_UnitScopeDeclarations) {
  auto r = Parse(
      "function automatic int helper(int x);\n"
      "  return x + 1;\n"
      "endfunction\n"
      "task automatic global_task(input int v);\n"
      "endtask\n"
      "module m;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->cu_items.size(), 2u);
  EXPECT_EQ(r.cu->cu_items[0]->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(r.cu->cu_items[0]->name, "helper");
  EXPECT_EQ(r.cu->cu_items[1]->kind, ModuleItemKind::kTaskDecl);
  EXPECT_EQ(r.cu->cu_items[1]->name, "global_task");
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

// 33. All 8 name spaces coexist in a single compilation unit
TEST(ParserClause03, Cl3_13_AllEightNameSpaces) {
  auto r = Parse(
      // (d) Text macro name space
      "`define VAL 1\n"
      // (b) Package name space
      "package pkg; int x; endpackage\n"
      // (c) Compilation-unit scope name space
      "function automatic int cu_fn(int a); return a; endfunction\n"
      // (a) Definitions name space: module, interface, program, primitive
      "module m (input logic clk, output logic q);\n"  // (g) Port name space
      "  (* keep *) logic flag;\n"                // (h) Attribute name space
      "  import pkg::*;\n"                        // (e) Module name space
      "  always_ff @(posedge clk) begin : blk\n"  // (f) Block name space
      "    int cnt;\n"
      "    cnt = `VAL;\n"
      "    q <= flag;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  // (b) Package name space
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "pkg");
  // (c) Compilation-unit scope
  ASSERT_GE(r.cu->cu_items.size(), 1u);
  EXPECT_EQ(r.cu->cu_items[0]->name, "cu_fn");
  // (a) Definitions name space
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
  // (g) Port name space
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "clk");
  // (h) Attribute name space
  EXPECT_TRUE(HasAttrNamed(r.cu->modules[0]->items, "keep"));
}

}  // namespace
