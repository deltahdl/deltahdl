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
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult313 Parse(const std::string& src) {
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

static bool ParseOk(const std::string& src) {
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

static bool HasItemOfKindAndName(const std::vector<ModuleItem*>& items,
                                 ModuleItemKind kind, const std::string& name) {
  for (const auto* item : items)
    if (item->kind == kind && item->name == name) return true;
  return false;
}

static bool HasAttrNamed(const std::vector<ModuleItem*>& items,
                         const std::string& name) {
  for (const auto* item : items)
    for (const auto& attr : item->attrs)
      if (attr.name == name) return true;
  return false;
}

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

// 3. Named begin-end block creating a subscope
TEST(ParserClause03, Cl3_13_NamedBeginEndBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : my_block\n"
      "    int x;\n"
      "    x = 1;\n"
      "  end : my_block\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* mod = r.cu->modules[0];
  ASSERT_GE(mod->items.size(), 1u);
  auto* item = mod->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kInitialBlock);
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->label, "my_block");
}

// 4. Nested named begin-end blocks
TEST(ParserClause03, Cl3_13_NestedNamedBlocks) {
  auto r = Parse(
      "module m;\n"
      "  initial begin : outer\n"
      "    begin : inner\n"
      "      int y;\n"
      "      y = 42;\n"
      "    end : inner\n"
      "  end : outer\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->label, "outer");
  ASSERT_GE(item->body->stmts.size(), 1u);
  EXPECT_EQ(item->body->stmts[0]->label, "inner");
}

// 5. Fork-join block creating a subscope
TEST(ParserClause03, Cl3_13_ForkJoinBlockSubscope) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    fork\n"
              "      $display(\"a\");\n"
              "      $display(\"b\");\n"
              "    join\n"
              "  end\n"
              "endmodule\n"));
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

// 7. Variable name same as module name (different name spaces)
TEST(ParserClause03, Cl3_13_VarNameSameAsModuleName) {
  // A variable named 'top' inside module 'top' is legal because
  // the definition name space and the local scope are distinct.
  EXPECT_TRUE(
      ParseOk("module top;\n"
              "  logic top;\n"
              "endmodule\n"));
}

// 8. Package with internal declarations (local scope)
TEST(ParserClause03, Cl3_13_PackageWithInternalDeclarations) {
  auto r = Parse(
      "package my_pkg;\n"
      "  typedef logic [7:0] byte_t;\n"
      "  parameter int WIDTH = 8;\n"
      "  function automatic int double_it(int x);\n"
      "    return x * 2;\n"
      "  endfunction\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  auto* pkg = r.cu->packages[0];
  EXPECT_EQ(pkg->name, "my_pkg");
  EXPECT_GE(pkg->items.size(), 3u);
}

// 9. Package import with :: operator
TEST(ParserClause03, Cl3_13_PackageImportExplicit) {
  auto r = Parse(
      "package pkg;\n"
      "  typedef int myint;\n"
      "endpackage\n"
      "module m;\n"
      "  import pkg::myint;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ASSERT_GE(mod->items.size(), 1u);
  auto* item = mod->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kImportDecl);
  EXPECT_EQ(item->import_item.package_name, "pkg");
  EXPECT_EQ(item->import_item.item_name, "myint");
  EXPECT_FALSE(item->import_item.is_wildcard);
}

// 10. Package wildcard import (import pkg::*)
TEST(ParserClause03, Cl3_13_PackageWildcardImport) {
  auto r = Parse(
      "package pkg;\n"
      "  typedef int myint;\n"
      "endpackage\n"
      "module m;\n"
      "  import pkg::*;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ASSERT_GE(mod->items.size(), 1u);
  auto* item = mod->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kImportDecl);
  EXPECT_EQ(item->import_item.package_name, "pkg");
  EXPECT_TRUE(item->import_item.is_wildcard);
}

// 11. Multiple packages imported into same module
TEST(ParserClause03, Cl3_13_MultiplePackageImports) {
  auto r = Parse(
      "package alpha;\n"
      "  typedef int alpha_t;\n"
      "endpackage\n"
      "package beta;\n"
      "  typedef int beta_t;\n"
      "endpackage\n"
      "module m;\n"
      "  import alpha::*;\n"
      "  import beta::beta_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 2u);
  auto* mod = r.cu->modules[0];
  int import_count = 0;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kImportDecl) import_count++;
  }
  EXPECT_EQ(import_count, 2);
}

// 12. Class scope -- members in class name space
TEST(ParserClause03, Cl3_13_ClassScopeMembers) {
  auto r = Parse(
      "class my_cls;\n"
      "  int data;\n"
      "  string name;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  EXPECT_EQ(cls->name, "my_cls");
  ASSERT_GE(cls->members.size(), 2u);
  EXPECT_EQ(cls->members[0]->kind, ClassMemberKind::kProperty);
  EXPECT_EQ(cls->members[0]->name, "data");
  EXPECT_EQ(cls->members[1]->kind, ClassMemberKind::kProperty);
  EXPECT_EQ(cls->members[1]->name, "name");
}

// 13. Class with methods sharing scope with member variables
TEST(ParserClause03, Cl3_13_ClassMethodsAndProperties) {
  auto r = Parse(
      "class my_cls;\n"
      "  int count;\n"
      "  function void increment();\n"
      "    count = count + 1;\n"
      "  endfunction\n"
      "  task reset();\n"
      "    count = 0;\n"
      "  endtask\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* cls = r.cu->classes[0];
  ASSERT_GE(cls->members.size(), 3u);
  EXPECT_EQ(cls->members[0]->kind, ClassMemberKind::kProperty);
  EXPECT_EQ(cls->members[0]->name, "count");
  EXPECT_EQ(cls->members[1]->kind, ClassMemberKind::kMethod);
  ASSERT_NE(cls->members[1]->method, nullptr);
  EXPECT_EQ(cls->members[1]->method->name, "increment");
  EXPECT_EQ(cls->members[2]->kind, ClassMemberKind::kMethod);
  ASSERT_NE(cls->members[2]->method, nullptr);
  EXPECT_EQ(cls->members[2]->method->name, "reset");
}

// 14. Generate block scope (for-generate)
TEST(ParserClause03, Cl3_13_GenerateForBlockScope) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 4; i = i + 1) begin : gen_blk\n"
      "    logic [7:0] data;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  bool found_gen = false;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kGenerateFor) {
      found_gen = true;
      EXPECT_FALSE(item->gen_body.empty());
    }
  }
  EXPECT_TRUE(found_gen);
}

// 15. Labeled generate blocks (if-generate)
TEST(ParserClause03, Cl3_13_LabeledIfGenerateBlock) {
  auto r = Parse(
      "module m;\n"
      "  parameter USE_FAST = 1;\n"
      "  if (USE_FAST) begin : fast_path\n"
      "    logic [7:0] result;\n"
      "  end else begin : slow_path\n"
      "    logic [15:0] result;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  bool found_gen_if = false;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kGenerateIf) {
      found_gen_if = true;
      EXPECT_FALSE(item->gen_body.empty());
    }
  }
  EXPECT_TRUE(found_gen_if);
}

// 16. Interface with modport declarations
TEST(ParserClause03, Cl3_13_InterfaceWithModports) {
  auto r = Parse(
      "interface bus_if;\n"
      "  logic [7:0] data;\n"
      "  logic valid, ready;\n"
      "  modport master (output data, output valid, input ready);\n"
      "  modport slave (input data, input valid, output ready);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  auto* ifc = r.cu->interfaces[0];
  EXPECT_EQ(ifc->name, "bus_if");
  ASSERT_EQ(ifc->modports.size(), 2u);
  EXPECT_EQ(ifc->modports[0]->name, "master");
  EXPECT_EQ(ifc->modports[1]->name, "slave");
}

// 17. Program block with declarations
TEST(ParserClause03, Cl3_13_ProgramBlockWithDeclarations) {
  auto r = Parse(
      "program test_prog;\n"
      "  int count;\n"
      "  initial begin\n"
      "    count = 0;\n"
      "  end\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->name, "test_prog");
  EXPECT_EQ(r.cu->programs[0]->decl_kind, ModuleDeclKind::kProgram);
  EXPECT_FALSE(r.cu->programs[0]->items.empty());
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

// 19. Hierarchical reference syntax (a.b.c)
TEST(ParserClause03, Cl3_13_HierarchicalReferenceSyntax) {
  // Hierarchical names like top.sub.sig are member-access expressions.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    $display(\"%0d\", top.sub.sig);\n"
              "  end\n"
              "endmodule\n"));
}

// 20. Package scope resolution (pkg::item)
TEST(ParserClause03, Cl3_13_PackageScopeResolution) {
  EXPECT_TRUE(
      ParseOk("package pkg;\n"
              "  parameter int WIDTH = 8;\n"
              "endpackage\n"
              "module m;\n"
              "  logic [pkg::WIDTH-1:0] data;\n"
              "endmodule\n"));
}

// 21. Class scope resolution (cls::member)
TEST(ParserClause03, Cl3_13_ClassScopeResolution) {
  EXPECT_TRUE(
      ParseOk("class base;\n"
              "  typedef int my_type;\n"
              "endclass\n"
              "module m;\n"
              "  base::my_type x;\n"
              "endmodule\n"));
}

// 22. Typedef in package scope
TEST(ParserClause03, Cl3_13_TypedefInPackageScope) {
  auto r = Parse(
      "package types_pkg;\n"
      "  typedef logic [7:0] byte_t;\n"
      "  typedef logic [15:0] word_t;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  auto* pkg = r.cu->packages[0];
  int typedef_count = 0;
  for (auto* item : pkg->items) {
    if (item->kind == ModuleItemKind::kTypedef) typedef_count++;
  }
  EXPECT_EQ(typedef_count, 2);
}

// 23. Enum in module scope
TEST(ParserClause03, Cl3_13_EnumInModuleScope) {
  auto r = Parse(
      "module m;\n"
      "  typedef enum logic [1:0] {IDLE, RUN, DONE} state_t;\n"
      "  state_t current_state;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  bool found_typedef = false;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kTypedef) {
      found_typedef = true;
      EXPECT_EQ(item->typedef_type.enum_members.size(), 3u);
    }
  }
  EXPECT_TRUE(found_typedef);
}

// 24. Named fork-join blocks
TEST(ParserClause03, Cl3_13_NamedForkJoinBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    fork : my_fork\n"
      "      $display(\"a\");\n"
      "      $display(\"b\");\n"
      "    join : my_fork\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->body, nullptr);
  ASSERT_GE(item->body->stmts.size(), 1u);
  auto* fork_stmt = item->body->stmts[0];
  EXPECT_EQ(fork_stmt->kind, StmtKind::kFork);
  EXPECT_EQ(fork_stmt->label, "my_fork");
}

// 25. begin-end with no name (anonymous block)
TEST(ParserClause03, Cl3_13_AnonymousBeginEndBlock) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    int x;\n"
      "    x = 5;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->body, nullptr);
  EXPECT_EQ(item->body->kind, StmtKind::kBlock);
  // Anonymous blocks have an empty label.
  EXPECT_TRUE(item->body->label.empty());
}

// 26. Multiple named blocks at same level
TEST(ParserClause03, Cl3_13_MultipleNamedBlocksSameLevel) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    begin : block_a\n"
      "      int x;\n"
      "      x = 1;\n"
      "    end : block_a\n"
      "    begin : block_b\n"
      "      int y;\n"
      "      y = 2;\n"
      "    end : block_b\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = r.cu->modules[0]->items[0]->body;
  ASSERT_NE(body, nullptr);
  ASSERT_GE(body->stmts.size(), 2u);
  EXPECT_EQ(body->stmts[0]->label, "block_a");
  EXPECT_EQ(body->stmts[1]->label, "block_b");
}

// 27. Parameter and localparam in module scope
TEST(ParserClause03, Cl3_13_ParameterAndLocalparamInModule) {
  auto r = Parse(
      "module m;\n"
      "  parameter int WIDTH = 8;\n"
      "  localparam int DEPTH = 16;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  bool found_param = false;
  bool found_localparam = false;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::kParamDecl && item->name == "WIDTH")
      found_param = true;
    if (item->kind == ModuleItemKind::kParamDecl && item->name == "DEPTH")
      found_localparam = true;
  }
  EXPECT_TRUE(found_param);
  EXPECT_TRUE(found_localparam);
}

// 28. Port names as part of module scope
TEST(ParserClause03, Cl3_13_PortNamesInModuleScope) {
  auto r = Parse(
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

// 29. Function with local variables creating subscope
TEST(ParserClause03, Cl3_13_FunctionWithLocalVarsSubscope) {
  auto r = Parse(
      "module m;\n"
      "  function automatic int compute(int a, int b);\n"
      "    int temp;\n"
      "    temp = a + b;\n"
      "    return temp;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ASSERT_GE(mod->items.size(), 1u);
  auto* func = mod->items[0];
  EXPECT_EQ(func->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(func->name, "compute");
  // The function should have body statements (local var + assign + return).
  EXPECT_FALSE(func->func_body_stmts.empty());
}

// 30. Nested class (class within a module -- class in module scope)
TEST(ParserClause03, Cl3_13_NestedClassInModule) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  class inner_cls;\n"
              "    int value;\n"
              "    function void set(int v);\n"
              "      value = v;\n"
              "    endfunction\n"
              "  endclass\n"
              "endmodule\n"));
}

// 31. Text macro name space (d) — `define introduces names with leading `
TEST(ParserClause03, Cl3_13_TextMacroNameSpace) {
  // Macro defined and used; subsequent redefinition overrides previous
  auto r = Parse(
      "`define WIDTH 8\n"
      "`define DEPTH 16\n"
      "module m;\n"
      "  logic [`WIDTH-1:0] data;\n"
      "  logic [`DEPTH-1:0] addr;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  // Macro names are unambiguous with other name spaces (leading ` character)
  EXPECT_TRUE(
      ParseOk("`define data 42\n"
              "module m; logic [7:0] data; endmodule\n"));
}

// 32. Attribute name space (h) — enclosed by (* and *)
TEST(ParserClause03, Cl3_13_AttributeNameSpace) {
  auto r = Parse(
      "module m;\n"
      "  (* synthesis *) logic flag;\n"
      "  (* full_case, parallel_case *) logic [1:0] sel;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  // Verify attributes are parsed and attached to declarations
  EXPECT_TRUE(HasAttrNamed(r.cu->modules[0]->items, "synthesis"));
  EXPECT_TRUE(HasAttrNamed(r.cu->modules[0]->items, "full_case"));
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
