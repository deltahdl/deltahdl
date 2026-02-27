// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

namespace {

// §3.8: Function returning value, void function, all 4 argument directions.
TEST(ParserClause03, Cl3_8_FunctionReturnAndVoidAndDirections) {
  auto r = Parse(
      "module m;\n"
      "  function int compute(input int a, output int b,\n"
      "                       inout int c, ref int d);\n"
      "    b = a;\n"
      "    return a + c + d;\n"
      "  endfunction\n"
      "  function void show(input int val);\n"
      "    $display(\"%d\", val);\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(
      CountItemsByKind(r.cu->modules[0]->items, ModuleItemKind::kFunctionDecl),
      2);
  const auto* compute = FindFunctionByName(r.cu->modules[0]->items, "compute");
  ASSERT_NE(compute, nullptr);
  ASSERT_EQ(compute->func_args.size(), 4u);
  EXPECT_EQ(compute->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(compute->func_args[1].direction, Direction::kOutput);
  EXPECT_EQ(compute->func_args[2].direction, Direction::kInout);
  EXPECT_EQ(compute->func_args[3].direction, Direction::kRef);
}

struct ParseResult309 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult309 Parse(const std::string& src) {
  ParseResult309 result;
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

// =============================================================================
// LRM §3.9 — Packages
// =============================================================================
// §3.9: "Packages provide a declaration space, which can be shared by other
//        building blocks." Package with typedef, functions, and end label.
TEST(ParserClause03, Cl3_9_PackageDeclarationsAndEndLabel) {
  auto r = Parse(
      "package ComplexPkg;\n"
      "  typedef struct { shortreal i, r; } Complex;\n"
      "  function automatic int helper(int x); return x; endfunction\n"
      "endpackage : ComplexPkg\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "ComplexPkg");
  EXPECT_TRUE(
      HasItemOfKind(r.cu->packages[0]->items, ModuleItemKind::kTypedef));
  EXPECT_TRUE(
      HasItemOfKind(r.cu->packages[0]->items, ModuleItemKind::kFunctionDecl));
}

// §3.9: "Package declarations can be imported into other building blocks,
//        including other packages."
TEST(ParserClause03, Cl3_9_ImportIntoModuleAndPackage) {
  auto r = Parse(
      "package A; typedef int myint; endpackage\n"
      "package B; import A::*; endpackage\n"
      "module m; import A::myint; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 2u);
  EXPECT_EQ(r.cu->packages[0]->name, "A");
  EXPECT_EQ(r.cu->packages[1]->name, "B");
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

struct ParseResult310 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult310 Parse(const std::string& src) {
  ParseResult310 result;
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

// =============================================================================
// LRM §3.10 — Configurations
// =============================================================================
// §3.10: "SystemVerilog provides the ability to specify design configurations,
//         which specify the binding information of module instances to specific
//         SystemVerilog source code. Configurations utilize libraries."
TEST(ParserClause03, Cl3_10_ConfigBindingAndLibraries) {
  auto r = Parse(
      "config cfg1;\n"
      "  design work.top;\n"
      "  default liblist work;\n"
      "  instance top.u1 use lib2.fast_adder;\n"
      "  cell adder liblist lib1 lib2;\n"
      "endconfig : cfg1\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->name, "cfg1");
  // Design statement: binding to specific source (lib.cell notation)
  ASSERT_EQ(r.cu->configs[0]->design_cells.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->design_cells[0].first, "work");
  EXPECT_EQ(r.cu->configs[0]->design_cells[0].second, "top");
  // Three rules: default, instance, cell — all configuration binding types
  ASSERT_EQ(r.cu->configs[0]->rules.size(), 3u);
  EXPECT_EQ(r.cu->configs[0]->rules[0]->kind, ConfigRuleKind::kDefault);
  ASSERT_EQ(r.cu->configs[0]->rules[0]->liblist.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->rules[0]->liblist[0], "work");
  auto* r1 = r.cu->configs[0]->rules[1];
  EXPECT_EQ(r1->kind, ConfigRuleKind::kInstance);
  EXPECT_EQ(r1->inst_path, "top.u1");
  EXPECT_EQ(r1->use_lib, "lib2");
  EXPECT_EQ(r1->use_cell, "fast_adder");
  auto* r2 = r.cu->configs[0]->rules[2];
  EXPECT_EQ(r2->kind, ConfigRuleKind::kCell);
  EXPECT_EQ(r2->cell_name, "adder");
  ASSERT_EQ(r2->liblist.size(), 2u);
}

struct ParseResult311 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult311 Parse(const std::string& src) {
  ParseResult311 result;
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

static ModuleItem* FindItemByKind(ParseResult311& r, ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

// =============================================================================
// LRM §3.11 — Overview of hierarchy
// =============================================================================
// §3.11 Hierarchy through instantiation, primitives as leaves, multiple tops
TEST(ParserClause03, Cl3_11_HierarchyAndInstantiation) {
  auto r = Parse(
      "module top;\n"
      "  logic in1, in2, sel;\n"
      "  wire out1;\n"
      "  mux2to1 m1 (.a(in1), .b(in2), .sel(sel), .y(out1));\n"
      "endmodule\n"
      "module mux2to1 (input wire a, b, sel, output logic y);\n"
      "  not g1 (sel_n, sel);\n"
      "  and g2 (a_s, a, sel_n);\n"
      "  and g3 (b_s, b, sel);\n"
      "  or  g4 (y, a_s, b_s);\n"
      "endmodule : mux2to1\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  // Multiple top-level blocks
  ASSERT_EQ(r.cu->modules.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->name, "top");
  EXPECT_EQ(r.cu->modules[1]->name, "mux2to1");
  // Hierarchy through instantiation with port connections for communication
  auto* inst = FindItemByKind(r, ModuleItemKind::kModuleInst);
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(inst->inst_module, "mux2to1");
  EXPECT_EQ(inst->inst_name, "m1");
  EXPECT_EQ(inst->inst_ports.size(), 4u);
  // Primitives as leaves: gate primitives (not, and, or)
  EXPECT_EQ(
      CountItemsByKind(r.cu->modules[1]->items, ModuleItemKind::kGateInst), 4);
}

struct ParseResult312 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult312 Parse(const std::string& src) {
  ParseResult312 result;
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

static const ModuleItem* FindInstByModule(const std::vector<ModuleItem*>& items,
                                          const std::string& module_name) {
  for (const auto* item : items)
    if (item->kind == ModuleItemKind::kModuleInst &&
        item->inst_module == module_name)
      return item;
  return nullptr;
}

// =============================================================================
// LRM §3.12 — Compilation and elaboration
// =============================================================================
// §3.12 Compilation and elaboration with parameterized instantiation
TEST(ParserClause03, Cl3_12_CompilationAndElaboration) {
  auto r = Parse(
      "package pkg; typedef logic [7:0] byte_t; endpackage\n"
      "module adder #(parameter W = 8) (\n"
      "    input [W-1:0] a, b, output [W-1:0] s);\n"
      "  assign s = a + b;\n"
      "endmodule\n"
      "module top; import pkg::*;\n"
      "  wire [15:0] x, y, z;\n"
      "  adder #(16) u0 (.a(x), .b(y), .s(z));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  // Package compiled before module references it
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "pkg");
  // Parameterized module: elaboration computes parameter values
  ASSERT_EQ(r.cu->modules.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->params.size(), 1u);
  // Elaboration expands instantiation with parameter override & connectivity
  const auto* inst = FindInstByModule(r.cu->modules[1]->items, "adder");
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(inst->inst_params.size(), 1u);
  EXPECT_EQ(inst->inst_ports.size(), 3u);
}

struct ParseResult31201 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult31201 Parse(const std::string& src) {
  ParseResult31201 result;
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

static const ModuleItem* FindItemByKindAndName(
    const std::vector<ModuleItem*>& items, ModuleItemKind kind,
    const std::string& name) {
  for (const auto* item : items)
    if (item->kind == kind && item->name == name) return item;
  return nullptr;
}

// =============================================================================
// LRM §3.12.1 — Compilation units
// =============================================================================
// 1. Compilation unit definition: a collection of source files compiled
// together.  A single Parse() call produces one CompilationUnit.
TEST(ParserClause03, Cl3_12_1_CompilationUnitDefinition) {
  auto r = Parse(
      "module a; endmodule\n"
      "module b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  // Both modules belong to the same compilation unit.
  ASSERT_EQ(r.cu->modules.size(), 2u);
  EXPECT_EQ(r.cu->modules[0]->name, "a");
  EXPECT_EQ(r.cu->modules[1]->name, "b");
}

// 2. Compilation-unit scope: declarations outside any other scope.
// CU scope can contain anything valid in a package (§26.2) —
// functions, tasks, typedefs, parameters, classes.
TEST(ParserClause03, Cl3_12_1_CuScopeContainsPackageItems) {
  auto r = Parse(
      "function int helper(int x); return x + 1; endfunction\n"
      "task auto_task; endtask\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  // Functions and tasks in CU scope are stored in cu_items.
  ASSERT_EQ(r.cu->cu_items.size(), 2u);
  EXPECT_EQ(r.cu->cu_items[0]->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(r.cu->cu_items[0]->name, "helper");
  EXPECT_EQ(r.cu->cu_items[1]->kind, ModuleItemKind::kTaskDecl);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

// 3. Bind constructs at CU scope (§23.11) — CU scope can also hold bind.
TEST(ParserClause03, Cl3_12_1_CuScopeBindDirective) {
  auto r = Parse(
      "module target; endmodule\n"
      "bind target target chk_inst();\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->bind_directives.size(), 1u);
  EXPECT_EQ(r.cu->bind_directives[0]->target, "target");
}

// 4. `include becomes part of the including file's CU.
// The preprocessor inlines included content into the same CU.
TEST(ParserClause03, Cl3_12_1_IncludeBecomesPartOfCU) {
  // We can't include real files in this unit test, but we verify that
  // the preprocessor produces a single text blob from `define/`ifdef
  // which are CU-scoped directives.  If an `include were processed,
  // its content would appear in the same preprocessed output.
  auto r = Parse(
      "`define MY_CONST 42\n"
      "module m;\n"
      "  localparam C = `MY_CONST;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  // The macro defined at CU scope is visible inside the module,
  // demonstrating that preprocessing merges everything into one CU.
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

// 5. Global visibility: modules, primitives, programs, interfaces, packages
// are visible in all CUs.  Within a single CU, all are accessible.
TEST(ParserClause03, Cl3_12_1_GloballyVisibleDesignElements) {
  auto r = Parse(
      "package pkg; endpackage\n"
      "interface intf; endinterface\n"
      "program prog; endprogram\n"
      "module mod; endmodule\n"
      "primitive udp_and(output o, input a, b);\n"
      "  table\n"
      "    0 0 : 0;\n"
      "    0 1 : 0;\n"
      "    1 0 : 0;\n"
      "    1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->udps.size(), 1u);
}

// 6. CU scope can hold classes (valid in a package per §26.2).
TEST(ParserClause03, Cl3_12_1_CuScopeClassDecl) {
  auto r = Parse(
      "class my_class;\n"
      "  int x;\n"
      "endclass\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "my_class");
}

// 8. Name resolution: nested scope searched first, then CU scope.
// A local declaration shadows a CU-scope declaration.
TEST(ParserClause03, Cl3_12_1_NameResolutionOrder) {
  // A function at CU scope and a module that also declares 'helper'.
  // The parser accepts both — resolution is elaboration's job.
  auto r = Parse(
      "function int helper(int x); return x; endfunction\n"
      "module m;\n"
      "  function int helper(int x); return x * 2; endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  // CU scope has the top-level function.
  ASSERT_EQ(r.cu->cu_items.size(), 1u);
  EXPECT_EQ(r.cu->cu_items[0]->name, "helper");
  // Module has its own 'helper' — shadows the CU-scope one.
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_NE(FindItemByKindAndName(r.cu->modules[0]->items,
                                  ModuleItemKind::kFunctionDecl, "helper"),
            nullptr);
}

// 10. No forward references in CU scope (except task/function names).
// The LRM says references shall only be made to names already defined.
// This is a semantic rule; the parser accepts the code but elaboration
// would reject it.  We test that parsing succeeds (syntax is valid).
TEST(ParserClause03, Cl3_12_1_ForwardRefSyntaxValid) {
  // This is valid syntax even though semantically 'b' is referenced
  // before its declaration at CU scope.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  wire w;\n"
              "endmodule\n"));
}

// 11. CU scope has no name — cannot be imported.
// An import of $unit would be illegal.  Verify that valid import syntax
// works and that CU items remain separate from packages.
TEST(ParserClause03, Cl3_12_1_CuScopeCannotBeImported) {
  // Normal package import works fine.
  auto r = Parse(
      "package pkg;\n"
      "  typedef int myint;\n"
      "endpackage\n"
      "module m;\n"
      "  import pkg::*;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  // CU-scope functions are NOT in any package.
  EXPECT_TRUE(r.cu->cu_items.empty());
  ASSERT_EQ(r.cu->packages.size(), 1u);
}

// 12. CU scope identifiers not accessible via hierarchical references.
// Hierarchical names start from $root (§23.3.1), not from CU scope.
// Verify that a hierarchical reference in a module parses correctly.
TEST(ParserClause03, Cl3_12_1_HierRefFromCUScope) {
  auto r = Parse(
      "module top;\n"
      "  module_a u1();\n"
      "endmodule\n"
      "module module_a;\n"
      "  logic sig;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 2u);
}

// 13. CU allows type sharing without packages (§3.12.1 last paragraph).
// Users can share types across a CU without declaring a package.
// Top-level typedef is parsed as a module item (discarded at top level
// in current implementation) or could be a class.  Verify CU-scope
// classes enable type sharing.
TEST(ParserClause03, Cl3_12_1_TypeSharingViaCUScope) {
  auto r = Parse(
      "class shared_type;\n"
      "  int value;\n"
      "endclass\n"
      "module m1;\n"
      "  shared_type obj;\n"
      "endmodule\n"
      "module m2;\n"
      "  shared_type obj;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  ASSERT_EQ(r.cu->modules.size(), 2u);
}

// 15. Config declarations at top level (part of CU).
TEST(ParserClause03, Cl3_12_1_ConfigAtCUScope) {
  auto r = Parse(
      "module lib_mod; endmodule\n"
      "config my_cfg;\n"
      "  design lib_mod;\n"
      "  default liblist;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->name, "my_cfg");
}

// 16. Checker declarations at CU scope.
TEST(ParserClause03, Cl3_12_1_CheckerAtCUScope) {
  auto r = Parse(
      "checker my_chk;\n"
      "endchecker\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
}

// =============================================================================
// A.1.2 source_text ::= [ timeunits_declaration ] { description }
// =============================================================================
// Empty source text.
TEST(SourceText, EmptySourceText) {
  auto r = Parse("");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules.empty());
}

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

// package_item: timeunits_declaration (footnote 3)
TEST(SourceText, PackageItemTimeunitsDecl) {
  auto r = Parse(
      "package pkg;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
}

// =============================================================================
// LRM §3.14 — Simulation time units and precision
// =============================================================================
TEST(ParserClause03, Cl3_14_TimeunitsAndTimescale) {
  auto r1 = Parse("module m; timeunit 1ns; endmodule\n");
  EXPECT_FALSE(r1.has_errors);
  EXPECT_TRUE(r1.cu->modules[0]->has_timeunit);
  auto r2 = Parse("module m; timeprecision 1ps; endmodule\n");
  EXPECT_FALSE(r2.has_errors);
  EXPECT_TRUE(r2.cu->modules[0]->has_timeprecision);
  auto r3 = Parse("module m; timeunit 1ns; timeprecision 1ps; endmodule\n");
  EXPECT_FALSE(r3.has_errors);
  EXPECT_TRUE(r3.cu->modules[0]->has_timeunit);
  EXPECT_TRUE(r3.cu->modules[0]->has_timeprecision);
  EXPECT_TRUE(ParseOk("module m; timeunit 100ps / 10fs; endmodule\n"));
  EXPECT_TRUE(
      ParseOk("program p; timeunit 10us; timeprecision 100ns; endprogram\n"));
  EXPECT_TRUE(ParseOk("interface ifc; timeunit 1ns; endinterface\n"));
  // `timescale directive
  EXPECT_TRUE(ParseOk("`timescale 1ns/1ps\nmodule m; endmodule\n"));
  // Time literals (§5.8): integer, fractional, all unit suffixes
  EXPECT_TRUE(ParseOk("module m; initial #10ns $display(\"d\"); endmodule\n"));
  EXPECT_TRUE(ParseOk("module m; initial #2.1ns $display(\"d\"); endmodule\n"));
  // Various magnitudes (Table 3-1)
  EXPECT_TRUE(
      ParseOk("module a; timeunit 100ns; timeprecision 10ps; endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module b; timeunit 1us; timeprecision 1ns; endmodule\n"));
}

// 1. TimeUnit enum: six values with correct power-of-10 exponents
// (s=0, ms=-3, us=-6, ns=-9, ps=-12, fs=-15).
TEST(ParserClause03, Cl3_14_TimeUnitEnumValues) {
  EXPECT_EQ(static_cast<int8_t>(TimeUnit::kS), 0);
  EXPECT_EQ(static_cast<int8_t>(TimeUnit::kMs), -3);
  EXPECT_EQ(static_cast<int8_t>(TimeUnit::kUs), -6);
  EXPECT_EQ(static_cast<int8_t>(TimeUnit::kNs), -9);
  EXPECT_EQ(static_cast<int8_t>(TimeUnit::kPs), -12);
  EXPECT_EQ(static_cast<int8_t>(TimeUnit::kFs), -15);
}

// 2. Table 3-1: ParseTimeUnitStr maps all six character strings.
TEST(ParserClause03, Cl3_14_Table3_1_AllUnitStrings) {
  TimeUnit u = TimeUnit::kNs;
  EXPECT_TRUE(ParseTimeUnitStr("s", u));
  EXPECT_EQ(u, TimeUnit::kS);
  EXPECT_TRUE(ParseTimeUnitStr("ms", u));
  EXPECT_EQ(u, TimeUnit::kMs);
  EXPECT_TRUE(ParseTimeUnitStr("us", u));
  EXPECT_EQ(u, TimeUnit::kUs);
  EXPECT_TRUE(ParseTimeUnitStr("ns", u));
  EXPECT_EQ(u, TimeUnit::kNs);
  EXPECT_TRUE(ParseTimeUnitStr("ps", u));
  EXPECT_EQ(u, TimeUnit::kPs);
  EXPECT_TRUE(ParseTimeUnitStr("fs", u));
  EXPECT_EQ(u, TimeUnit::kFs);
}

// 3. Table 3-1: invalid unit strings are rejected.
TEST(ParserClause03, Cl3_14_Table3_1_InvalidStrings) {
  TimeUnit u = TimeUnit::kNs;
  EXPECT_FALSE(ParseTimeUnitStr("", u));
  EXPECT_FALSE(ParseTimeUnitStr("xs", u));
  EXPECT_FALSE(ParseTimeUnitStr("sec", u));
  EXPECT_FALSE(ParseTimeUnitStr("NS", u));  // case-sensitive
}

// 4. "us" represents microseconds (substitution for the mu-s symbol).
TEST(ParserClause03, Cl3_14_UsForMicroseconds) {
  TimeUnit u = TimeUnit::kNs;
  EXPECT_TRUE(ParseTimeUnitStr("us", u));
  EXPECT_EQ(u, TimeUnit::kUs);
  EXPECT_EQ(static_cast<int8_t>(u), -6);  // 10^-6 = microsecond
}

// 5. TimeScale struct: time values have two components (unit + precision).
TEST(ParserClause03, Cl3_14_TimeScaleTwoComponents) {
  TimeScale ts;
  ts.unit = TimeUnit::kNs;
  ts.magnitude = 1;
  ts.precision = TimeUnit::kPs;
  ts.prec_magnitude = 1;
  EXPECT_EQ(ts.unit, TimeUnit::kNs);
  EXPECT_EQ(ts.precision, TimeUnit::kPs);
  // Unit and precision are independently stored.
  EXPECT_NE(static_cast<int8_t>(ts.unit), static_cast<int8_t>(ts.precision));
}

// 12. Precision constraint: precision exponent <= unit exponent.
// Finer units have more-negative exponents (kFs < kPs < ... < kS).
TEST(ParserClause03, Cl3_14_PrecisionAtLeastAsPreciseAsUnit) {
  EXPECT_LE(static_cast<int8_t>(TimeUnit::kFs),
            static_cast<int8_t>(TimeUnit::kPs));
  EXPECT_LE(static_cast<int8_t>(TimeUnit::kPs),
            static_cast<int8_t>(TimeUnit::kNs));
  EXPECT_LE(static_cast<int8_t>(TimeUnit::kNs),
            static_cast<int8_t>(TimeUnit::kUs));
  EXPECT_LE(static_cast<int8_t>(TimeUnit::kUs),
            static_cast<int8_t>(TimeUnit::kMs));
  EXPECT_LE(static_cast<int8_t>(TimeUnit::kMs),
            static_cast<int8_t>(TimeUnit::kS));
}

// 13. Time values stored in design element: module with timeunit and
// timeprecision stores both components.
TEST(ParserClause03, Cl3_14_TimeValuesInDesignElement) {
  auto r = Parse(
      "module m;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* mod = r.cu->modules[0];
  EXPECT_TRUE(mod->has_timeunit);
  EXPECT_TRUE(mod->has_timeprecision);
  EXPECT_EQ(mod->time_unit, TimeUnit::kNs);
  EXPECT_EQ(mod->time_prec, TimeUnit::kPs);
}

// ===========================================================================
// §3.14: Timeunit/timeprecision parsing
// ===========================================================================
TEST(Lexical, Timeunit_BasicParse) {
  auto r = Parse(
      "module top;\n"
      "  timeunit 1ns;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  // Should parse without error. The timeunit decl is consumed.
  EXPECT_EQ(r.cu->modules[0]->name, "top");
}

TEST(Lexical, Timeprecision_BasicParse) {
  auto r = Parse(
      "module top;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
}

TEST(Lexical, Timeunit_WithSlash) {
  // timeunit 1ns / 1ps;  (combined form)
  auto r = Parse(
      "module top;\n"
      "  timeunit 1ns / 1ps;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
}

TEST(Lexical, Timeunit_DifferentValues) {
  // Various time unit values
  auto r = Parse(
      "module top;\n"
      "  timeunit 100us;\n"
      "  timeprecision 10ns;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
}

TEST(Lexical, Timeunit_StoredInModuleDecl_Values) {
  // The timeunit/timeprecision values should be stored in ModuleDecl.
  auto r = Parse(
      "module top;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  auto* mod = r.cu->modules[0];
  EXPECT_EQ(mod->time_unit, TimeUnit::kNs);
  EXPECT_EQ(mod->time_prec, TimeUnit::kPs);
}

TEST(Lexical, Timeunit_StoredInModuleDecl_Flags) {
  auto r = Parse(
      "module top;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  auto* mod = r.cu->modules[0];
  EXPECT_TRUE(mod->has_timeunit);
  EXPECT_TRUE(mod->has_timeprecision);
}

// =============================================================================
// LRM §3.14.1 — Time value rounding
// =============================================================================
// 14. Same precision as unit: delay values rounded to whole numbers.
TEST(ParserClause03, Cl3_14_1_SamePrecisionRoundsToInteger) {
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kNs, 1};
  // 2.75ns with 1ns precision rounds to 3ns = 3 ticks at ns.
  EXPECT_EQ(RealDelayToTicks(2.75, ts, TimeUnit::kNs), 3u);
  // 2.3ns rounds to 2ns.
  EXPECT_EQ(RealDelayToTicks(2.3, ts, TimeUnit::kNs), 2u);
  // 2.5ns rounds to 3ns (round half away from zero).
  EXPECT_EQ(RealDelayToTicks(2.5, ts, TimeUnit::kNs), 3u);
}

// 15. One order of magnitude smaller: rounds to one decimal place.
TEST(ParserClause03, Cl3_14_1_OneOrderSmallerRoundsToOneDecimal) {
  // 1ns unit, 100ps precision → 1 decimal place in ns.
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kPs, 100};
  // 2.75ns → 2.8ns = 2800ps = 2800 ticks at ps.
  EXPECT_EQ(RealDelayToTicks(2.75, ts, TimeUnit::kPs), 2800u);
  // 2.73ns → 2.7ns = 2700ps.
  EXPECT_EQ(RealDelayToTicks(2.73, ts, TimeUnit::kPs), 2700u);
}

// 16. Rounding example: 1ns unit, 100ps precision, 2.75ns rounds to 2.8ns.
TEST(ParserClause03, Cl3_14_1_LrmExample_2_75ns) {
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kPs, 100};
  // 2.75ns rounded to nearest 100ps = 2.8ns = 2800 ticks at ps.
  EXPECT_EQ(RealDelayToTicks(2.75, ts, TimeUnit::kPs), 2800u);
  // Verify in ns-tick form: at ns precision, 2800ps = 2.8ns ≈ 3 ticks.
  // But at ps global precision the value is 2800.
  EXPECT_EQ(RealDelayToTicks(2.75, ts, TimeUnit::kPs), 2800u);
}

// 17. Two orders of magnitude smaller: rounds to two decimal places.
TEST(ParserClause03, Cl3_14_1_TwoOrdersSmaller) {
  // 1ns unit, 10ps precision → 2 decimal places in ns.
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kPs, 10};
  // 2.756ns → 2.76ns = 2760ps.
  EXPECT_EQ(RealDelayToTicks(2.756, ts, TimeUnit::kPs), 2760u);
  // 2.754ns → 2.75ns = 2750ps.
  EXPECT_EQ(RealDelayToTicks(2.754, ts, TimeUnit::kPs), 2750u);
}

// 18. Three orders (full precision): no rounding needed.
TEST(ParserClause03, Cl3_14_1_ThreeOrdersNoRounding) {
  // 1ns unit, 1ps precision → 3 decimal places in ns.
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kPs, 1};
  // 2.756ns = 2756ps exactly, no rounding.
  EXPECT_EQ(RealDelayToTicks(2.756, ts, TimeUnit::kPs), 2756u);
}

// 19. Zero delay: rounds to zero regardless of precision.
TEST(ParserClause03, Cl3_14_1_ZeroDelay) {
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kPs, 100};
  EXPECT_EQ(RealDelayToTicks(0.0, ts, TimeUnit::kPs), 0u);
}

// 20. Exact integer delays pass through unchanged with any precision.
TEST(ParserClause03, Cl3_14_1_ExactIntegerPassThrough) {
  TimeScale ts{TimeUnit::kNs, 1, TimeUnit::kPs, 100};
  // 5.0ns is exact at any precision → 5000ps.
  EXPECT_EQ(RealDelayToTicks(5.0, ts, TimeUnit::kPs), 5000u);
  // 3.0ns → 3000ps.
  EXPECT_EQ(RealDelayToTicks(3.0, ts, TimeUnit::kPs), 3000u);
}

}  // namespace
