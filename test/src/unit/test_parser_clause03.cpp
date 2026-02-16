#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

struct ParseResult3 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult3 Parse(const std::string& src) {
  ParseResult3 result;
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

static ModuleItem* FindItemByKind(ParseResult3& r, ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

// =============================================================================
// LRM section 3.2 -- Design elements
// =============================================================================

TEST(ParserSection3, DesignElementModuleBasic) {
  auto r = Parse("module top; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "top");
  EXPECT_EQ(r.cu->modules[0]->decl_kind, ModuleDeclKind::kModule);
}

TEST(ParserSection3, DesignElementProgramBasic) {
  auto r = Parse("program p; endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->name, "p");
  EXPECT_EQ(r.cu->programs[0]->decl_kind, ModuleDeclKind::kProgram);
}

TEST(ParserSection3, DesignElementInterfaceBasic) {
  auto r = Parse("interface ifc; endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->name, "ifc");
  EXPECT_EQ(r.cu->interfaces[0]->decl_kind, ModuleDeclKind::kInterface);
}

TEST(ParserSection3, DesignElementPackage) {
  auto r = Parse("package pkg; endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "pkg");
}

TEST(ParserSection3, DesignElementClass) {
  auto r = Parse("class cls; endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "cls");
}

TEST(ParserSection3, DesignElementPrimitive) {
  auto r = Parse(
      "primitive mux_prim (output out, input sel, a, b);\n"
      "  table\n"
      "    0 0 ? : 0;\n"
      "    0 1 ? : 1;\n"
      "    1 ? 0 : 0;\n"
      "    1 ? 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->udps[0]->name, "mux_prim");
}

TEST(ParserSection3, DesignElementCheckerBasic) {
  auto r = Parse("checker chk; endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->name, "chk");
  EXPECT_EQ(r.cu->checkers[0]->decl_kind, ModuleDeclKind::kChecker);
}

TEST(ParserSection3, DesignElementConfig) {
  auto r = Parse(
      "config cfg1;\n"
      "  design top;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->name, "cfg1");
}

TEST(ParserSection3, AllSevenDesignElements) {
  // §3.2: A design element is a module, program, interface, checker,
  //       package, primitive, or configuration.
  auto r = Parse(
      "module m; endmodule\n"
      "program p; endprogram\n"
      "interface ifc; endinterface\n"
      "checker chk; endchecker\n"
      "package pkg; endpackage\n"
      "primitive udp_and (output out, input a, b);\n"
      "  table 0 0 : 0; 0 1 : 0; 1 0 : 0; 1 1 : 1; endtable\n"
      "endprimitive\n"
      "config cfg; design m; endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->configs.size(), 1u);
}

TEST(ParserSection3, MultipleModulesInCompilationUnit) {
  auto r = Parse(
      "module a; endmodule\n"
      "module b; endmodule\n"
      "module c; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 3u);
  EXPECT_EQ(r.cu->modules[0]->name, "a");
  EXPECT_EQ(r.cu->modules[1]->name, "b");
  EXPECT_EQ(r.cu->modules[2]->name, "c");
}

TEST(ParserSection3, ModuleWithPortsAndBody) {
  auto r = Parse(
      "module mux2to1 (input wire a, b, sel, output logic y);\n"
      "  assign y = sel ? b : a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->ports.size(), 4u);
}

TEST(ParserSection3, MacromoduleKeyword) {
  // macromodule is interchangeable with module (LRM 23.2)
  auto r = Parse("macromodule mm; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "mm");
}

// =============================================================================
// LRM section 3.3 -- Modules
// =============================================================================

// §3.3: "The basic building block in SystemVerilog is the module, enclosed
//        between the keywords module and endmodule."
TEST(ParserSection3, Sec3_3_ModuleEndLabel) {
  auto r = Parse(
      "module m;\n"
      "endmodule : m\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
}

// §3.3 LRM mux2to1 example (verbatim, with always_comb procedural block).
TEST(ParserSection3, Sec3_3_Mux2to1LrmExample) {
  auto r = Parse(
      "module mux2to1 (input wire a, b, sel,\n"
      "                output logic y);\n"
      "  always_comb begin\n"
      "    if (sel) y = a;\n"
      "    else     y = b;\n"
      "  end\n"
      "endmodule: mux2to1\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "mux2to1");
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 4u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "a");
  EXPECT_EQ(r.cu->modules[0]->ports[3].name, "y");
  auto* blk = FindItemByKind(r, ModuleItemKind::kAlwaysBlock);
  ASSERT_NE(blk, nullptr);
  EXPECT_EQ(blk->always_kind, AlwaysKind::kAlwaysComb);
}

// §3.3: "Data declarations, such as nets, variables, structures, and unions"
TEST(ParserSection3, Sec3_3_DataDeclarations) {
  auto r = Parse(
      "module m;\n"
      "  wire [7:0] w;\n"
      "  logic [15:0] v;\n"
      "  struct packed { logic [3:0] a; logic [3:0] b; } s;\n"
      "  union packed { logic [7:0] x; logic [7:0] y; } u;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_GE(r.cu->modules[0]->items.size(), 4u);
}

// §3.3: "Constant declarations"
TEST(ParserSection3, Sec3_3_ConstantDeclarations) {
  auto r = Parse(
      "module m;\n"
      "  parameter WIDTH = 8;\n"
      "  localparam DEPTH = 16;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool has_param = false;
  for (const auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kParamDecl) has_param = true;
  }
  EXPECT_TRUE(has_param);
}

// §3.3: "User-defined type definitions"
TEST(ParserSection3, Sec3_3_UserDefinedTypes) {
  auto r = Parse(
      "module m;\n"
      "  typedef logic [7:0] byte_t;\n"
      "  byte_t data;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool has_typedef = false;
  for (const auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kTypedef) has_typedef = true;
  }
  EXPECT_TRUE(has_typedef);
}

// §3.3: "Class definitions"
TEST(ParserSection3, Sec3_3_ClassDefinition) {
  auto r = Parse(
      "module m;\n"
      "  class my_class;\n"
      "    int val;\n"
      "  endclass\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool has_class = false;
  for (const auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kClassDecl) has_class = true;
  }
  EXPECT_TRUE(has_class);
}

// §3.3: "Subroutine definitions" (function + task)
TEST(ParserSection3, Sec3_3_SubroutineDefinitions) {
  auto r = Parse(
      "module m;\n"
      "  function int add(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "  task display_val(input int x);\n"
      "    $display(\"%d\", x);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool has_func = false, has_task = false;
  for (const auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kFunctionDecl) has_func = true;
    if (item->kind == ModuleItemKind::kTaskDecl) has_task = true;
  }
  EXPECT_TRUE(has_func);
  EXPECT_TRUE(has_task);
}

// §3.3: "Procedural blocks"
TEST(ParserSection3, Sec3_3_ProceduralBlocks) {
  auto r = Parse(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  initial a = 0;\n"
      "  final $display(\"done\");\n"
      "  always @(posedge clk) a <= b;\n"
      "  always_comb b = a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool has_initial = false, has_final = false;
  bool has_always = false, has_always_comb = false;
  for (const auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock) has_initial = true;
    if (item->kind == ModuleItemKind::kFinalBlock) has_final = true;
    if (item->kind == ModuleItemKind::kAlwaysBlock) {
      if (item->always_kind == AlwaysKind::kAlways) has_always = true;
      if (item->always_kind == AlwaysKind::kAlwaysComb) has_always_comb = true;
    }
  }
  EXPECT_TRUE(has_initial);
  EXPECT_TRUE(has_final);
  EXPECT_TRUE(has_always);
  EXPECT_TRUE(has_always_comb);
}

// §3.3: "Generate blocks"
TEST(ParserSection3, Sec3_3_GenerateBlocks) {
  EXPECT_TRUE(
      ParseOk("module m #(parameter N = 4) ();\n"
              "  genvar i;\n"
              "  generate\n"
              "    for (i = 0; i < N; i = i + 1) begin : gen_loop\n"
              "      logic [7:0] data;\n"
              "    end\n"
              "  endgenerate\n"
              "endmodule\n"));
}

// §3.3: "Specify blocks"
TEST(ParserSection3, Sec3_3_SpecifyBlock) {
  EXPECT_TRUE(
      ParseOk("module m (input a, output y);\n"
              "  assign y = a;\n"
              "  specify\n"
              "    (a => y) = 1.5;\n"
              "  endspecify\n"
              "endmodule\n"));
}

// §3.3: "Continuous assignments"
TEST(ParserSection3, Sec3_3_ContinuousAssignment) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, y;\n"
      "  assign y = a & b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* ca = FindItemByKind(r, ModuleItemKind::kContAssign);
  ASSERT_NE(ca, nullptr);
}

// §3.3: "Instantiations of other modules, programs, interfaces, checkers,
//        and primitives"
TEST(ParserSection3, Sec3_3_DesignElementInstantiations) {
  auto r = Parse(
      "module child; endmodule\n"
      "module top;\n"
      "  logic sig;\n"
      "  child c0();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 2u);
  // "top" is modules[1]; check it has the instantiation.
  bool has_inst = false;
  for (const auto* item : r.cu->modules[1]->items) {
    if (item->kind == ModuleItemKind::kModuleInst) has_inst = true;
  }
  EXPECT_TRUE(has_inst);
}

// =============================================================================
// LRM section 3.4 -- Programs
// =============================================================================

// §3.4: "The program building block is enclosed between the keywords
//        program...endprogram."
TEST(ParserSection3, Sec3_4_ProgramEndLabel) {
  auto r = Parse(
      "program p;\n"
      "endprogram : p\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->name, "p");
}

// §3.4 LRM example (verbatim):
//   program test (input clk, input [16:1] addr, inout [7:0] data);
//   initial begin ... end
//   endprogram
TEST(ParserSection3, Sec3_4_LrmExample) {
  auto r = Parse(
      "program test (input clk, input [16:1] addr, inout [7:0] data);\n"
      "  initial begin\n"
      "  end\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->name, "test");
  ASSERT_EQ(r.cu->programs[0]->ports.size(), 3u);
  EXPECT_EQ(r.cu->programs[0]->ports[0].name, "clk");
  EXPECT_EQ(r.cu->programs[0]->ports[1].name, "addr");
  EXPECT_EQ(r.cu->programs[0]->ports[2].name, "data");
  EXPECT_EQ(r.cu->programs[0]->ports[2].direction, Direction::kInout);
  bool has_initial = false;
  for (const auto* item : r.cu->programs[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock) has_initial = true;
  }
  EXPECT_TRUE(has_initial);
}

// §3.4: "A program block can contain data declarations"
TEST(ParserSection3, Sec3_4_DataDeclarations) {
  auto r = Parse(
      "program p;\n"
      "  logic [7:0] count;\n"
      "  int status;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_GE(r.cu->programs[0]->items.size(), 2u);
}

// §3.4: "A program block can contain ... class definitions"
TEST(ParserSection3, Sec3_4_ClassDefinition) {
  auto r = Parse(
      "program p;\n"
      "  class my_trans;\n"
      "    int data;\n"
      "  endclass\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool has_class = false;
  for (const auto* item : r.cu->programs[0]->items) {
    if (item->kind == ModuleItemKind::kClassDecl) has_class = true;
  }
  EXPECT_TRUE(has_class);
}

// §3.4: "A program block can contain ... subroutine definitions"
TEST(ParserSection3, Sec3_4_SubroutineDefinitions) {
  auto r = Parse(
      "program p;\n"
      "  function int get_val;\n"
      "    return 42;\n"
      "  endfunction\n"
      "  task run_test;\n"
      "  endtask\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool has_func = false;
  bool has_task = false;
  for (const auto* item : r.cu->programs[0]->items) {
    if (item->kind == ModuleItemKind::kFunctionDecl) has_func = true;
    if (item->kind == ModuleItemKind::kTaskDecl) has_task = true;
  }
  EXPECT_TRUE(has_func);
  EXPECT_TRUE(has_task);
}

// §3.4: "A program block can contain ... one or more initial ... procedures"
TEST(ParserSection3, Sec3_4_InitialProcedure) {
  auto r = Parse(
      "program p;\n"
      "  initial begin\n"
      "    $display(\"test\");\n"
      "  end\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool has_initial = false;
  for (const auto* item : r.cu->programs[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock) has_initial = true;
  }
  EXPECT_TRUE(has_initial);
}

// §3.4: "A program block can contain ... final procedures"
TEST(ParserSection3, Sec3_4_FinalProcedure) {
  auto r = Parse(
      "program p;\n"
      "  final begin\n"
      "    $display(\"done\");\n"
      "  end\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  bool has_final = false;
  for (const auto* item : r.cu->programs[0]->items) {
    if (item->kind == ModuleItemKind::kFinalBlock) has_final = true;
  }
  EXPECT_TRUE(has_final);
}

// §3.4: "It cannot contain always procedures" — restriction noted.
// The parser currently accepts this; semantic checking would reject it.
TEST(ParserSection3, Sec3_4_NoAlwaysProceduresNote) {
  auto r = Parse(
      "program p;\n"
      "  always @(*) begin end\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  // Parser accepts (no syntax error), but LRM §3.4 disallows always in program.
  EXPECT_FALSE(r.has_errors);
}

// §3.4: "It creates a scope that encapsulates program-wide data"
TEST(ParserSection3, Sec3_4_MultiplePrograms) {
  auto r = Parse(
      "program p1;\n"
      "  logic a;\n"
      "endprogram\n"
      "program p2;\n"
      "  logic b;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 2u);
  EXPECT_EQ(r.cu->programs[0]->name, "p1");
  EXPECT_EQ(r.cu->programs[1]->name, "p2");
}

// =============================================================================
// LRM section 6.21 -- Scope and lifetime (automatic/static)
// =============================================================================

TEST(ParserSection3, ModuleLifetimeAutomaticAndStatic) {
  EXPECT_TRUE(ParseOk("module automatic m; endmodule\n"));
  EXPECT_TRUE(ParseOk("module static m; endmodule\n"));
}

TEST(ParserSection3, FunctionLifetime) {
  // automatic
  auto ra = Parse(
      "module m;\n"
      "  function automatic int add(int a, int b); return a+b; endfunction\n"
      "endmodule\n");
  ASSERT_NE(ra.cu, nullptr);
  EXPECT_FALSE(ra.has_errors);
  EXPECT_EQ(ra.cu->modules[0]->items[0]->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_TRUE(ra.cu->modules[0]->items[0]->is_automatic);
  // static
  auto rs = Parse(
      "module m;\n"
      "  function static int mul(int a, int b); return a*b; endfunction\n"
      "endmodule\n");
  ASSERT_NE(rs.cu, nullptr);
  EXPECT_FALSE(rs.has_errors);
  EXPECT_EQ(rs.cu->modules[0]->items[0]->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_TRUE(rs.cu->modules[0]->items[0]->is_static);
}

TEST(ParserSection3, TaskLifetime) {
  auto ra =
      Parse("module m; task automatic t(input int x); endtask endmodule\n");
  ASSERT_NE(ra.cu, nullptr);
  EXPECT_FALSE(ra.has_errors);
  EXPECT_EQ(ra.cu->modules[0]->items[0]->kind, ModuleItemKind::kTaskDecl);
  EXPECT_TRUE(ra.cu->modules[0]->items[0]->is_automatic);
  auto rs = Parse("module m; task static t(input int x); endtask endmodule\n");
  ASSERT_NE(rs.cu, nullptr);
  EXPECT_FALSE(rs.has_errors);
  EXPECT_EQ(rs.cu->modules[0]->items[0]->kind, ModuleItemKind::kTaskDecl);
  EXPECT_TRUE(rs.cu->modules[0]->items[0]->is_static);
}

TEST(ParserSection3, TopLevelFunctionAutomatic) {
  // Top-level (compilation-unit scope) function with automatic lifetime
  auto r = Parse(
      "function automatic int foo(int x);\n"
      "  return x + 1;\n"
      "endfunction\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->cu_items.size(), 1u);
  EXPECT_EQ(r.cu->cu_items[0]->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_TRUE(r.cu->cu_items[0]->is_automatic);
}

TEST(ParserSection3, ProgramAutomaticLifetime) {
  // program with automatic lifetime
  EXPECT_TRUE(
      ParseOk("program automatic test_prog;\n"
              "  initial begin\n"
              "    $display(\"hello\");\n"
              "  end\n"
              "endprogram\n"));
}

// =============================================================================
// LRM section 3.14 -- Simulation time units and precision (time values)
// =============================================================================

TEST(ParserSection3, TimeunitInsideModule) {
  auto r = Parse(
      "module m;\n"
      "  timeunit 1ns;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(r.cu->modules[0]->has_timeunit);
}

TEST(ParserSection3, TimeprecisionInsideModule) {
  auto r = Parse(
      "module m;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(r.cu->modules[0]->has_timeprecision);
}

TEST(ParserSection3, TimeunitWithSlashPrecision) {
  // timeunit with combined precision (LRM 3.14.2.2)
  auto r = Parse(
      "module m;\n"
      "  timeunit 100ps / 10fs;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->has_timeunit);
}

TEST(ParserSection3, TimeunitAndTimeprecisionBoth) {
  // Both timeunit and timeprecision in one module
  auto r = Parse(
      "module m;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->has_timeunit);
  EXPECT_TRUE(r.cu->modules[0]->has_timeprecision);
}

TEST(ParserSection3, TimescaleDirective) {
  auto r = Parse(
      "`timescale 1ns/1ps\n"
      "module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ParserSection3, TimescaleMultipleModules) {
  // LRM 3.14.2.1: timescale applies to all modules that follow
  auto r = Parse(
      "`timescale 1ns/10ps\n"
      "module a; endmodule\n"
      "module b; endmodule\n"
      "`timescale 1ps/1ps\n"
      "module c; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 3u);
}

TEST(ParserSection3, TimeunitInProgram) {
  auto r = Parse(
      "program p;\n"
      "  timeunit 10us;\n"
      "  timeprecision 100ns;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
}

TEST(ParserSection3, TimeunitInInterface) {
  auto r = Parse(
      "interface ifc;\n"
      "  timeunit 1ns;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
}

// =============================================================================
// LRM section 5.8 -- Time literals
// =============================================================================

TEST(ParserSection3, TimeLiteralInDelay) {
  // Time literals: integer or fixed-point followed by a time unit (LRM 5.8)
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial #10ns $display(\"done\");\n"
              "endmodule\n"));
}

TEST(ParserSection3, TimeLiteralPicoseconds) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial #40ps $display(\"done\");\n"
              "endmodule\n"));
}

TEST(ParserSection3, TimeLiteralFractional) {
  // Fractional time literal: 2.1ns
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial #2.1ns $display(\"done\");\n"
              "endmodule\n"));
}

TEST(ParserSection3, TimeLiteralAllUnits) {
  // All time unit suffixes: s, ms, us, ns, ps, fs
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    #1s $display(\"s\");\n"
              "    #1ms $display(\"ms\");\n"
              "    #1us $display(\"us\");\n"
              "    #1ns $display(\"ns\");\n"
              "    #1ps $display(\"ps\");\n"
              "    #1fs $display(\"fs\");\n"
              "  end\n"
              "endmodule\n"));
}

// =============================================================================
// LRM section 23.2.2 -- Port declarations
// =============================================================================

// --- ANSI style ports ---

TEST(ParserSection3, AnsiPortInput) {
  auto r = Parse(
      "module m (input logic a);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInput);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "a");
}

TEST(ParserSection3, AnsiPortOutput) {
  auto r = Parse(
      "module m (output logic y);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kOutput);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "y");
}

TEST(ParserSection3, AnsiPortInout) {
  auto r = Parse(
      "module m (inout wire [7:0] data);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInout);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "data");
}

TEST(ParserSection3, AnsiPortRef) {
  auto r = Parse(
      "module m (ref logic [3:0] r);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kRef);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "r");
}

TEST(ParserSection3, AnsiPortMultipleDirections) {
  // Multiple ports with mixed directions (ANSI header)
  auto r = Parse(
      "module m (input logic clk, rst,\n"
      "          output logic [7:0] data,\n"
      "          inout wire bus);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 4u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].direction, Direction::kInput);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "clk");
  EXPECT_EQ(r.cu->modules[0]->ports[1].direction, Direction::kInput);
  EXPECT_EQ(r.cu->modules[0]->ports[1].name, "rst");
  EXPECT_EQ(r.cu->modules[0]->ports[2].direction, Direction::kOutput);
  EXPECT_EQ(r.cu->modules[0]->ports[2].name, "data");
  EXPECT_EQ(r.cu->modules[0]->ports[3].direction, Direction::kInout);
  EXPECT_EQ(r.cu->modules[0]->ports[3].name, "bus");
}

TEST(ParserSection3, AnsiPortVariants) {
  EXPECT_TRUE(ParseOk("module m (input var int in1); endmodule\n"));
  EXPECT_TRUE(ParseOk("module m (output reg [7:0] q); endmodule\n"));
  EXPECT_TRUE(ParseOk("module m (input signed [7:0] s); endmodule\n"));
}

// --- Non-ANSI style ports ---

TEST(ParserSection3, NonAnsiPortDeclaration) {
  // Non-ANSI style: port list + separate direction declarations
  auto r = Parse(
      "module m (a, b, y);\n"
      "  input a, b;\n"
      "  output y;\n"
      "  assign y = a & b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ParserSection3, NonAnsiPortVariants) {
  EXPECT_TRUE(
      ParseOk("module m (a, d); input [15:0] a; inout [7:0] d; endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module m (a, b); inout [7:0] a; inout [7:0] b; endmodule\n"));
}

// --- Port declarations in interface ---

TEST(ParserSection3, InterfaceWithPort) {
  auto r = Parse(
      "interface bus_if (input logic clk);\n"
      "  logic req, gnt;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->ports[0].name, "clk");
  EXPECT_EQ(r.cu->interfaces[0]->ports[0].direction, Direction::kInput);
}

// --- Empty port list ---

TEST(ParserSection3, EmptyPortListParens) {
  auto r = Parse("module m (); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports.size(), 0u);
}

TEST(ParserSection3, NoPortListAtAll) {
  auto r = Parse("module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->ports.size(), 0u);
}

// --- Dot-star port ---

TEST(ParserSection3, DotStarPortImplicit) {
  // LRM 23.2: module_keyword [lifetime] module_identifier (.*) ;
  EXPECT_TRUE(ParseOk("module m (.*); endmodule\n"));
}

// --- Port with default values ---

TEST(ParserSection3, AnsiPortWithDefaultValue) {
  EXPECT_TRUE(
      ParseOk("module m (input int x = 10);\n"
              "endmodule\n"));
}

// --- Interface port in module ---

TEST(ParserSection3, InterfacePortInModule) {
  // LRM 23.2.2: interface port declaration
  EXPECT_TRUE(
      ParseOk("interface myif;\n"
              "  logic [7:0] data;\n"
              "endinterface\n"
              "module m (myif bus);\n"
              "endmodule\n"));
}

// --- Module instantiation creating hierarchy ---

TEST(ParserSection3, ModuleInstantiationHierarchy) {
  auto r = Parse(
      "module top;\n"
      "  logic in1, in2, sel;\n"
      "  wire out1;\n"
      "  mux2to1 m1 (.a(in1), .b(in2), .sel(sel), .y(out1));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* inst = FindItemByKind(r, ModuleItemKind::kModuleInst);
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(inst->inst_module, "mux2to1");
  EXPECT_EQ(inst->inst_name, "m1");
}

// --- Compilation unit scope items ---

TEST(ParserSection3, TopLevelFunction) {
  auto r = Parse(
      "function automatic int foo(int x);\n"
      "  return x + 1;\n"
      "endfunction\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->cu_items.size(), 1u);
  EXPECT_EQ(r.cu->cu_items[0]->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(r.cu->cu_items[0]->name, "foo");
}

TEST(ParserSection3, TopLevelTask) {
  auto r = Parse(
      "task automatic my_task(input int x);\n"
      "endtask\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->cu_items.size(), 1u);
  EXPECT_EQ(r.cu->cu_items[0]->kind, ModuleItemKind::kTaskDecl);
}

TEST(ParserSection3, ModuleAndPackageInSameUnit) {
  auto r = Parse(
      "package pkg;\n"
      "  typedef int myint;\n"
      "endpackage\n"
      "module m;\n"
      "  import pkg::*;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->modules.size(), 1u);
}

// --- Interface with modports ---

TEST(ParserSection3, InterfaceWithModport) {
  auto r = Parse(
      "interface myif;\n"
      "  logic [7:0] data;\n"
      "  logic valid, ready;\n"
      "  modport master (output data, output valid, input ready);\n"
      "  modport slave (input data, input valid, output ready);\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  ASSERT_EQ(r.cu->interfaces[0]->modports.size(), 2u);
  EXPECT_EQ(r.cu->interfaces[0]->modports[0]->name, "master");
  EXPECT_EQ(r.cu->interfaces[0]->modports[1]->name, "slave");
}

// --- Time units with different magnitudes (LRM Table 3-1) ---

TEST(ParserSection3, TimeunitVariousMagnitudes) {
  EXPECT_TRUE(
      ParseOk("module a; timeunit 100ns; timeprecision 10ps; endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module b; timeunit 1us; timeprecision 1ns; endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module c; timeunit 1ps; timeprecision 1fs; endmodule\n"));
  EXPECT_TRUE(
      ParseOk("module d; timeunit 10ms; timeprecision 100us; endmodule\n"));
}
