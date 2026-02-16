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
// LRM section 6.21 -- Scope and lifetime (automatic/static)
// =============================================================================

TEST(ParserSection3, ModuleLifetimeAutomatic) {
  // module with automatic lifetime (LRM 23.2.1)
  auto r = Parse(
      "module automatic m;\n"
      "  function int foo(int x);\n"
      "    return x + 1;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ParserSection3, ModuleLifetimeStatic) {
  // module with static lifetime
  auto r = Parse(
      "module static m;\n"
      "  function int bar(int x);\n"
      "    return x * 2;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ParserSection3, FunctionAutomaticLifetime) {
  // function declared with automatic lifetime (LRM 6.21)
  auto r = Parse(
      "module m;\n"
      "  function automatic int add(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 1u);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_TRUE(item->is_automatic);
}

TEST(ParserSection3, FunctionStaticLifetime) {
  // function declared with static lifetime
  auto r = Parse(
      "module m;\n"
      "  function static int mul(int a, int b);\n"
      "    return a * b;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 1u);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_TRUE(item->is_static);
}

TEST(ParserSection3, TaskAutomaticLifetime) {
  // task declared with automatic lifetime
  auto r = Parse(
      "module m;\n"
      "  task automatic my_task(input int x);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 1u);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_TRUE(item->is_automatic);
}

TEST(ParserSection3, TaskStaticLifetime) {
  auto r = Parse(
      "module m;\n"
      "  task static my_task(input int x);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->modules[0]->items.size(), 1u);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTaskDecl);
  EXPECT_TRUE(item->is_static);
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

TEST(ParserSection3, AnsiPortInputVar) {
  // input var int -- variable port type (LRM 23.2.2.3)
  EXPECT_TRUE(
      ParseOk("module m (input var int in1, input var shortreal in2);\n"
              "endmodule\n"));
}

TEST(ParserSection3, AnsiPortOutputRegister) {
  // output reg (ANSI style)
  EXPECT_TRUE(
      ParseOk("module m (output reg [7:0] q);\n"
              "endmodule\n"));
}

TEST(ParserSection3, AnsiPortSigned) {
  // Signed port declaration
  EXPECT_TRUE(
      ParseOk("module m (input signed [7:0] s_data);\n"
              "endmodule\n"));
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

TEST(ParserSection3, NonAnsiPortWithWidth) {
  // Non-ANSI ports with vector width
  EXPECT_TRUE(
      ParseOk("module m (addr, data);\n"
              "  input [15:0] addr;\n"
              "  inout [7:0] data;\n"
              "endmodule\n"));
}

TEST(ParserSection3, NonAnsiPortInoutBidirectional) {
  EXPECT_TRUE(
      ParseOk("module m (a, b);\n"
              "  inout [7:0] a;\n"
              "  inout [7:0] b;\n"
              "endmodule\n"));
}

// --- Port declarations in program and interface ---

TEST(ParserSection3, ProgramWithPorts) {
  auto r = Parse(
      "program test (input clk, input [15:0] addr, inout [7:0] data);\n"
      "  initial begin\n"
      "  end\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->ports.size(), 3u);
}

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

// --- Time units with different magnitudes ---

TEST(ParserSection3, TimeunitAllMagnitudes) {
  // LRM Table 3-1: 1, 10, or 100 with s, ms, us, ns, ps, fs
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  timeunit 100ns;\n"
              "  timeprecision 10ps;\n"
              "endmodule\n"));
}

TEST(ParserSection3, TimeunitMicroseconds) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  timeunit 1us;\n"
              "  timeprecision 1ns;\n"
              "endmodule\n"));
}

TEST(ParserSection3, TimeunitFemtoseconds) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  timeunit 1ps;\n"
              "  timeprecision 1fs;\n"
              "endmodule\n"));
}

TEST(ParserSection3, TimeunitMilliseconds) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  timeunit 10ms;\n"
              "  timeprecision 100us;\n"
              "endmodule\n"));
}
