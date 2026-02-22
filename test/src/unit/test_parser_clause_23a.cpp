#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
};

static ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

// --- Non-ANSI port declarations (LRM §23.2.2.1) ---

TEST(ParserSection23, NonAnsiPortsBasic) {
  auto r = Parse("module m(a, b);\n"
                 "  input a;\n"
                 "  output b;\n"
                 "  assign b = a;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 2);
  struct Expected {
    const char *name;
    Direction dir;
  };
  Expected expected[] = {{"a", Direction::kInput}, {"b", Direction::kOutput}};
  for (size_t i = 0; i < 2; ++i) {
    EXPECT_EQ(mod->ports[i].name, expected[i].name);
    EXPECT_EQ(mod->ports[i].direction, expected[i].dir);
  }
}

TEST(ParserSection23, NonAnsiPortsWithTypesPortA) {
  auto r = Parse("module m(a, b);\n"
                 "  input [7:0] a;\n"
                 "  output reg b;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 2);
  EXPECT_EQ(mod->ports[0].name, "a");
  EXPECT_EQ(mod->ports[0].direction, Direction::kInput);
  EXPECT_NE(mod->ports[0].data_type.packed_dim_left, nullptr);
}

TEST(ParserSection23, NonAnsiPortsWithTypesPortB) {
  auto r = Parse("module m(a, b);\n"
                 "  input [7:0] a;\n"
                 "  output reg b;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 2);
  EXPECT_EQ(mod->ports[1].name, "b");
  EXPECT_EQ(mod->ports[1].direction, Direction::kOutput);
  EXPECT_EQ(mod->ports[1].data_type.kind, DataTypeKind::kReg);
}

TEST(ParserSection23, NonAnsiPortsMixed) {
  auto r = Parse("module m(a, b, c, d);\n"
                 "  input a, b;\n"
                 "  output [3:0] c;\n"
                 "  inout d;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 4);
  struct Expected {
    const char *name;
    Direction dir;
  };
  Expected expected[] = {
      {"a", Direction::kInput},
      {"b", Direction::kInput},
      {"c", Direction::kOutput},
      {"d", Direction::kInout},
  };
  for (size_t i = 0; i < 4; ++i) {
    EXPECT_EQ(mod->ports[i].name, expected[i].name);
    EXPECT_EQ(mod->ports[i].direction, expected[i].dir);
  }
  EXPECT_NE(mod->ports[2].data_type.packed_dim_left, nullptr);
}

// --- Wildcard .* port connections (LRM §23.3.2.4) ---

TEST(ParserSection23, WildcardConnection) {
  auto r = Parse("module top;\n"
                 "  sub m1(.*);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "sub");
  EXPECT_EQ(item->inst_name, "m1");
  EXPECT_TRUE(item->inst_wildcard);
}

TEST(ParserSection23, WildcardWithNamed) {
  auto r = Parse("module top;\n"
                 "  sub m1(.*, .clk(sys_clk));\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_TRUE(item->inst_wildcard);
  ASSERT_EQ(item->inst_ports.size(), 1);
  EXPECT_EQ(item->inst_ports[0].first, "clk");
}

// --- Extern module declarations (LRM §23.2.1) ---

TEST(ParserSection23, ExternModuleHeader) {
  auto r = Parse("extern module foo(input logic a, output logic b);\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  auto *mod = r.cu->modules[0];
  EXPECT_EQ(mod->name, "foo");
  EXPECT_TRUE(mod->is_extern);
  EXPECT_TRUE(mod->items.empty());
}

TEST(ParserSection23, ExternModulePorts) {
  auto r = Parse("extern module foo(input logic a, output logic b);\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 2);
  struct Expected {
    const char *name;
    Direction dir;
  };
  Expected expected[] = {{"a", Direction::kInput}, {"b", Direction::kOutput}};
  for (size_t i = 0; i < 2; ++i) {
    EXPECT_EQ(mod->ports[i].name, expected[i].name);
    EXPECT_EQ(mod->ports[i].direction, expected[i].dir);
  }
}

TEST(ParserSection23, ExternModuleNoBody) {
  auto r = Parse("extern module bar(input logic x);\n"
                 "module baz; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 2);
  struct Expected {
    const char *name;
    bool is_extern;
  };
  Expected expected[] = {{"bar", true}, {"baz", false}};
  for (size_t i = 0; i < 2; ++i) {
    EXPECT_EQ(r.cu->modules[i]->name, expected[i].name);
    EXPECT_EQ(r.cu->modules[i]->is_extern, expected[i].is_extern);
  }
}

// --- Instance arrays (LRM §23.3.2) ---

TEST(ParserSection23, InstanceArrayKind) {
  auto r = Parse("module top;\n"
                 "  sub inst[3:0] (.a(a), .b(b));\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "sub");
  EXPECT_EQ(item->inst_name, "inst");
}

TEST(ParserSection23, InstanceArrayRange) {
  auto r = Parse("module top;\n"
                 "  sub inst[3:0] (.a(a), .b(b));\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_NE(item->inst_range_left, nullptr);
  EXPECT_NE(item->inst_range_right, nullptr);
}

TEST(ParserSection23, InstanceArraySingle) {
  auto r = Parse("module top;\n"
                 "  sub inst[8] (.a(a));\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_name, "inst");
  EXPECT_NE(item->inst_range_left, nullptr);
  // Single dimension: only left is set, right is nullptr.
  EXPECT_EQ(item->inst_range_right, nullptr);
}

// --- End labels on design elements (LRM section 3) ---

TEST(ParserSection23, EndLabelModule) {
  auto r = Parse("module foo; endmodule : foo\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  EXPECT_EQ(r.cu->modules[0]->name, "foo");
}

TEST(ParserSection23, EndLabelModuleNoLabel) {
  auto r = Parse("module bar; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  EXPECT_EQ(r.cu->modules[0]->name, "bar");
}

TEST(ParserSection23, EndLabelPackage) {
  auto r = Parse("package mypkg; endpackage : mypkg\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->packages.size(), 1);
  EXPECT_EQ(r.cu->packages[0]->name, "mypkg");
}

TEST(ParserSection23, EndLabelInterface) {
  auto r = Parse("interface myif; endinterface : myif\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->interfaces.size(), 1);
  EXPECT_EQ(r.cu->interfaces[0]->name, "myif");
}

TEST(ParserSection23, EndLabelProgram) {
  auto r = Parse("program myprog; endprogram : myprog\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->programs.size(), 1);
  EXPECT_EQ(r.cu->programs[0]->name, "myprog");
}

TEST(ParserSection23, EndLabelClass) {
  auto r = Parse("class myclass; endclass : myclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1);
  EXPECT_EQ(r.cu->classes[0]->name, "myclass");
}

// --- Multi-item import (LRM section 26.3) ---

static void VerifyImportItem(const ModuleItem *item, const char *pkg,
                             const char *name) {
  EXPECT_EQ(item->kind, ModuleItemKind::kImportDecl);
  EXPECT_EQ(item->import_item.package_name, pkg);
  EXPECT_EQ(item->import_item.item_name, name);
}

TEST(ParserSection23, MultiItemImport) {
  auto r = Parse("module m;\n"
                 "  import pkg::a, pkg::b;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 2);
  VerifyImportItem(mod->items[0], "pkg", "a");
  VerifyImportItem(mod->items[1], "pkg", "b");
}

TEST(ParserSection23, MultiItemImportWithWildcardFirst) {
  auto r = Parse("module m;\n"
                 "  import pkg::*, other::func;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 2);
  EXPECT_EQ(mod->items[0]->import_item.package_name, "pkg");
  EXPECT_TRUE(mod->items[0]->import_item.is_wildcard);
}

TEST(ParserSection23, MultiItemImportWithWildcardSecond) {
  auto r = Parse("module m;\n"
                 "  import pkg::*, other::func;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 2);
  EXPECT_EQ(mod->items[1]->import_item.package_name, "other");
  EXPECT_EQ(mod->items[1]->import_item.item_name, "func");
}

// --- Package export declarations (LRM section 26.6) ---

TEST(ParserSection23, ExportDecl) {
  auto r = Parse("package p;\n"
                 "  export pkg::*;\n"
                 "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  auto *pkg = r.cu->packages[0];
  ASSERT_EQ(pkg->items.size(), 1);
  EXPECT_EQ(pkg->items[0]->kind, ModuleItemKind::kExportDecl);
  EXPECT_EQ(pkg->items[0]->import_item.package_name, "pkg");
  EXPECT_TRUE(pkg->items[0]->import_item.is_wildcard);
}

TEST(ParserSection23, ExportWildcardAll) {
  auto r = Parse("package p;\n"
                 "  export *::*;\n"
                 "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  auto *pkg = r.cu->packages[0];
  ASSERT_EQ(pkg->items.size(), 1);
  EXPECT_EQ(pkg->items[0]->kind, ModuleItemKind::kExportDecl);
  EXPECT_EQ(pkg->items[0]->import_item.package_name, "*");
  EXPECT_TRUE(pkg->items[0]->import_item.is_wildcard);
}

// --- timeunit / timeprecision (LRM section 3.14) ---

TEST(ParserSection23, TimeunitDecl) {
  auto r = Parse("module m;\n"
                 "  timeunit 1ns;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
  // timeunit is consumed; no items generated (just parsed and skipped).
}

TEST(ParserSection23, TimeprecisionDecl) {
  auto r = Parse("module m;\n"
                 "  timeprecision 1ps;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
}

TEST(ParserSection23, TimeunitAndTimeprecision) {
  auto r = Parse("module m;\n"
                 "  timeunit 1ns;\n"
                 "  timeprecision 100ps;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
}

// --- Lifetime qualifier on module/interface/program (LRM section 3) ---

TEST(ParserSection23, ModuleLifetimeAutomatic) {
  auto r = Parse("module automatic m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
}

TEST(ParserSection23, ModuleLifetimeStatic) {
  auto r = Parse("module static m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
}

TEST(ParserSection23, InterfaceLifetimeAutomatic) {
  auto r = Parse("interface automatic myif; endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->interfaces.size(), 1);
  EXPECT_EQ(r.cu->interfaces[0]->name, "myif");
}

TEST(ParserSection23, ProgramLifetimeAutomatic) {
  auto r = Parse("program automatic myprog; endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->programs.size(), 1);
  EXPECT_EQ(r.cu->programs[0]->name, "myprog");
}

// --- Package import in module headers (LRM section 26.4) ---

TEST(ParserSection23, ModuleHeaderImport) {
  auto r = Parse("module m import pkg::*; ();\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  EXPECT_EQ(mod->name, "m");
  // The header import generates an import item in the module body.
  ASSERT_GE(mod->items.size(), 1);
  EXPECT_EQ(mod->items[0]->kind, ModuleItemKind::kImportDecl);
}

TEST(ParserSection23, ModuleHeaderImportDetails) {
  auto r = Parse("module m import pkg::*; ();\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  ASSERT_GE(mod->items.size(), 1);
  EXPECT_EQ(mod->items[0]->import_item.package_name, "pkg");
  EXPECT_TRUE(mod->items[0]->import_item.is_wildcard);
}

TEST(ParserSection23, ModuleHeaderImportWithParamsImport) {
  auto r = Parse("module m import A::*; #(parameter N = 4) (input logic clk);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  EXPECT_EQ(mod->name, "m");
  ASSERT_GE(mod->items.size(), 1);
  EXPECT_EQ(mod->items[0]->kind, ModuleItemKind::kImportDecl);
}

TEST(ParserSection23, ModuleHeaderImportWithParamsPortsAndParams) {
  auto r = Parse("module m import A::*; #(parameter N = 4) (input logic clk);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  ASSERT_EQ(mod->params.size(), 1);
  ASSERT_EQ(mod->ports.size(), 1);
}

TEST(ParserSection23, ModuleHeaderMultipleImportsFirst) {
  auto r = Parse("module m import A::*, B::foo; ();\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  EXPECT_EQ(mod->name, "m");
  ASSERT_GE(mod->items.size(), 2);
  EXPECT_EQ(mod->items[0]->import_item.package_name, "A");
  EXPECT_TRUE(mod->items[0]->import_item.is_wildcard);
}

TEST(ParserSection23, ModuleHeaderMultipleImportsSecond) {
  auto r = Parse("module m import A::*, B::foo; ();\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  ASSERT_GE(mod->items.size(), 2);
  EXPECT_EQ(mod->items[1]->import_item.package_name, "B");
  EXPECT_EQ(mod->items[1]->import_item.item_name, "foo");
}

// =============================================================================
// LRM section 23.2 -- Module definitions (additional)
// =============================================================================

TEST(ParserSection23, ModuleWithParameters) {
  auto r = Parse("module m #(parameter WIDTH = 8, parameter DEPTH = 16)(\n"
                 "  input logic [WIDTH-1:0] data_in,\n"
                 "  output logic [WIDTH-1:0] data_out\n"
                 ");\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  EXPECT_EQ(mod->name, "m");
  ASSERT_EQ(mod->params.size(), 2u);
  EXPECT_EQ(mod->params[0].first, "WIDTH");
  EXPECT_EQ(mod->params[1].first, "DEPTH");
  ASSERT_EQ(mod->ports.size(), 2u);
}

TEST(ParserSection23, ModuleEmptyPortList) {
  auto r = Parse("module m(); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
  EXPECT_TRUE(r.cu->modules[0]->ports.empty());
}

TEST(ParserSection23, ModuleNoPortList) {
  auto r = Parse("module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
  EXPECT_TRUE(r.cu->modules[0]->ports.empty());
}

// =============================================================================
// LRM section 23.3 -- Ports (additional)
// =============================================================================

TEST(ParserSection23, AnsiPortsInputOutput) {
  auto r = Parse("module m(input logic clk, input logic rst, output logic q);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 3u);
  EXPECT_EQ(mod->ports[0].direction, Direction::kInput);
  EXPECT_EQ(mod->ports[0].name, "clk");
  EXPECT_EQ(mod->ports[2].direction, Direction::kOutput);
  EXPECT_EQ(mod->ports[2].name, "q");
}

TEST(ParserSection23, AnsiPortsWithDefaultType) {
  auto r = Parse("module m(input a, output b);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 2u);
  EXPECT_EQ(mod->ports[0].direction, Direction::kInput);
  EXPECT_EQ(mod->ports[1].direction, Direction::kOutput);
}

TEST(ParserSection23, AnsiPortsInout) {
  auto r = Parse("module m(inout wire [7:0] data);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 1u);
  EXPECT_EQ(mod->ports[0].direction, Direction::kInout);
  EXPECT_EQ(mod->ports[0].name, "data");
}

// =============================================================================
// LRM section 23.10 -- Module instantiation / parameter override
// =============================================================================

TEST(ParserSection23, ModuleInstBasic) {
  auto r = Parse("module top;\n"
                 "  sub u1(.a(w1), .b(w2));\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "sub");
  EXPECT_EQ(item->inst_name, "u1");
  ASSERT_EQ(item->inst_ports.size(), 2u);
}

TEST(ParserSection23, ModuleInstWithParamOverride) {
  auto r = Parse("module top;\n"
                 "  sub #(8, 16) u1(.a(w1));\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "sub");
  ASSERT_EQ(item->inst_params.size(), 2u);
}

TEST(ParserSection23, ModuleInstNamedParamOverride) {
  auto r = Parse("module top;\n"
                 "  sub #(.WIDTH(8), .DEPTH(16)) u1(.a(w1));\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "sub");
}

// =============================================================================
// LRM section 23.10.2 -- Generated instantiation
// =============================================================================

TEST(ParserSection23, GenerateForInstantiation) {
  auto r = Parse("module top;\n"
                 "  for (genvar i = 0; i < 4; i++) begin : gen_blk\n"
                 "    sub u(.a(w[i]));\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1u);
  EXPECT_EQ(mod->items[0]->kind, ModuleItemKind::kGenerateFor);
  ASSERT_EQ(mod->items[0]->gen_body.size(), 1u);
  EXPECT_EQ(mod->items[0]->gen_body[0]->kind, ModuleItemKind::kModuleInst);
}

// =============================================================================
// LRM section 23.10.2.1 -- Generate blocks
// =============================================================================

TEST(ParserSection23, GenerateBlockLabeled) {
  auto r = Parse("module top;\n"
                 "  if (1) begin : blk\n"
                 "    wire a;\n"
                 "    assign a = 1;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1u);
  EXPECT_EQ(mod->items[0]->kind, ModuleItemKind::kGenerateIf);
  ASSERT_GE(mod->items[0]->gen_body.size(), 2u);
}

// =============================================================================
// LRM section 23.10.2.2 -- Conditional generate
// =============================================================================

TEST(ParserSection23, ConditionalGenerateIfElse) {
  auto r = Parse("module top;\n"
                 "  if (WIDTH == 8) begin\n"
                 "    assign out = a;\n"
                 "  end else begin\n"
                 "    assign out = b;\n"
                 "  end\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateIf);
  ASSERT_NE(gen->gen_else, nullptr);
}

TEST(ParserSection23, ConditionalGenerateCase) {
  auto r = Parse("module top;\n"
                 "  case (MODE)\n"
                 "    0: assign out = a;\n"
                 "    1: assign out = b;\n"
                 "    default: assign out = 0;\n"
                 "  endcase\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateCase);
  ASSERT_EQ(gen->gen_case_items.size(), 3u);
}

// =============================================================================
// LRM section 23.10.4 -- Port connection rules (additional)
// =============================================================================

TEST(ParserSection23, PortConnectionPositional) {
  auto r = Parse("module top;\n"
                 "  sub u1(a, b, c);\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "sub");
  ASSERT_EQ(item->inst_ports.size(), 3u);
}

TEST(ParserSection23, PortConnectionNamed) {
  auto r = Parse("module top;\n"
                 "  sub u1(.clk(sys_clk), .rst(sys_rst), .data(bus));\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  ASSERT_EQ(item->inst_ports.size(), 3u);
  EXPECT_EQ(item->inst_ports[0].first, "clk");
  EXPECT_EQ(item->inst_ports[1].first, "rst");
  EXPECT_EQ(item->inst_ports[2].first, "data");
}

TEST(ParserSection23, PortConnectionEmptyNamed) {
  auto r = Parse("module top;\n"
                 "  sub u1(.clk(sys_clk), .unused());\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  ASSERT_EQ(item->inst_ports.size(), 2u);
  EXPECT_EQ(item->inst_ports[1].first, "unused");
  EXPECT_EQ(item->inst_ports[1].second, nullptr);
}

// =============================================================================
// LRM section 23.3.2 -- Module instantiation syntax (additional)
// =============================================================================
