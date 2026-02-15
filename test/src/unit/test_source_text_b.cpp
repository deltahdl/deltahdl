#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// --- Test helpers ---

namespace {

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string& src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

}  // namespace

// =============================================================================
// A.1.5 Configuration source text
// =============================================================================

// config_declaration: config name; design statement; endconfig
TEST(SourceText, ConfigDeclBasic) {
  auto r = Parse(
      "config cfg1;\n"
      "  design work.top;\n"
      "  default liblist work;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  auto* c = r.cu->configs[0];
  EXPECT_EQ(c->name, "cfg1");
  ASSERT_EQ(c->design_cells.size(), 1u);
  EXPECT_EQ(c->design_cells[0].first, "work");
  EXPECT_EQ(c->design_cells[0].second, "top");
  ASSERT_EQ(c->rules.size(), 1u);
  EXPECT_EQ(c->rules[0]->kind, ConfigRuleKind::kDefault);
}

// config_declaration with endconfig label
TEST(SourceText, ConfigDeclEndLabel) {
  auto r = Parse(
      "config cfg2;\n"
      "  design top;\n"
      "endconfig : cfg2\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->configs.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->name, "cfg2");
}

// config_declaration with local_parameter_declaration
TEST(SourceText, ConfigDeclLocalParams) {
  auto r = Parse(
      "config cfg3;\n"
      "  localparam WIDTH = 8;\n"
      "  localparam DEPTH = 4;\n"
      "  design work.top;\n"
      "  default liblist work;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* c = r.cu->configs[0];
  ASSERT_EQ(c->local_params.size(), 2u);
  EXPECT_EQ(c->local_params[0].first, "WIDTH");
  EXPECT_EQ(c->local_params[1].first, "DEPTH");
}

// design_statement: multiple cells, with and without library qualifier
TEST(SourceText, ConfigDesignMultipleCells) {
  auto r = Parse(
      "config cfg4;\n"
      "  design work.top lib2.sub cellonly;\n"
      "  default liblist work;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* c = r.cu->configs[0];
  ASSERT_EQ(c->design_cells.size(), 3u);
  EXPECT_EQ(c->design_cells[0].first, "work");
  EXPECT_EQ(c->design_cells[0].second, "top");
  EXPECT_EQ(c->design_cells[1].first, "lib2");
  EXPECT_EQ(c->design_cells[1].second, "sub");
  // Unqualified cell: lib is empty
  EXPECT_EQ(c->design_cells[2].first, "");
  EXPECT_EQ(c->design_cells[2].second, "cellonly");
}

// config_rule_statement: default_clause liblist_clause
TEST(SourceText, ConfigRuleDefaultLiblist) {
  auto r = Parse(
      "config cfg5;\n"
      "  design top;\n"
      "  default liblist lib1 lib2 lib3;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kDefault);
  ASSERT_EQ(rule->liblist.size(), 3u);
  EXPECT_EQ(rule->liblist[0], "lib1");
  EXPECT_EQ(rule->liblist[1], "lib2");
  EXPECT_EQ(rule->liblist[2], "lib3");
}

// config_rule_statement: inst_clause liblist_clause with hierarchical inst_name
TEST(SourceText, ConfigRuleInstLiblist) {
  auto r = Parse(
      "config cfg6;\n"
      "  design top;\n"
      "  instance top.u1.u2 liblist mylib;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kInstance);
  EXPECT_EQ(rule->inst_path, "top.u1.u2");
  ASSERT_EQ(rule->liblist.size(), 1u);
  EXPECT_EQ(rule->liblist[0], "mylib");
}

// config_rule_statement: inst_clause use_clause
TEST(SourceText, ConfigRuleInstUse) {
  auto r = Parse(
      "config cfg7;\n"
      "  design top;\n"
      "  instance top.u1 use work.alt_cell;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kInstance);
  EXPECT_EQ(rule->inst_path, "top.u1");
  EXPECT_EQ(rule->use_lib, "work");
  EXPECT_EQ(rule->use_cell, "alt_cell");
}

// config_rule_statement: cell_clause liblist_clause
TEST(SourceText, ConfigRuleCellLiblist) {
  auto r = Parse(
      "config cfg8;\n"
      "  design top;\n"
      "  cell mylib.mycell liblist lib_a lib_b;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kCell);
  EXPECT_EQ(rule->cell_lib, "mylib");
  EXPECT_EQ(rule->cell_name, "mycell");
  ASSERT_EQ(rule->liblist.size(), 2u);
  EXPECT_EQ(rule->liblist[0], "lib_a");
  EXPECT_EQ(rule->liblist[1], "lib_b");
}

// config_rule_statement: cell_clause use_clause with :config suffix
TEST(SourceText, ConfigRuleCellUseConfig) {
  auto r = Parse(
      "config cfg9;\n"
      "  design top;\n"
      "  cell flip_flop use work.ff_impl :config;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kCell);
  EXPECT_EQ(rule->cell_name, "flip_flop");
  EXPECT_EQ(rule->use_lib, "work");
  EXPECT_EQ(rule->use_cell, "ff_impl");
  EXPECT_TRUE(rule->use_config);
}

// use_clause: use with named_parameter_assignment
TEST(SourceText, ConfigUseNamedParams) {
  auto r = Parse(
      "config cfg10;\n"
      "  design top;\n"
      "  instance top.u1 use #(.WIDTH(16), .DEPTH(4));\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kInstance);
  ASSERT_EQ(rule->use_params.size(), 2u);
  EXPECT_EQ(rule->use_params[0].first, "WIDTH");
  EXPECT_EQ(rule->use_params[1].first, "DEPTH");
}

// use_clause: use [lib.] cell named_parameter_assignment (combined form)
TEST(SourceText, ConfigUseCellAndParams) {
  auto r = Parse(
      "config cfg11;\n"
      "  design top;\n"
      "  cell adder use work.fast_add #(.W(32)) :config;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->use_lib, "work");
  EXPECT_EQ(rule->use_cell, "fast_add");
  ASSERT_EQ(rule->use_params.size(), 1u);
  EXPECT_EQ(rule->use_params[0].first, "W");
  EXPECT_TRUE(rule->use_config);
}

// Comprehensive: multiple rules of different kinds in one config
TEST(SourceText, ConfigMultipleRules) {
  auto r = Parse(
      "config cfg12;\n"
      "  design work.top;\n"
      "  default liblist work rtl;\n"
      "  instance top.dut use gate.dut_impl;\n"
      "  cell lib.ram liblist sram_lib;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* c = r.cu->configs[0];
  ASSERT_EQ(c->rules.size(), 3u);
  EXPECT_EQ(c->rules[0]->kind, ConfigRuleKind::kDefault);
  EXPECT_EQ(c->rules[1]->kind, ConfigRuleKind::kInstance);
  EXPECT_EQ(c->rules[2]->kind, ConfigRuleKind::kCell);
}

// cell_clause: unqualified cell identifier (no library prefix)
TEST(SourceText, ConfigCellUnqualified) {
  auto r = Parse(
      "config cfg13;\n"
      "  design top;\n"
      "  cell mux4 use better_mux;\n"
      "endconfig\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* rule = r.cu->configs[0]->rules[0];
  EXPECT_EQ(rule->kind, ConfigRuleKind::kCell);
  EXPECT_EQ(rule->cell_lib, "");
  EXPECT_EQ(rule->cell_name, "mux4");
  EXPECT_EQ(rule->use_cell, "better_mux");
}

// =============================================================================
// A.1.6 Interface items
// =============================================================================

// interface_or_generate_item ::= { attribute_instance } module_common_item
// Verify that a module_common_item (continuous assign) is accepted inside an
// interface body, producing an item in the interface's items list.
TEST(SourceText, InterfaceOrGenerateItemModuleCommon) {
  auto r = Parse(
      "interface ifc;\n"
      "  assign a = b;\n"
      "endinterface\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  auto* ifc = r.cu->interfaces[0];
  ASSERT_GE(ifc->items.size(), 1u);
  EXPECT_EQ(ifc->items[0]->kind, ModuleItemKind::kContAssign);
}

// interface_or_generate_item ::= { attribute_instance } extern_tf_declaration
// extern_tf_declaration ::= extern method_prototype ;
// Verify extern function prototype inside an interface.
TEST(SourceText, ExternFunctionPrototypeInInterface) {
  auto r = Parse(
      "interface ifc;\n"
      "  extern function void compute(input int x);\n"
      "endinterface\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  auto* ifc = r.cu->interfaces[0];
  ASSERT_GE(ifc->items.size(), 1u);
  EXPECT_EQ(ifc->items[0]->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(ifc->items[0]->name, "compute");
  EXPECT_TRUE(ifc->items[0]->is_extern);
  // Prototype only — no body statements.
  EXPECT_TRUE(ifc->items[0]->func_body_stmts.empty());
}

// extern_tf_declaration ::= extern method_prototype ;
// method_prototype ::= task_prototype — extern task prototype.
TEST(SourceText, ExternTaskPrototypeInInterface) {
  auto r = Parse(
      "interface ifc;\n"
      "  extern task run();\n"
      "endinterface\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  auto* ifc = r.cu->interfaces[0];
  ASSERT_GE(ifc->items.size(), 1u);
  EXPECT_EQ(ifc->items[0]->kind, ModuleItemKind::kTaskDecl);
  EXPECT_EQ(ifc->items[0]->name, "run");
  EXPECT_TRUE(ifc->items[0]->is_extern);
  EXPECT_TRUE(ifc->items[0]->func_body_stmts.empty());
}

// extern_tf_declaration ::= extern forkjoin task_prototype ;
TEST(SourceText, ExternForkjoinTaskPrototype) {
  auto r = Parse(
      "interface ifc;\n"
      "  extern forkjoin task parallel_run();\n"
      "endinterface\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  auto* ifc = r.cu->interfaces[0];
  ASSERT_GE(ifc->items.size(), 1u);
  EXPECT_EQ(ifc->items[0]->kind, ModuleItemKind::kTaskDecl);
  EXPECT_EQ(ifc->items[0]->name, "parallel_run");
  EXPECT_TRUE(ifc->items[0]->is_extern);
  EXPECT_TRUE(ifc->items[0]->is_forkjoin);
  EXPECT_TRUE(ifc->items[0]->func_body_stmts.empty());
}

// extern_tf_declaration inside a module (interface_or_generate_item applies
// to modules too via module_or_generate_item).
TEST(SourceText, ExternFunctionPrototypeInModule) {
  auto r = Parse(
      "module m;\n"
      "  extern function int compute(input int a, input int b);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* mod = r.cu->modules[0];
  ASSERT_GE(mod->items.size(), 1u);
  EXPECT_EQ(mod->items[0]->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(mod->items[0]->name, "compute");
  EXPECT_TRUE(mod->items[0]->is_extern);
  EXPECT_TRUE(mod->items[0]->func_body_stmts.empty());
}

// interface_item ::= port_declaration ;
// Verify that port declarations are accepted in interface ANSI port list.
TEST(SourceText, InterfaceItemPortDecl) {
  auto r = Parse(
      "interface ifc(input logic clk, output logic data);\n"
      "endinterface\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->ports.size(), 2u);
  EXPECT_EQ(r.cu->interfaces[0]->ports[0].name, "clk");
  EXPECT_EQ(r.cu->interfaces[0]->ports[1].name, "data");
}

// non_port_interface_item ::= generate_region
TEST(SourceText, NonPortInterfaceItemGenerateRegion) {
  auto r = Parse(
      "interface ifc;\n"
      "  generate\n"
      "    assign a = b;\n"
      "  endgenerate\n"
      "endinterface\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_GE(r.cu->interfaces[0]->items.size(), 1u);
}

// non_port_interface_item ::= program_declaration
TEST(SourceText, NonPortInterfaceItemProgram) {
  auto r = Parse(
      "interface ifc;\n"
      "  program p; endprogram\n"
      "endinterface\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  ASSERT_GE(r.cu->interfaces[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->items[0]->kind,
            ModuleItemKind::kNestedModuleDecl);
}

// non_port_interface_item ::= modport_declaration
TEST(SourceText, NonPortInterfaceItemModport) {
  auto r = Parse(
      "interface ifc;\n"
      "  modport master(input clk, output data);\n"
      "endinterface\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  ASSERT_EQ(r.cu->interfaces[0]->modports.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->modports[0]->name, "master");
}

// non_port_interface_item ::= interface_declaration (nested interface)
TEST(SourceText, NonPortInterfaceItemNestedInterface) {
  auto r = Parse(
      "interface outer;\n"
      "  interface inner; endinterface\n"
      "endinterface\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  ASSERT_GE(r.cu->interfaces[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->items[0]->kind,
            ModuleItemKind::kNestedModuleDecl);
}

// non_port_interface_item ::= timeunits_declaration
TEST(SourceText, NonPortInterfaceItemTimeunits) {
  auto r = Parse(
      "interface ifc;\n"
      "  timeunit 1ns;\n"
      "endinterface\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
}

// Combined: interface with multiple A.1.6 item types.
TEST(SourceText, InterfaceMultipleItemTypes) {
  auto r = Parse(
      "interface bus_if;\n"
      "  logic [7:0] data;\n"
      "  extern function void validate();\n"
      "  extern forkjoin task run_parallel();\n"
      "  modport master(output data);\n"
      "  modport slave(input data);\n"
      "endinterface\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  auto* ifc = r.cu->interfaces[0];
  // data var + extern function + extern forkjoin task = 3 items
  ASSERT_GE(ifc->items.size(), 3u);
  EXPECT_EQ(ifc->modports.size(), 2u);
  // Verify the extern function.
  bool found_extern_func = false;
  bool found_forkjoin_task = false;
  for (auto* item : ifc->items) {
    if (item->kind == ModuleItemKind::kFunctionDecl && item->is_extern) {
      found_extern_func = true;
      EXPECT_EQ(item->name, "validate");
    }
    if (item->kind == ModuleItemKind::kTaskDecl && item->is_forkjoin) {
      found_forkjoin_task = true;
      EXPECT_EQ(item->name, "run_parallel");
    }
  }
  EXPECT_TRUE(found_extern_func);
  EXPECT_TRUE(found_forkjoin_task);
}

// =============================================================================
// A.1.7 Program items
// =============================================================================

// program_item ::= port_declaration ;
TEST(SourceText, ProgramItemPortDecl) {
  auto r = Parse(
      "program prg(input logic clk, output logic done);\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  auto* p = r.cu->programs[0];
  EXPECT_EQ(p->name, "prg");
  EXPECT_EQ(p->ports.size(), 2u);
  EXPECT_EQ(p->ports[0].direction, Direction::kInput);
  EXPECT_EQ(p->ports[1].direction, Direction::kOutput);
}

// non_port_program_item ::= continuous_assign
TEST(SourceText, ProgramContinuousAssign) {
  auto r = Parse(
      "program prg;\n"
      "  logic a, b;\n"
      "  assign a = b;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  bool found_assign = false;
  for (auto* item : r.cu->programs[0]->items) {
    if (item->kind == ModuleItemKind::kContAssign) found_assign = true;
  }
  EXPECT_TRUE(found_assign);
}

// non_port_program_item ::= module_or_generate_item_declaration
TEST(SourceText, ProgramModuleOrGenerateItemDecl) {
  auto r = Parse(
      "program prg;\n"
      "  int count;\n"
      "  function void compute(); endfunction\n"
      "  task run(); endtask\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  auto& items = r.cu->programs[0]->items;
  bool found_var = false;
  bool found_func = false;
  bool found_task = false;
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kVarDecl && item->name == "count")
      found_var = true;
    if (item->kind == ModuleItemKind::kFunctionDecl && item->name == "compute")
      found_func = true;
    if (item->kind == ModuleItemKind::kTaskDecl && item->name == "run")
      found_task = true;
  }
  EXPECT_TRUE(found_var);
  EXPECT_TRUE(found_func);
  EXPECT_TRUE(found_task);
}

// non_port_program_item ::= initial_construct
TEST(SourceText, ProgramInitialConstruct) {
  auto r = Parse(
      "program prg;\n"
      "  initial begin\n"
      "    $display(\"hello\");\n"
      "  end\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  bool found_initial = false;
  for (auto* item : r.cu->programs[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock) found_initial = true;
  }
  EXPECT_TRUE(found_initial);
}

// non_port_program_item ::= final_construct
TEST(SourceText, ProgramFinalConstruct) {
  auto r = Parse(
      "program prg;\n"
      "  final begin\n"
      "    $display(\"done\");\n"
      "  end\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  bool found_final = false;
  for (auto* item : r.cu->programs[0]->items) {
    if (item->kind == ModuleItemKind::kFinalBlock) found_final = true;
  }
  EXPECT_TRUE(found_final);
}

// non_port_program_item ::= concurrent_assertion_item
TEST(SourceText, ProgramConcurrentAssertion) {
  auto r = Parse(
      "program prg;\n"
      "  logic clk, a;\n"
      "  assert property (@(posedge clk) a);\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  bool found_assert = false;
  for (auto* item : r.cu->programs[0]->items) {
    if (item->kind == ModuleItemKind::kAssertProperty) found_assert = true;
  }
  EXPECT_TRUE(found_assert);
}

// non_port_program_item ::= timeunits_declaration
TEST(SourceText, ProgramTimeunitsDecl) {
  auto r = Parse(
      "program prg;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->name, "prg");
}

// program_generate_item ::= loop_generate_construct
TEST(SourceText, ProgramGenerateLoop) {
  auto r = Parse(
      "program prg;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 4; i = i + 1) begin : blk\n"
      "    int x;\n"
      "  end\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  bool found_for = false;
  for (auto* item : r.cu->programs[0]->items) {
    if (item->kind == ModuleItemKind::kGenerateFor) found_for = true;
  }
  EXPECT_TRUE(found_for);
}

// program_generate_item ::= conditional_generate_construct
TEST(SourceText, ProgramGenerateConditional) {
  auto r = Parse(
      "program prg;\n"
      "  parameter P = 1;\n"
      "  if (P) begin : blk\n"
      "    int x;\n"
      "  end\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  bool found_if = false;
  for (auto* item : r.cu->programs[0]->items) {
    if (item->kind == ModuleItemKind::kGenerateIf) found_if = true;
  }
  EXPECT_TRUE(found_if);
}

// program_generate_item ::= generate_region
TEST(SourceText, ProgramGenerateRegion) {
  auto r = Parse(
      "program prg;\n"
      "  generate\n"
      "    int x;\n"
      "  endgenerate\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_FALSE(r.cu->programs[0]->items.empty());
}

// program_generate_item ::= elaboration_severity_system_task
TEST(SourceText, ProgramElabSeverityTask) {
  auto r = Parse(
      "program prg;\n"
      "  $info(\"program loaded\");\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  bool found_elab = false;
  for (auto* item : r.cu->programs[0]->items) {
    if (item->kind == ModuleItemKind::kElabSystemTask) found_elab = true;
  }
  EXPECT_TRUE(found_elab);
}

// Combined: program with multiple A.1.7 item types.
TEST(SourceText, ProgramMultipleItemTypes) {
  auto r = Parse(
      "program prg(input logic clk);\n"
      "  timeunit 1ns;\n"
      "  int count;\n"
      "  assign count = 0;\n"
      "  initial begin $display(\"start\"); end\n"
      "  final begin $display(\"end\"); end\n"
      "  assert property (@(posedge clk) count >= 0);\n"
      "  generate int g; endgenerate\n"
      "  $warning(\"check\");\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  auto& items = r.cu->programs[0]->items;
  bool found_var = false;
  bool found_assign = false;
  bool found_initial = false;
  bool found_final = false;
  bool found_assert = false;
  bool found_elab = false;
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kVarDecl) found_var = true;
    if (item->kind == ModuleItemKind::kContAssign) found_assign = true;
    if (item->kind == ModuleItemKind::kInitialBlock) found_initial = true;
    if (item->kind == ModuleItemKind::kFinalBlock) found_final = true;
    if (item->kind == ModuleItemKind::kAssertProperty) found_assert = true;
    if (item->kind == ModuleItemKind::kElabSystemTask) found_elab = true;
  }
  EXPECT_TRUE(found_var);
  EXPECT_TRUE(found_assign);
  EXPECT_TRUE(found_initial);
  EXPECT_TRUE(found_final);
  EXPECT_TRUE(found_assert);
  EXPECT_TRUE(found_elab);
}

// =============================================================================
// A.1.8 Checker items
// =============================================================================

// checker_port_list / checker_port_item / checker_port_direction
TEST(SourceText, CheckerPortList) {
  auto r = Parse(
      "checker chk(input logic clk, output bit valid);\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  auto* chk = r.cu->checkers[0];
  EXPECT_EQ(chk->name, "chk");
  EXPECT_EQ(chk->decl_kind, ModuleDeclKind::kChecker);
  ASSERT_EQ(chk->ports.size(), 2u);
  EXPECT_EQ(chk->ports[0].direction, Direction::kInput);
  EXPECT_EQ(chk->ports[0].name, "clk");
  EXPECT_EQ(chk->ports[1].direction, Direction::kOutput);
  EXPECT_EQ(chk->ports[1].name, "valid");
}

// checker_port_item with default value (= property_actual_arg)
TEST(SourceText, CheckerPortDefaultValue) {
  auto r = Parse(
      "checker chk(input logic clk = 1'b0);\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_EQ(r.cu->checkers[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->ports[0].direction, Direction::kInput);
  EXPECT_EQ(r.cu->checkers[0]->ports[0].name, "clk");
  EXPECT_NE(r.cu->checkers[0]->ports[0].default_value, nullptr);
}

// checker_or_generate_item ::= continuous_assign
TEST(SourceText, CheckerContinuousAssign) {
  auto r = Parse(
      "checker chk;\n"
      "  assign a = b;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_GE(r.cu->checkers[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->items[0]->kind, ModuleItemKind::kContAssign);
}

// checker_or_generate_item ::= initial_construct | always_construct |
// final_construct
TEST(SourceText, CheckerInitialAlwaysFinal) {
  auto r = Parse(
      "checker chk;\n"
      "  initial begin end\n"
      "  always @(posedge clk) x <= 1;\n"
      "  final begin end\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  auto& items = r.cu->checkers[0]->items;
  ASSERT_GE(items.size(), 3u);
  bool found_initial = false, found_always = false, found_final = false;
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kInitialBlock) found_initial = true;
    if (item->kind == ModuleItemKind::kAlwaysBlock) found_always = true;
    if (item->kind == ModuleItemKind::kFinalBlock) found_final = true;
  }
  EXPECT_TRUE(found_initial);
  EXPECT_TRUE(found_always);
  EXPECT_TRUE(found_final);
}

// checker_or_generate_item ::= assertion_item
TEST(SourceText, CheckerAssertionItem) {
  auto r = Parse(
      "checker chk;\n"
      "  assert property (@(posedge clk) a |-> b);\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_GE(r.cu->checkers[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->items[0]->kind, ModuleItemKind::kAssertProperty);
}

// checker_or_generate_item_declaration ::= [rand] data_declaration
TEST(SourceText, CheckerRandDataDecl) {
  auto r = Parse(
      "checker chk;\n"
      "  rand bit [3:0] val;\n"
      "  logic [7:0] data;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_GE(r.cu->checkers[0]->items.size(), 2u);
  EXPECT_EQ(r.cu->checkers[0]->items[0]->kind, ModuleItemKind::kVarDecl);
  EXPECT_TRUE(r.cu->checkers[0]->items[0]->is_rand);
  EXPECT_EQ(r.cu->checkers[0]->items[1]->kind, ModuleItemKind::kVarDecl);
  EXPECT_FALSE(r.cu->checkers[0]->items[1]->is_rand);
}

// checker_or_generate_item_declaration ::= function_declaration
TEST(SourceText, CheckerFunctionDecl) {
  auto r = Parse(
      "checker chk;\n"
      "  function automatic int add(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_GE(r.cu->checkers[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->items[0]->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(r.cu->checkers[0]->items[0]->name, "add");
}

// checker_or_generate_item_declaration ::= checker_declaration (nested)
TEST(SourceText, CheckerNestedChecker) {
  auto r = Parse(
      "checker outer;\n"
      "  checker inner;\n"
      "    logic a;\n"
      "  endchecker\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->name, "outer");
}

// checker_or_generate_item_declaration ::= genvar_declaration
TEST(SourceText, CheckerGenvarDecl) {
  auto r = Parse(
      "checker chk;\n"
      "  genvar i;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_GE(r.cu->checkers[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->items[0]->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(r.cu->checkers[0]->items[0]->name, "i");
}

// checker_or_generate_item_declaration ::= default disable iff expr ;
TEST(SourceText, CheckerDefaultDisableIff) {
  auto r = Parse(
      "checker chk;\n"
      "  default disable iff rst;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_GE(r.cu->checkers[0]->items.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->items[0]->kind,
            ModuleItemKind::kDefaultDisableIff);
}

// checker_generate_item ::= loop | conditional | generate_region | elab task
TEST(SourceText, CheckerGenerateItems) {
  auto r = Parse(
      "checker chk;\n"
      "  for (genvar i = 0; i < 4; i++) begin end\n"
      "  if (1) begin end\n"
      "  generate endgenerate\n"
      "  $info(\"checker ok\");\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  auto& items = r.cu->checkers[0]->items;
  bool found_for = false, found_if = false, found_elab = false;
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kGenerateFor) found_for = true;
    if (item->kind == ModuleItemKind::kGenerateIf) found_if = true;
    if (item->kind == ModuleItemKind::kElabSystemTask) found_elab = true;
  }
  EXPECT_TRUE(found_for);
  EXPECT_TRUE(found_if);
  EXPECT_TRUE(found_elab);
}

// Combined: checker with multiple A.1.8 item types.
TEST(SourceText, CheckerMultipleItemTypes) {
  auto r = Parse(
      "checker chk(input logic clk, output bit ok);\n"
      "  logic sig;\n"
      "  assign ok = sig;\n"
      "  initial begin end\n"
      "  always @(posedge clk) sig <= 1;\n"
      "  final begin end\n"
      "  assert property (@(posedge clk) sig);\n"
      "  default disable iff !ok;\n"
      "  function int f(); return 0; endfunction\n"
      "  $warning(\"test\");\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  auto* chk = r.cu->checkers[0];
  EXPECT_EQ(chk->name, "chk");
  ASSERT_EQ(chk->ports.size(), 2u);
  bool found_var = false, found_assign = false, found_initial = false;
  bool found_always = false, found_final = false, found_assert = false;
  bool found_disable = false, found_func = false, found_elab = false;
  for (auto* item : chk->items) {
    if (item->kind == ModuleItemKind::kVarDecl) found_var = true;
    if (item->kind == ModuleItemKind::kContAssign) found_assign = true;
    if (item->kind == ModuleItemKind::kInitialBlock) found_initial = true;
    if (item->kind == ModuleItemKind::kAlwaysBlock) found_always = true;
    if (item->kind == ModuleItemKind::kFinalBlock) found_final = true;
    if (item->kind == ModuleItemKind::kAssertProperty) found_assert = true;
    if (item->kind == ModuleItemKind::kDefaultDisableIff) found_disable = true;
    if (item->kind == ModuleItemKind::kFunctionDecl) found_func = true;
    if (item->kind == ModuleItemKind::kElabSystemTask) found_elab = true;
  }
  EXPECT_TRUE(found_var);
  EXPECT_TRUE(found_assign);
  EXPECT_TRUE(found_initial);
  EXPECT_TRUE(found_always);
  EXPECT_TRUE(found_final);
  EXPECT_TRUE(found_assert);
  EXPECT_TRUE(found_disable);
  EXPECT_TRUE(found_func);
  EXPECT_TRUE(found_elab);
}
