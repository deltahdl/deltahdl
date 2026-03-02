// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

static bool HasItemOfKind(const std::vector<ModuleItem*>& items,
                          ModuleItemKind kind) {
  for (const auto* item : items)
    if (item->kind == kind) return true;
  return false;
}

static ModuleItem* FindItemByKind(ParseResult& r, ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

namespace {

TEST_F(AnnexHParseTest, AnnexOMultipleDpiDecls) {
  auto* unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" function int c_add(int a, int b);\n"
      "  import \"DPI-C\" pure function real c_sin(real x);\n"
      "  export \"DPI-C\" function sv_compute;\n"
      "  export \"DPI-C\" task sv_run;\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 4u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(items[0]->name, "c_add");
  EXPECT_EQ(items[1]->kind, ModuleItemKind::kDpiImport);
  EXPECT_EQ(items[1]->name, "c_sin");
  EXPECT_TRUE(items[1]->dpi_is_pure);
  EXPECT_EQ(items[2]->kind, ModuleItemKind::kDpiExport);
  EXPECT_EQ(items[2]->name, "sv_compute");
  EXPECT_FALSE(items[2]->dpi_is_task);
  EXPECT_EQ(items[3]->kind, ModuleItemKind::kDpiExport);
  EXPECT_EQ(items[3]->name, "sv_run");
  EXPECT_TRUE(items[3]->dpi_is_task);
}

// =============================================================================
// LRM §3.2 — Design elements
// =============================================================================
TEST(ParserClause03, AllSevenDesignElements) {
  // §3.2: A design element is a module, program, interface, checker,
  //       package, primitive, or configuration.
  auto r = ParseWithPreprocessor(
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
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
  EXPECT_EQ(r.cu->modules[0]->decl_kind, ModuleDeclKind::kModule);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->name, "p");
  EXPECT_EQ(r.cu->programs[0]->decl_kind, ModuleDeclKind::kProgram);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->name, "ifc");
  EXPECT_EQ(r.cu->interfaces[0]->decl_kind, ModuleDeclKind::kInterface);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->name, "chk");
  EXPECT_EQ(r.cu->checkers[0]->decl_kind, ModuleDeclKind::kChecker);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_EQ(r.cu->packages[0]->name, "pkg");
  ASSERT_EQ(r.cu->udps.size(), 1u);
  EXPECT_EQ(r.cu->udps[0]->name, "udp_and");
  ASSERT_EQ(r.cu->configs.size(), 1u);
  EXPECT_EQ(r.cu->configs[0]->name, "cfg");
  // Multiple design elements of same type in one compilation unit
  EXPECT_TRUE(ParseOk("module a; endmodule\nmodule b; endmodule\n"));
  // Module + package coexist in same unit with import
  EXPECT_TRUE(
      ParseOk("package p; typedef int myint; endpackage\n"
              "module m; import p::*; endmodule\n"));
}

// Multiple descriptions in source text.
TEST(SourceText, MultipleDescriptions) {
  auto r = ParseWithPreprocessor(
      "module m1; endmodule\n"
      "interface ifc; endinterface\n"
      "program prg; endprogram\n"
      "package pkg; endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->packages.size(), 1u);
}

// =============================================================================
// LRM §3.4 — Programs
// =============================================================================
// §3.4 LRM example (verbatim) with end label:
//   program test (input clk, input [16:1] addr, inout [7:0] data);
//   initial begin ... end
//   endprogram : test
TEST(ParserClause03, Cl3_4_LrmExample) {
  auto r = ParseWithPreprocessor(
      "program test (input clk, input [16:1] addr, inout [7:0] data);\n"
      "  initial begin\n"
      "  end\n"
      "endprogram : test\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_EQ(r.cu->programs[0]->name, "test");
  ASSERT_EQ(r.cu->programs[0]->ports.size(), 3u);
  EXPECT_EQ(r.cu->programs[0]->ports[0].name, "clk");
  EXPECT_EQ(r.cu->programs[0]->ports[1].name, "addr");
  EXPECT_EQ(r.cu->programs[0]->ports[2].name, "data");
  EXPECT_EQ(r.cu->programs[0]->ports[2].direction, Direction::kInout);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kInitialBlock));
}

// §3.4:
TEST(ParserClause03, Cl3_4_DataAndClassDeclarations) {
  auto r = ParseWithPreprocessor(
      "program p;\n"
      "  logic [7:0] count;\n"
      "  int status;\n"
      "  class my_trans; int data; endclass\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_GE(r.cu->programs[0]->items.size(), 3u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kClassDecl));
  // §3.4: Multiple programs each create separate scopes
  EXPECT_TRUE(
      ParseOk("program p1; logic a; endprogram\n"
              "program p2; logic b; endprogram\n"));
}

// §3.4: "A program block can contain ... subroutine definitions ...
//        initial ... final procedures"
TEST(ParserClause03, Cl3_4_SubroutinesAndProcedures) {
  auto r = ParseWithPreprocessor(
      "program p;\n"
      "  function int get_val; return 42; endfunction\n"
      "  task run_test; endtask\n"
      "  initial $display(\"test\");\n"
      "  final $display(\"done\");\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kFunctionDecl));
  EXPECT_TRUE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kTaskDecl));
  EXPECT_TRUE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kInitialBlock));
  EXPECT_TRUE(
      HasItemOfKind(r.cu->programs[0]->items, ModuleItemKind::kFinalBlock));
}

// §3.4:
TEST(ParserClause03, Cl3_4_RejectsDisallowedItems) {
  EXPECT_TRUE(
      ParseWithPreprocessor("program p; always @(*) begin end endprogram\n")
          .has_errors);
  EXPECT_TRUE(
      ParseWithPreprocessor("program p; always_comb begin end endprogram\n")
          .has_errors);
  EXPECT_TRUE(ParseWithPreprocessor(
                  "program p; always_ff @(posedge clk) begin end endprogram\n")
                  .has_errors);
  EXPECT_TRUE(
      ParseWithPreprocessor("program p; always_latch begin end endprogram\n")
          .has_errors);
  EXPECT_TRUE(ParseWithPreprocessor("module c; endmodule\n"
                                    "program p; c i(); endprogram\n")
                  .has_errors);
  // Interface and program instances hit the same instantiation path.
  EXPECT_TRUE(ParseWithPreprocessor("interface ifc; endinterface\n"
                                    "program p; ifc i(); endprogram\n")
                  .has_errors);
}

// =============================================================================
// LRM §3.5 — Interfaces
// =============================================================================
// §3.5 LRM example: simple_bus interface definition.
// Also covers end label (endinterface : simple_bus) and interface port.
TEST(ParserClause03, Cl3_5_LrmExample) {
  auto r = ParseWithPreprocessor(
      "interface simple_bus(input logic clk);\n"
      "  logic req, gnt;\n"
      "  logic [7:0] addr, data;\n"
      "  logic [1:0] mode;\n"
      "  logic start, rdy;\n"
      "endinterface : simple_bus\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->name, "simple_bus");
  ASSERT_EQ(r.cu->interfaces[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->interfaces[0]->ports[0].name, "clk");
  EXPECT_EQ(r.cu->interfaces[0]->ports[0].direction, Direction::kInput);
  EXPECT_GE(r.cu->interfaces[0]->items.size(), 5u);
}

// §3.5:
TEST(ParserClause03, Cl3_5_ParametersConstantsVariables) {
  auto r = ParseWithPreprocessor(
      "interface ifc #(parameter WIDTH = 8);\n"
      "  localparam DEPTH = 16;\n"
      "  logic [WIDTH-1:0] data;\n"
      "  wire valid;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_GE(r.cu->interfaces[0]->items.size(), 2u);
}

// §3.5:
TEST(ParserClause03, Cl3_5_FunctionsAndTasks) {
  auto r = ParseWithPreprocessor(
      "interface ifc;\n"
      "  function automatic int get_data;\n"
      "    return 42;\n"
      "  endfunction\n"
      "  task automatic send(input int val);\n"
      "  endtask\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->interfaces[0]->items, ModuleItemKind::kFunctionDecl));
  EXPECT_TRUE(
      HasItemOfKind(r.cu->interfaces[0]->items, ModuleItemKind::kTaskDecl));
}

// §3.5: "an interface can also contain processes (i.e., initial or always
//        procedures) and continuous assignments"
TEST(ParserClause03, Cl3_5_ProcessesAndContinuousAssign) {
  auto r = ParseWithPreprocessor(
      "interface ifc;\n"
      "  logic sig_a, sig_b;\n"
      "  initial sig_a = 0;\n"
      "  always @(sig_a) sig_b = ~sig_a;\n"
      "  assign sig_b = sig_a;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->interfaces[0]->items, ModuleItemKind::kInitialBlock));
  EXPECT_TRUE(
      HasItemOfKind(r.cu->interfaces[0]->items, ModuleItemKind::kAlwaysBlock));
  EXPECT_TRUE(
      HasItemOfKind(r.cu->interfaces[0]->items, ModuleItemKind::kContAssign));
}

// §3.5: "the modport construct is provided"
TEST(ParserClause03, Cl3_5_Modport) {
  auto r = ParseWithPreprocessor(
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

// =============================================================================
// LRM §3.6 — Checkers
// =============================================================================
// §3.6: Checker encapsulates assertions (assert property, cover property,
//        property/sequence declarations) — the primary purpose of checkers.
TEST(ParserClause03, Cl3_6_AssertionsInChecker) {
  auto r = ParseWithPreprocessor(
      "checker req_ack_chk(logic clk, req, ack);\n"
      "  property req_followed_by_ack;\n"
      "    @(posedge clk) req |-> ##[1:3] ack;\n"
      "  endproperty\n"
      "  assert property (req_followed_by_ack);\n"
      "  cover property (req_followed_by_ack);\n"
      "endchecker : req_ack_chk\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->name, "req_ack_chk");
  ASSERT_GE(r.cu->checkers[0]->ports.size(), 3u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kPropertyDecl));
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kAssertProperty));
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kCoverProperty));
}

// §3.6: Checker also encapsulates "modeling code" — variables, initial blocks,
//        always blocks used alongside assertions for auxiliary verification.
TEST(ParserClause03, Cl3_6_ModelingCodeInChecker) {
  auto r = ParseWithPreprocessor(
      "checker model_chk;\n"
      "  logic flag;\n"
      "  initial flag = 0;\n"
      "  always @(flag) flag <= ~flag;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kInitialBlock));
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kAlwaysBlock));
  EXPECT_GE(r.cu->checkers[0]->items.size(), 3u);  // var + initial + always
}

// =============================================================================
// LRM §3.8 — Subroutines
// =============================================================================
// §3.8: "A task is called as a statement. A task can have any number of
//        input, output, inout, and ref arguments, but does not return a
//        value. Tasks can block simulation time during execution."
TEST(ParserClause03, Cl3_8_TaskAllDirectionsAndBlocking) {
  auto r = ParseWithPreprocessor(
      "module m;\n"
      "  task my_task(input int a, output int b, inout int c, ref int d);\n"
      "    #10;\n"
      "    b = a + c;\n"
      "    c = d;\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* task = FindItemByKind(r, ModuleItemKind::kTaskDecl);
  ASSERT_NE(task, nullptr);
  EXPECT_EQ(task->name, "my_task");
  ASSERT_EQ(task->func_args.size(), 4u);
  EXPECT_EQ(task->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(task->func_args[1].direction, Direction::kOutput);
  EXPECT_EQ(task->func_args[2].direction, Direction::kInout);
  EXPECT_EQ(task->func_args[3].direction, Direction::kRef);
  // Task has a body with delay (#10 blocks time) + assignments
  EXPECT_GE(task->func_body_stmts.size(), 1u);
}

}  // namespace
