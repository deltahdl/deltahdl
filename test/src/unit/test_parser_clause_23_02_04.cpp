#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

// Syntax 23-5: "zero" case — a module definition may contain no module items.
TEST(ModuleItemsParsing, EmptyModuleBody) {
  auto r = Parse("module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(r.cu->modules[0]->items.empty());
}

// Syntax 23-5: "more" case — a module definition may contain many module items
// of several different alternatives at once.
TEST(ModuleItemsParsing, AllModuleItemAlternatives) {
  auto r = Parse(
      "module m(input a, output y);\n"
      "  wire w1, w2;\n"
      "  logic v;\n"
      "  assign y = a;\n"
      "  alias w1 = w2;\n"
      "  initial begin end\n"
      "  final begin end\n"
      "  always_comb begin end\n"
      "  genvar i;\n"
      "  if (1) begin : g\n"
      "    wire gw;\n"
      "  end\n"
      "  defparam u.W = 8;\n"
      "  specify\n"
      "    (a => y) = 1;\n"
      "  endspecify\n"
      "  specparam delay = 5;\n"
      "  $info;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_GE(r.cu->modules[0]->items.size(), 10u);
}

// module_common_item alternative: continuous_assign.
TEST(ModuleItemsParsing, ContinuousAssign) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b, y;\n"
      "  assign y = a & b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kContAssign));
}

// module_common_item alternative: initial_construct.
TEST(ModuleItemsParsing, InitialConstruct) {
  auto r = Parse(
      "module m;\n"
      "  initial begin end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kInitialBlock));
}

// module_common_item alternative: final_construct.
TEST(ModuleItemsParsing, FinalConstruct) {
  auto r = Parse(
      "module m;\n"
      "  final begin end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kFinalBlock));
}

// module_common_item alternative: always_construct. The four always_keyword
// kinds are a §9.2 distinction; §23.2.4 only requires always_construct to be a
// module item, so a single observer suffices here.
TEST(ModuleItemsParsing, AlwaysConstructPlain) {
  auto r = Parse(
      "module m;\n"
      "  always @(posedge clk) begin end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasAlwaysOfKind(r.cu->modules[0]->items, AlwaysKind::kAlways));
}

// module_common_item alternative: loop_generate_construct.
TEST(ModuleItemsParsing, LoopGenerateConstruct) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 4; i = i + 1) begin : gen_blk\n"
      "    wire w;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kGenerateFor));
}

// module_common_item alternative: conditional_generate_construct. The if vs
// case forms are a §27.5 distinction, so one observer covers §23.2.4.
TEST(ModuleItemsParsing, ConditionalGenerateIf) {
  auto r = Parse(
      "module m;\n"
      "  if (1) begin : yes\n"
      "    wire w;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kGenerateIf));
}

// module_or_generate_item alternative: parameter_override (BNF-6). The number
// of defparam assignments is a list_of_defparam_assignments (A.2.4) detail.
TEST(ModuleItemsParsing, ParameterOverride) {
  auto r = Parse(
      "module m;\n"
      "  defparam u1.W = 16;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kDefparam));
}

// module_or_generate_item alternative: gate_instantiation.
TEST(ModuleItemsParsing, GateInstantiation) {
  auto r = Parse(
      "module m;\n"
      "  and g1(y, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kGateInst));
}

// module_or_generate_item alternative: udp_instantiation.
TEST(ModuleItemsParsing, UdpInstantiation) {
  auto r = Parse(
      "primitive my_udp(output y, input a, b);\n"
      "  table\n"
      "    0 0 : 0;\n"
      "    0 1 : 1;\n"
      "    1 0 : 1;\n"
      "    1 1 : 0;\n"
      "  endtable\n"
      "endprimitive\n"
      "module m;\n"
      "  my_udp u1(y, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kUdpInst));
}

// module_or_generate_item alternative: module_instantiation.
TEST(ModuleItemsParsing, ModuleInstantiation) {
  auto r = Parse(
      "module m;\n"
      "  sub u1(.a(x), .b(y));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kModuleInst));
}

// module_common_item alternative: interface_instantiation. A distinct Syntax
// 23-5 alternative even though the parser shares the instantiation AST kind.
TEST(ModuleItemsParsing, InterfaceInstantiation) {
  auto r = Parse(
      "module m;\n"
      "  bus_if bus_inst(.clk(clk));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kModuleInst));
}

// module_common_item alternative: program_instantiation.
TEST(ModuleItemsParsing, ProgramInstantiationInModule) {
  auto r = Parse(
      "program prg;\n"
      "endprogram\n"
      "module m;\n"
      "  prg p1();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kModuleInst));
}

// module_common_item alternative: assertion_item. The assert/assume/cover/
// restrict forms are a §16.14.6 distinction, so one observer covers §23.2.4.
TEST(ModuleItemsParsing, AssertionItem) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a |-> b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kAssertProperty));
}

// module_common_item alternative: bind_directive. Recorded on the enclosing
// module rather than its item list.
TEST(ModuleItemsParsing, BindDirectiveAsModuleItem) {
  auto r = Parse(
      "module m;\n"
      "  bind target_mod chk chk_i(.a(s));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->bind_directives.size(), 1u);
}

// module_common_item alternative: net_alias. The number of aliased nets is a
// §10.11 detail, not a §23.2.4 distinction.
TEST(ModuleItemsParsing, NetAlias) {
  auto r = Parse(
      "module m;\n"
      "  wire w1, w2;\n"
      "  alias w1 = w2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kAlias));
}

// module_or_generate_item_declaration alternative:
// package_or_generate_item_declaration (here a class declaration).
TEST(ModuleItemsParsing, ClassInsideModule) {
  auto r = Parse(
      "module m;\n"
      "  class inner_cls;\n"
      "    int x;\n"
      "  endclass\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* cls = FindClassDeclItem(r.cu->modules[0]->items);
  ASSERT_NE(cls, nullptr);
  EXPECT_EQ(cls->name, "inner_cls");
}

// module_or_generate_item_declaration alternative: genvar_declaration.
TEST(ModuleItemsParsing, GenvarDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  genvar i, j;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// module_or_generate_item_declaration alternative: clocking_declaration.
TEST(ModuleItemsParsing, ClockingDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kClockingBlock));
}

// module_or_generate_item_declaration alternative: default clocking ... ;
TEST(ModuleItemsParsing, DefaultClocking) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "  endclocking\n"
      "  default clocking cb;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// module_or_generate_item_declaration alternative: default disable iff ... ;
TEST(ModuleItemsParsing, DefaultDisableIff) {
  auto r = Parse(
      "module m;\n"
      "  default disable iff rst;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(r.cu->modules[0]->items,
                            ModuleItemKind::kDefaultDisableIff));
}

// non_port_module_item alternative: generate_region.
TEST(ModuleItemsParsing, GenerateRegion) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "    wire w;\n"
      "  endgenerate\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// non_port_module_item alternative: specify_block.
TEST(ModuleItemsParsing, SpecifyBlock) {
  auto r = Parse(
      "module m(input a, output y);\n"
      "  specify\n"
      "    (a => y) = 1;\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kSpecifyBlock));
}

// non_port_module_item alternative: specparam_declaration.
TEST(ModuleItemsParsing, SpecparamDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  specparam delay = 10;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kSpecparam));
}

// non_port_module_item alternative: module_declaration (nested module).
TEST(ModuleItemsParsing, NestedModuleDeclaration) {
  auto r = Parse(
      "module outer;\n"
      "  module inner;\n"
      "  endmodule\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r.cu->modules[0]->items,
                              ModuleItemKind::kNestedModuleDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->nested_module_decl, nullptr);
  EXPECT_EQ(item->nested_module_decl->decl_kind, ModuleDeclKind::kModule);
  EXPECT_EQ(item->nested_module_decl->name, "inner");
}

// non_port_module_item alternative: interface_declaration (nested interface).
TEST(ModuleItemsParsing, NestedInterfaceDeclaration) {
  auto r = Parse(
      "module outer;\n"
      "  interface inner_if;\n"
      "  endinterface\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r.cu->modules[0]->items,
                              ModuleItemKind::kNestedModuleDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->nested_module_decl, nullptr);
  EXPECT_EQ(item->nested_module_decl->decl_kind, ModuleDeclKind::kInterface);
}

// non_port_module_item alternative: program_declaration (nested program).
TEST(ModuleItemsParsing, NestedProgramDeclaration) {
  auto r = Parse(
      "module outer;\n"
      "  program inner_pgm;\n"
      "  endprogram\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r.cu->modules[0]->items,
                              ModuleItemKind::kNestedModuleDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->nested_module_decl, nullptr);
  EXPECT_EQ(item->nested_module_decl->decl_kind, ModuleDeclKind::kProgram);
}

// module_item alternative: port_declaration ; (non-ANSI port declaration item).
TEST(ModuleItemsParsing, PortDeclAsModuleItem) {
  auto r = Parse(
      "module m(a, b, y);\n"
      "  input a, b;\n"
      "  output y;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// Syntax 23-5 attribute_instance prefix on a module_or_generate_item.
TEST(ModuleItemsParsing, ItemWithAttributes) {
  auto r = Parse(
      "module m;\n"
      "  (* full_case *) wire w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// An elaboration system task accepted as a module item. The particular
// severity ($fatal/$error/$warning/$info) is a §20.11 distinction.
TEST(ModuleItemsParsing, ElabFatalTask) {
  auto r = Parse(
      "module m;\n"
      "  $fatal(1, \"error message\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kElabSystemTask));
}

// non_port_module_item alternative: timeunits_declaration. timeunit, time-
// precision, and the combined form are a §3.14.2 distinction.
TEST(ModuleItemsParsing, TimeunitAsModuleItem) {
  auto r = Parse(
      "module m;\n"
      "  timeunit 1ns;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->has_timeunit);
}

// Footnote 3: a later timeunits_declaration is legal when it repeats and
// matches a prior declaration in the same time scope.
TEST(ModuleItemsParsing, TimeunitRepeatMatches) {
  auto r = Parse(
      "module m;\n"
      "  timeunit 1ns;\n"
      "  wire w;\n"
      "  timeunit 1ns;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// Footnote 3: a later timeunits_declaration with no prior declaration to repeat
// is illegal.
TEST(ModuleItemsParsing, ErrorTimeunitNoPriorDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  wire w;\n"
      "  timeunit 1ns;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// Footnote 3: a repeated timeunits_declaration that does not match the prior
// one is illegal.
TEST(ModuleItemsParsing, ErrorTimeunitMismatch) {
  auto r = Parse(
      "module m;\n"
      "  timeunit 1ns;\n"
      "  wire w;\n"
      "  timeunit 1us;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// parameter_override is terminated by ';' (BNF-6).
TEST(ModuleItemsParsing, ErrorDefparamMissingSemicolon) {
  auto r = Parse(
      "module m;\n"
      "  defparam u.W = 16\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// A generate_region must be closed with endgenerate.
TEST(ModuleItemsParsing, ErrorUnclosedGenerateRegion) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "    wire w;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// A net_alias module item is terminated by ';'.
TEST(ModuleItemsParsing, ErrorNetAliasMissingSemicolon) {
  auto r = Parse(
      "module m;\n"
      "  wire w1, w2;\n"
      "  alias w1 = w2\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

// A timeunits_declaration module item is terminated by ';'.
TEST(ModuleItemsParsing, ErrorTimeunitMissingSemicolon) {
  auto r = Parse(
      "module m;\n"
      "  timeunit 1ns\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
