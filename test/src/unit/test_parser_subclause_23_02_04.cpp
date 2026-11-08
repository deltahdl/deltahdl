#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"

using namespace delta;
namespace {

TEST(ModuleItemsParsing, EmptyModuleBody) {
  auto r = Parse("module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(r.cu->modules[0]->items.empty());
}

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

TEST(ModuleItemsParsing, AlwaysConstructPlain) {
  auto r = Parse(
      "module m;\n"
      "  always @(posedge clk) begin end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasAlwaysOfKind(r.cu->modules[0]->items, AlwaysKind::kAlways));
}

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

TEST(ModuleItemsParsing, GenvarDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  genvar i, j;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

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

TEST(ModuleItemsParsing, PortDeclAsModuleItem) {
  auto r = Parse(
      "module m(a, b, y);\n"
      "  input a, b;\n"
      "  output y;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ModuleItemsParsing, ItemWithAttributes) {
  auto r = Parse(
      "module m;\n"
      "  (* full_case *) wire w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

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

TEST(ModuleItemsParsing, TimeunitAsModuleItem) {
  auto r = Parse(
      "module m;\n"
      "  timeunit 1ns;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->has_timeunit);
}

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

TEST(ModuleItemsParsing, ErrorTimeunitNoPriorDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  wire w;\n"
      "  timeunit 1ns;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "timeunit as a later item requires a matching "
                            "prior declaration in the same time scope",
                            3, "3.14.2.2"));
}

TEST(ModuleItemsParsing, ErrorTimeunitMismatch) {
  auto r = Parse(
      "module m;\n"
      "  timeunit 1ns;\n"
      "  wire w;\n"
      "  timeunit 1us;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "timeunit does not match prior declaration", 4, "3.14.2.2"));
}

TEST(ModuleItemsParsing, ErrorDefparamMissingSemicolon) {
  auto r = Parse(
      "module m;\n"
      "  defparam u.W = 16\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got 'endmodule'", 3, "23.10.1"));
}

TEST(ModuleItemsParsing, ErrorUnclosedGenerateRegion) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "    wire w;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected 'endgenerate', got 'endmodule'",
                            4, "27.3"));
}

TEST(ModuleItemsParsing, ErrorNetAliasMissingSemicolon) {
  auto r = Parse(
      "module m;\n"
      "  wire w1, w2;\n"
      "  alias w1 = w2\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got 'endmodule'", 4, "10.11"));
}

TEST(ModuleItemsParsing, ErrorTimeunitMissingSemicolon) {
  auto r = Parse(
      "module m;\n"
      "  timeunit 1ns\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got 'endmodule'", 3, "3.14.2.2"));
}

TEST(ModuleItemsParsing, ErrorNonModuleItemInBody) {
  auto r = Parse(
      "module m;\n"
      "  42;\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "unexpected token in module body", 2, "23.2.4"));
}

}  // namespace
