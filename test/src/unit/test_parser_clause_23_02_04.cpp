#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ModuleItemsParsing, ModuleDefinitionWithBody) {
  auto r = Parse(
      "module m;\n"
      "  wire a;\n"
      "  assign a = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  EXPECT_EQ(mod->name, "m");
  ASSERT_GE(mod->items.size(), 2);
}

TEST(ModuleItemsParsing, EmptyModuleBody) {
  auto r = Parse("module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(r.cu->modules[0]->items.empty());
}

TEST(ModuleItemsParsing, MultipleItemKinds) {
  auto r = Parse(
      "module m;\n"
      "  wire a;\n"
      "  assign a = 1;\n"
      "  initial begin end\n"
      "  always_comb begin end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_GE(r.cu->modules[0]->items.size(), 4u);
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

TEST(ModuleItemsParsing, AlwaysComb) {
  auto r = Parse(
      "module m;\n"
      "  always_comb begin end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasAlwaysOfKind(r.cu->modules[0]->items, AlwaysKind::kAlwaysComb));
}

TEST(ModuleItemsParsing, AlwaysFF) {
  auto r = Parse(
      "module m;\n"
      "  always_ff @(posedge clk) begin end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasAlwaysOfKind(r.cu->modules[0]->items, AlwaysKind::kAlwaysFF));
}

TEST(ModuleItemsParsing, AlwaysLatch) {
  auto r = Parse(
      "module m;\n"
      "  always_latch begin end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasAlwaysOfKind(r.cu->modules[0]->items, AlwaysKind::kAlwaysLatch));
}

TEST(ModuleItemsParsing, AllAlwaysVariants) {
  auto r = Parse(
      "module m;\n"
      "  always @(*) begin end\n"
      "  always_comb begin end\n"
      "  always_ff @(posedge clk) begin end\n"
      "  always_latch begin end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasAlwaysOfKind(r.cu->modules[0]->items, AlwaysKind::kAlways));
  EXPECT_TRUE(
      HasAlwaysOfKind(r.cu->modules[0]->items, AlwaysKind::kAlwaysComb));
  EXPECT_TRUE(HasAlwaysOfKind(r.cu->modules[0]->items, AlwaysKind::kAlwaysFF));
  EXPECT_TRUE(
      HasAlwaysOfKind(r.cu->modules[0]->items, AlwaysKind::kAlwaysLatch));
}

TEST(ModuleItemsParsing, MixedProcedureTypes) {
  auto r = Parse(
      "module m;\n"
      "  initial a = 0;\n"
      "  always @(posedge clk) q <= d;\n"
      "  final $display(\"done\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kInitialBlock));
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kAlwaysBlock));
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kFinalBlock));
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

TEST(ModuleItemsParsing, ConditionalGenerateCase) {
  auto r = Parse(
      "module m;\n"
      "  case (1)\n"
      "    0: wire a;\n"
      "    1: wire b;\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kGenerateCase));
}

TEST(ModuleItemsParsing, GenerateIfElse) {
  auto r = Parse(
      "module m;\n"
      "  if (1) begin : yes\n"
      "    wire a;\n"
      "  end else begin : no\n"
      "    wire b;\n"
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

TEST(ModuleItemsParsing, NestedModuleDecl) {
  auto r = Parse(
      "module outer;\n"
      "  module inner;\n"
      "  endmodule\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(r.cu->modules[0]->items,
                            ModuleItemKind::kNestedModuleDecl));
}

TEST(ModuleItemsParsing, NestedInterfaceDecl) {
  auto r = Parse(
      "module outer;\n"
      "  interface inner_ifc;\n"
      "  endinterface\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(r.cu->modules[0]->items,
                            ModuleItemKind::kNestedModuleDecl));
}

TEST(ModuleItemsParsing, NestedProgramDecl) {
  auto r = Parse(
      "module outer;\n"
      "  program inner_prg;\n"
      "  endprogram\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(r.cu->modules[0]->items,
                            ModuleItemKind::kNestedModuleDecl));
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

TEST(ModuleItemsParsing, BindDirectiveInModule) {
  auto r = Parse(
      "module target; endmodule\n"
      "module checker_m; endmodule\n"
      "module m;\n"
      "  bind target checker_m inst(.*);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
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

TEST(ModuleItemsParsing, ItemWithAttributes) {
  auto r = Parse(
      "module m;\n"
      "  (* full_case *) wire w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ModuleItemsParsing, GenvarDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  genvar i, j;\n"
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

TEST(ModuleItemsParsing, ElabErrorTask) {
  auto r = Parse(
      "module m;\n"
      "  $error(\"something wrong\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ModuleItemsParsing, ElabWarningTask) {
  auto r = Parse(
      "module m;\n"
      "  $warning;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ModuleItemsParsing, ElabInfoTask) {
  auto r = Parse(
      "module m;\n"
      "  $info(\"build info\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
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

TEST(ParameterOverride, ListOfDefparamAssignmentsThree) {
  auto r = Parse(
      "module top;\n"
      "  defparam u0.A = 1, u0.B = 2, u0.C = 3;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->defparam_assigns.size(), 3u);
}

TEST(ParameterOverride, DefparamSingleAssignment) {
  auto r = Parse(
      "module m;\n"
      "  defparam u.WIDTH = 32;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kDefparam);
  EXPECT_EQ(item->defparam_assigns.size(), 1u);
}

TEST(ModuleItemsParsing, ErrorDefparamMissingSemicolon) {
  auto r = Parse(
      "module m;\n"
      "  defparam u.W = 16\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ModuleItemsParsing, ErrorUnclosedGenerateRegion) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "    wire w;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ModuleItemsParsing, NetAlias) {
  auto r = Parse(
      "module m;\n"
      "  wire w1, w2;\n"
      "  alias w1 = w2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kAlias));
}

TEST(ModuleItemsParsing, NetAliasThreeNets) {
  auto r = Parse(
      "module m;\n"
      "  wire w1, w2, w3;\n"
      "  alias w1 = w2 = w3;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAlias);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->alias_nets.size(), 3u);
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
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kUdpInst));
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

TEST(ModuleItemsParsing, TimeprecisionAsModuleItem) {
  auto r = Parse(
      "module m;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->has_timeprecision);
}

TEST(ModuleItemsParsing, TimeunitWithPrecisionAsModuleItem) {
  auto r = Parse(
      "module m;\n"
      "  timeunit 1ns / 1ps;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->has_timeunit);
  EXPECT_TRUE(r.cu->modules[0]->has_timeprecision);
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

TEST(ModuleItemsParsing, AssumePropertyInModule) {
  auto r = Parse(
      "module m;\n"
      "  assume property (@(posedge clk) a |-> b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kAssumeProperty));
}

TEST(ModuleItemsParsing, CoverPropertyInModule) {
  auto r = Parse(
      "module m;\n"
      "  cover property (@(posedge clk) a |-> b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kCoverProperty));
}

TEST(ModuleItemsParsing, RestrictPropertyInModule) {
  auto r = Parse(
      "module m;\n"
      "  restrict property (@(posedge clk) a |-> b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(r.cu->modules[0]->items,
                            ModuleItemKind::kRestrictProperty));
}

TEST(ModuleItemsParsing, CoverSequenceInModule) {
  auto r = Parse(
      "module m;\n"
      "  cover sequence (@(posedge clk) a ##1 b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kCoverSequence));
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

TEST(ModuleItemsParsing, TimeprecisionRepeatMatches) {
  auto r = Parse(
      "module m;\n"
      "  timeprecision 1ps;\n"
      "  wire w;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ModuleItemsParsing, TimeunitBothHeaderRepeatMatches) {
  auto r = Parse(
      "module m;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
      "  wire w;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ps;\n"
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
  EXPECT_TRUE(r.has_errors);
}

TEST(ModuleItemsParsing, ErrorTimeprecisionNoPriorDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  wire w;\n"
      "  timeprecision 1ps;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ModuleItemsParsing, ErrorTimeunitMismatch) {
  auto r = Parse(
      "module m;\n"
      "  timeunit 1ns;\n"
      "  wire w;\n"
      "  timeunit 1us;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ModuleItemsParsing, ErrorTimeprecisionMismatch) {
  auto r = Parse(
      "module m;\n"
      "  timeprecision 1ps;\n"
      "  wire w;\n"
      "  timeprecision 1ns;\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ModuleItemsParsing, ErrorNetAliasMissingSemicolon) {
  auto r = Parse(
      "module m;\n"
      "  wire w1, w2;\n"
      "  alias w1 = w2\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ModuleItemsParsing, ErrorTimeunitMissingSemicolon) {
  auto r = Parse(
      "module m;\n"
      "  timeunit 1ns\n"
      "endmodule\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
