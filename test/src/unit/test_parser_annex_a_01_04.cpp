#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(ModuleItemsA14, ElabFatalTask) {
  auto r = Parse(
      "module m;\n"
      "  $fatal(1, \"error message\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kElabSystemTask));
}

TEST(ModuleItemsA14, ElabErrorTask) {
  auto r = Parse(
      "module m;\n"
      "  $error(\"something wrong\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ModuleItemsA14, ElabWarningTask) {
  auto r = Parse(
      "module m;\n"
      "  $warning;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ModuleItemsA14, ElabInfoTask) {
  auto r = Parse(
      "module m;\n"
      "  $info(\"build info\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ModuleItemsA14, ContinuousAssign) {
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

TEST(ModuleItemsA14, NetAlias) {
  auto r = Parse(
      "module m;\n"
      "  wire a, b;\n"
      "  alias a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kAlias));
}

TEST(ModuleItemsA14, InitialConstruct) {
  auto r = Parse(
      "module m;\n"
      "  initial begin end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kInitialBlock));
}

TEST(ModuleItemsA14, FinalConstruct) {
  auto r = Parse(
      "module m;\n"
      "  final begin end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kFinalBlock));
}

TEST(ModuleItemsA14, AlwaysConstructPlain) {
  auto r = Parse(
      "module m;\n"
      "  always @(posedge clk) begin end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasAlwaysOfKind(r.cu->modules[0]->items, AlwaysKind::kAlways));
}

TEST(ModuleItemsA14, AlwaysComb) {
  auto r = Parse(
      "module m;\n"
      "  always_comb begin end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasAlwaysOfKind(r.cu->modules[0]->items, AlwaysKind::kAlwaysComb));
}

TEST(ModuleItemsA14, AlwaysFF) {
  auto r = Parse(
      "module m;\n"
      "  always_ff @(posedge clk) begin end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasAlwaysOfKind(r.cu->modules[0]->items, AlwaysKind::kAlwaysFF));
}

TEST(ModuleItemsA14, AlwaysLatch) {
  auto r = Parse(
      "module m;\n"
      "  always_latch begin end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasAlwaysOfKind(r.cu->modules[0]->items, AlwaysKind::kAlwaysLatch));
}

TEST(ModuleItemsA14, LoopGenerateConstruct) {
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

TEST(ModuleItemsA14, ConditionalGenerateIf) {
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

TEST(ModuleItemsA14, ConditionalGenerateCase) {
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

TEST(ModuleItemsA14, ParameterOverride) {
  auto r = Parse(
      "module m;\n"
      "  defparam u1.W = 16;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kDefparam));
}

TEST(ModuleItemsA14, GateInstantiation) {
  auto r = Parse(
      "module m;\n"
      "  and g1(y, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kGateInst));
}

TEST(ModuleItemsA14, ModuleInstantiation) {
  auto r = Parse(
      "module m;\n"
      "  sub u1(.a(x), .b(y));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kModuleInst));
}

TEST(ModuleItemsA14, ClockingDeclaration) {
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

TEST(ModuleItemsA14, DefaultClocking) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "  endclocking\n"
      "  default clocking cb;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ModuleItemsA14, DefaultDisableIff) {
  auto r = Parse(
      "module m;\n"
      "  default disable iff rst;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(r.cu->modules[0]->items,
                            ModuleItemKind::kDefaultDisableIff));
}

TEST(ModuleItemsA14, GenerateRegion) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "    wire w;\n"
      "  endgenerate\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ModuleItemsA14, SpecifyBlock) {
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

TEST(ModuleItemsA14, SpecparamDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  specparam delay = 10;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kSpecparam));
}

TEST(ModuleItemsA14, NestedModuleDecl) {
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

TEST(ModuleItemsA14, NestedInterfaceDecl) {
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

TEST(ModuleItemsA14, NestedProgramDecl) {
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

TEST(ModuleItemsA14, TimeunitsInModule) {
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

TEST(ModuleItemsA14, PortDeclAsModuleItem) {
  auto r = Parse(
      "module m(a, b, y);\n"
      "  input a, b;\n"
      "  output y;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ModuleItemsA14, BindDirectiveInModule) {
  auto r = Parse(
      "module target; endmodule\n"
      "module checker_m; endmodule\n"
      "module m;\n"
      "  bind target checker_m inst(.*);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ModuleItemsA14, AssertionItem) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a |-> b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kAssertProperty));
}

TEST(ModuleItemsA14, InterfaceInstantiation) {
  auto r = Parse(
      "module m;\n"
      "  bus_if bus_inst(.clk(clk));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kModuleInst));
}

TEST(ModuleItemsA14, ItemWithAttributes) {
  auto r = Parse(
      "module m;\n"
      "  (* full_case *) wire w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ModuleItemsA14, GenvarDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  genvar i, j;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}
