#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(CheckerItemsParsing, GenerateItemInChecker) {
  auto r = Parse(
      "checker my_chk;\n"
      "  if (W > 0)\n"
      "    wire a;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  bool found_if = false;
  for (auto* item : r.cu->checkers[0]->items) {
    if (item->kind == ModuleItemKind::kGenerateIf) found_if = true;
  }
  EXPECT_TRUE(found_if);
}

TEST(CheckerItemsParsing, CheckerWithPorts) {
  auto r = Parse(
      "checker my_chk(input clk, output logic valid);\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
}

TEST(CheckerItemsParsing, CheckerInitial) {
  auto r = Parse(
      "checker my_chk;\n"
      "  initial begin end\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kInitialBlock));
}

TEST(CheckerItemsParsing, CheckerAlways) {
  auto r = Parse(
      "checker my_chk;\n"
      "  always_ff @(posedge clk) begin end\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CheckerItemsParsing, CheckerFinal) {
  auto r = Parse(
      "checker my_chk;\n"
      "  final $display(\"done\");\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kFinalBlock));
}

TEST(CheckerItemsParsing, CheckerAssertion) {
  auto r = Parse(
      "checker my_chk;\n"
      "  assert property (@(posedge clk) req |-> ack);\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CheckerItemsParsing, CheckerContAssign) {
  auto r = Parse(
      "checker my_chk;\n"
      "  wire a, b;\n"
      "  assign a = b;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CheckerItemsParsing, CheckerRandDataDecl) {
  auto r = Parse(
      "checker my_chk;\n"
      "  rand logic [7:0] data;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CheckerItemsParsing, CheckerFuncDecl) {
  auto r = Parse(
      "checker my_chk;\n"
      "  function int add(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kFunctionDecl));
}

TEST(CheckerItemsParsing, CheckerNestedChecker) {
  auto r = Parse(
      "checker outer;\n"
      "  checker inner;\n"
      "  endchecker\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CheckerItemsParsing, CheckerGenvar) {
  auto r = Parse(
      "checker my_chk;\n"
      "  genvar i;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CheckerItemsParsing, CheckerClocking) {
  auto r = Parse(
      "checker my_chk;\n"
      "  clocking cb @(posedge clk);\n"
      "  endclocking\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CheckerItemsParsing, CheckerDefaultClocking) {
  auto r = Parse(
      "checker my_chk;\n"
      "  clocking cb @(posedge clk);\n"
      "  endclocking\n"
      "  default clocking cb;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CheckerItemsParsing, CheckerDefaultDisableIff) {
  auto r = Parse(
      "checker my_chk;\n"
      "  default disable iff rst;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CheckerItemsParsing, CheckerNullItem) {
  auto r = Parse(
      "checker my_chk;\n"
      "  ;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CheckerItemsParsing, CheckerGenFor) {
  auto r = Parse(
      "checker my_chk;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 4; i = i + 1) begin : gen\n"
      "    wire w;\n"
      "  end\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kGenerateFor));
}

TEST(CheckerItemsParsing, CheckerGenerateRegion) {
  auto r = Parse(
      "checker my_chk;\n"
      "  generate\n"
      "    wire w;\n"
      "  endgenerate\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CheckerItemsParsing, CheckerElabTask) {
  auto r = Parse(
      "checker my_chk;\n"
      "  $warning(\"check this\");\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CheckerItemsParsing, CheckerEndLabel) {
  auto r = Parse(
      "checker my_chk;\n"
      "endchecker : my_chk\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CheckerItemsParsing, CheckerInputPorts) {
  auto r = Parse(
      "checker port_check(input logic clk, input logic rst);\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_GE(r.cu->checkers[0]->ports.size(), 2u);
  EXPECT_EQ(r.cu->checkers[0]->ports[0].name, "clk");
  EXPECT_EQ(r.cu->checkers[0]->ports[0].direction, Direction::kInput);
  EXPECT_EQ(r.cu->checkers[0]->ports[1].name, "rst");
  EXPECT_EQ(r.cu->checkers[0]->ports[1].direction, Direction::kInput);
}

TEST(CheckerItemsParsing, CheckerOutputPorts) {
  auto r = Parse(
      "checker out_check(input logic clk, output logic valid);\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_GE(r.cu->checkers[0]->ports.size(), 2u);
  EXPECT_EQ(r.cu->checkers[0]->ports[1].name, "valid");
  EXPECT_EQ(r.cu->checkers[0]->ports[1].direction, Direction::kOutput);
}

TEST(CheckerItemsParsing, CheckerNoPorts) {
  auto r = Parse(
      "checker no_ports;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_TRUE(r.cu->checkers[0]->ports.empty());
}

TEST(CheckerItemsParsing, CheckerEmptyParenPorts) {
  auto r = Parse(
      "checker empty_parens();\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_TRUE(r.cu->checkers[0]->ports.empty());
}

TEST(CheckerItemsParsing, CheckerPropertyDecl) {
  auto r = Parse(
      "checker prop_check(input logic clk, input logic a, input logic b);\n"
      "  property p1;\n"
      "    a |-> b;\n"
      "  endproperty\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kPropertyDecl));
}

TEST(CheckerItemsParsing, CheckerSequenceDecl) {
  auto r = Parse(
      "checker seq_check(input logic clk, input logic a);\n"
      "  sequence s1;\n"
      "    a;\n"
      "  endsequence\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kSequenceDecl));
}

TEST(CheckerItemsParsing, CheckerAssertPropertyWithPorts) {
  auto r = Parse(
      "checker assert_check(input logic clk, input logic a, input logic b);\n"
      "  assert property (@(posedge clk) a |-> b);\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kAssertProperty));
}

TEST(CheckerItemsParsing, CheckerContAssignWithVars) {
  auto r = Parse(
      "checker assign_check;\n"
      "  logic a, b;\n"
      "  assign a = b;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kContAssign));
}

TEST(CheckerItemsParsing, CheckerFuncDeclAutomatic) {
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

TEST(CheckerItemsParsing, CheckerPortListDetailed) {
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

TEST(CheckerItemsParsing, CheckerPortDefaultValue) {
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

TEST(CheckerItemsParsing, CheckerContAssignItemKind) {
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

TEST(CheckerItemsParsing, CheckerInitialAlwaysFinal) {
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
  EXPECT_TRUE(HasItemKind(items, ModuleItemKind::kInitialBlock));
  EXPECT_TRUE(HasItemKind(items, ModuleItemKind::kAlwaysBlock));
  EXPECT_TRUE(HasItemKind(items, ModuleItemKind::kFinalBlock));
}

TEST(CheckerItemsParsing, CheckerAssertionItemKind) {
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

TEST(CheckerItemsParsing, CheckerNestedCheckerWithBody) {
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

TEST(CheckerItemsParsing, CheckerGenvarDeclItemKind) {
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

TEST(CheckerItemsParsing, CheckerGenerateItems) {
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
  EXPECT_TRUE(HasItemKind(items, ModuleItemKind::kGenerateFor));
  EXPECT_TRUE(HasItemKind(items, ModuleItemKind::kGenerateIf));
  EXPECT_TRUE(HasItemKind(items, ModuleItemKind::kElabSystemTask));
}

TEST(CheckerItemsParsing, CheckerMultipleItemTypes) {
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
  EXPECT_TRUE(HasItemKind(chk->items, ModuleItemKind::kVarDecl));
  EXPECT_TRUE(HasItemKind(chk->items, ModuleItemKind::kContAssign));
  EXPECT_TRUE(HasItemKind(chk->items, ModuleItemKind::kInitialBlock));
  EXPECT_TRUE(HasItemKind(chk->items, ModuleItemKind::kAlwaysBlock));
  EXPECT_TRUE(HasItemKind(chk->items, ModuleItemKind::kFinalBlock));
  EXPECT_TRUE(HasItemKind(chk->items, ModuleItemKind::kAssertProperty));
  EXPECT_TRUE(HasItemKind(chk->items, ModuleItemKind::kDefaultDisableIff));
  EXPECT_TRUE(HasItemKind(chk->items, ModuleItemKind::kFunctionDecl));
  EXPECT_TRUE(HasItemKind(chk->items, ModuleItemKind::kElabSystemTask));
}

TEST(CheckerItemsParsing, CheckerRandDataDeclItemKind) {
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

TEST(CheckerItemsParsing, CheckerOutputPortWithAssertion) {
  auto r = Parse(
      "checker mutex(logic [31:0] sig, event clock, output bit failure);\n"
      "  assert property (@clock $onehot0(sig))\n"
      "    failure = 1'b0; else failure = 1'b1;\n"
      "endchecker : mutex\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->name, "mutex");
  EXPECT_GE(r.cu->checkers[0]->ports.size(), 3u);
}

TEST(CheckerItemsParsing, CheckerNestedCheckerDeclaration) {
  auto r = Parse(
      "checker outer;\n"
      "  checker inner;\n"
      "  endchecker\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->name, "outer");
  EXPECT_FALSE(r.cu->checkers[0]->items.empty());
}

TEST(CheckerItemsParsing, CheckerAlwaysFF) {
  auto r = Parse(
      "checker check(logic a, b, c, clk, rst);\n"
      "  logic x, y, z;\n"
      "  assign x = a;\n"
      "  always_ff @(posedge clk or negedge rst) begin\n"
      "    a1: assert (b);\n"
      "    if (rst)\n"
      "      z <= b;\n"
      "    else z <= !c;\n"
      "  end\n"
      "endchecker : check\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->name, "check");
  EXPECT_FALSE(r.cu->checkers[0]->items.empty());
}

TEST(CheckerItemsParsing, CheckerDefaultClockingWithRand) {
  auto r = Parse(
      "checker clocked_check(bit clk);\n"
      "  default clocking @(posedge clk); endclocking\n"
      "  rand bit flag;\n"
      "  a1: assert property (flag == 1'b1);\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->name, "clocked_check");
  EXPECT_FALSE(r.cu->checkers[0]->items.empty());
}

TEST(CheckerItemsParsing, CheckerAlwaysBlock) {
  auto r = Parse(
      "checker always_check(input logic clk, input logic a);\n"
      "  always @(posedge clk)\n"
      "    assert(a);\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kAlwaysBlock));
}

TEST(CheckerItemsParsing, CheckerInitialBlock) {
  auto r = Parse(
      "checker init_check;\n"
      "  initial begin\n"
      "    $display(\"checker started\");\n"
      "  end\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kInitialBlock));
}

TEST(CheckerItemsParsing, CheckerInitialProcedure) {
  auto r = Parse(
      "checker init_check(input logic clk, input logic rst);\n"
      "  logic flag;\n"
      "  initial begin\n"
      "    flag = 0;\n"
      "  end\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->name, "init_check");
  EXPECT_FALSE(r.cu->checkers[0]->items.empty());
}

TEST(CheckerItemsParsing, CheckerAlwaysComb) {
  auto r = Parse(
      "checker comb_check(logic a, b);\n"
      "  logic v;\n"
      "  always_comb begin\n"
      "    if (a)\n"
      "      v = b;\n"
      "    else\n"
      "      v = !b;\n"
      "  end\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->name, "comb_check");
  EXPECT_FALSE(r.cu->checkers[0]->items.empty());
}

TEST(CheckerItemsParsing, CheckerFinalProcedure) {
  auto r = Parse(
      "checker final_check;\n"
      "  logic count;\n"
      "  final begin\n"
      "    $display(\"count = %%0d\", count);\n"
      "  end\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->name, "final_check");
  EXPECT_FALSE(r.cu->checkers[0]->items.empty());
}

TEST(CheckerItemsParsing, CheckerCovergroupAndClocking) {
  auto r = Parse(
      "checker my_check(logic clk, active);\n"
      "  bit active_d1 = 1'b0;\n"
      "  always_ff @(posedge clk) begin\n"
      "    active_d1 <= active;\n"
      "  end\n"
      "  covergroup cg_active @(posedge clk);\n"
      "    cp_active : coverpoint active\n"
      "    {\n"
      "      bins idle = { 1'b0 };\n"
      "      bins active = { 1'b1 };\n"
      "    }\n"
      "    option.per_instance = 1;\n"
      "  endgroup\n"
      "endchecker : my_check\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->name, "my_check");
  EXPECT_FALSE(r.cu->checkers[0]->items.empty());
}

TEST(CheckerItemsParsing, CheckerCovergroup) {
  auto r = Parse(
      "checker cov_check(input logic clk, input logic x);\n"
      "  covergroup cg @(posedge clk);\n"
      "    coverpoint x;\n"
      "  endgroup\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kCovergroupDecl));
}

TEST(CheckerItemsParsing, CheckerBitVector) {
  auto r = Parse(
      "checker bv_check;\n"
      "  logic [7:0] counter;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_FALSE(r.cu->checkers[0]->items.empty());
}

TEST(CheckerItemsParsing, CheckerRandVariable) {
  auto r = Parse(
      "checker observer_model(bit valid, reset);\n"
      "  default clocking @$global_clock; endclocking\n"
      "  rand bit flag;\n"
      "endchecker : observer_model\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->name, "observer_model");
  EXPECT_FALSE(r.cu->checkers[0]->items.empty());
}

TEST(CheckerItemsParsing, CheckerRandConstVariable) {
  auto r = Parse(
      "checker reason_about_one_bit(bit [63:0] data1, bit [63:0] data2,\n"
      "                              event clock);\n"
      "  rand const bit [5:0] idx;\n"
      "  a1: assert property (@clock data1[idx] == data2[idx]);\n"
      "endchecker : reason_about_one_bit\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->name, "reason_about_one_bit");
  EXPECT_FALSE(r.cu->checkers[0]->items.empty());
}

TEST(CheckerItemsParsing, CheckerWithVariables) {
  auto r = Parse(
      "checker var_check;\n"
      "  logic a, b;\n"
      "  assign a = b;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_FALSE(r.cu->checkers[0]->items.empty());
}

TEST(CheckerItemsParsing, CheckerAssumeProperty) {
  auto r = Parse(
      "checker observer_model(bit valid, reset);\n"
      "  default clocking @$global_clock; endclocking\n"
      "  rand bit flag;\n"
      "  m1: assume property (reset |=> !flag);\n"
      "  m2: assume property (!reset && flag |=> flag);\n"
      "  m3: assume property ($rising_gclk(flag) |-> valid);\n"
      "endchecker : observer_model\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->name, "observer_model");
  EXPECT_FALSE(r.cu->checkers[0]->items.empty());
}

TEST(CheckerItemsParsing, CheckerPortWithAttribute) {
  auto r = Parse(
      "checker chk((* mark *) input logic clk);\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_EQ(r.cu->checkers[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->ports[0].name, "clk");
  EXPECT_EQ(r.cu->checkers[0]->ports[0].direction, Direction::kInput);
}

TEST(CheckerItemsParsing, CheckerPortWithArrayDimension) {
  auto r = Parse(
      "checker chk(input logic data [3:0]);\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_EQ(r.cu->checkers[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->ports[0].name, "data");
  EXPECT_FALSE(r.cu->checkers[0]->ports[0].unpacked_dims.empty());
}

TEST(CheckerItemsParsing, CheckerPortImplicitDirection) {
  auto r = Parse(
      "checker chk(logic sig);\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_EQ(r.cu->checkers[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->ports[0].name, "sig");
}

TEST(CheckerItemsParsing, CheckerCoverPropertyItem) {
  auto r = Parse(
      "checker chk;\n"
      "  cover property (@(posedge clk) a ##1 b);\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kCoverProperty));
}

TEST(CheckerItemsParsing, CheckerCoverSequenceItem) {
  auto r = Parse(
      "checker chk;\n"
      "  cover sequence (@(posedge clk) a ##1 b);\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kCoverSequence));
}

TEST(CheckerItemsParsing, CheckerRestrictPropertyItem) {
  auto r = Parse(
      "checker chk;\n"
      "  restrict property (@(posedge clk) a |-> b);\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_TRUE(HasItemOfKind(r.cu->checkers[0]->items,
                            ModuleItemKind::kRestrictProperty));
}

TEST(CheckerItemsParsing, CheckerCaseGenerate) {
  auto r = Parse(
      "checker chk;\n"
      "  case (MODE)\n"
      "    0: wire a;\n"
      "    1: wire b;\n"
      "    default: wire c;\n"
      "  endcase\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kGenerateCase));
}

TEST(CheckerItemsParsing, CheckerElabTaskErrorSeverity) {
  auto r = Parse(
      "checker chk;\n"
      "  $error(\"something wrong\");\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kElabSystemTask));
}

TEST(CheckerItemsParsing, CheckerElabTaskFatalSeverity) {
  auto r = Parse(
      "checker chk;\n"
      "  $fatal(1, \"fatal error\");\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kElabSystemTask));
}

TEST(CheckerItemsParsing, CheckerAlwaysLatch) {
  auto r = Parse(
      "checker chk;\n"
      "  always_latch\n"
      "    if (en) q <= d;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_TRUE(HasItemOfKind(r.cu->checkers[0]->items,
                            ModuleItemKind::kAlwaysLatchBlock));
}

TEST(CheckerItemsParsing, CheckerMultipleNullItems) {
  auto r = Parse(
      "checker chk;\n"
      "  ;\n"
      "  ;\n"
      "  ;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
}

}  // namespace
