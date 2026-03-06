#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §A.1.8 Checker items

TEST(ParserAnnexA042, GenerateItemInChecker) {
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

// checker_port_list ::= checker_port_item { , checker_port_item }
TEST(CheckerItemsA18, CheckerWithPorts) {
  auto r = Parse(
      "checker my_chk(input clk, output logic valid);\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
}

// checker_or_generate_item ::= initial_construct
TEST(CheckerItemsA18, CheckerInitial) {
  auto r = Parse(
      "checker my_chk;\n"
      "  initial begin end\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(r.cu->checkers[0]->items,
                            ModuleItemKind::kInitialBlock));
}

// checker_or_generate_item ::= always_construct
TEST(CheckerItemsA18, CheckerAlways) {
  auto r = Parse(
      "checker my_chk;\n"
      "  always_ff @(posedge clk) begin end\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// checker_or_generate_item ::= final_construct
TEST(CheckerItemsA18, CheckerFinal) {
  auto r = Parse(
      "checker my_chk;\n"
      "  final $display(\"done\");\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(r.cu->checkers[0]->items,
                            ModuleItemKind::kFinalBlock));
}

// checker_or_generate_item ::= assertion_item
TEST(CheckerItemsA18, CheckerAssertion) {
  auto r = Parse(
      "checker my_chk;\n"
      "  assert property (@(posedge clk) req |-> ack);\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// checker_or_generate_item ::= continuous_assign
TEST(CheckerItemsA18, CheckerContAssign) {
  auto r = Parse(
      "checker my_chk;\n"
      "  wire a, b;\n"
      "  assign a = b;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// checker_or_generate_item_declaration ::= [rand] data_declaration
TEST(CheckerItemsA18, CheckerRandDataDecl) {
  auto r = Parse(
      "checker my_chk;\n"
      "  rand logic [7:0] data;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// checker_or_generate_item_declaration ::= function_declaration
TEST(CheckerItemsA18, CheckerFuncDecl) {
  auto r = Parse(
      "checker my_chk;\n"
      "  function int add(int a, int b);\n"
      "    return a + b;\n"
      "  endfunction\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(r.cu->checkers[0]->items,
                            ModuleItemKind::kFunctionDecl));
}

// checker_or_generate_item_declaration ::= checker_declaration (nested)
TEST(CheckerItemsA18, CheckerNestedChecker) {
  auto r = Parse(
      "checker outer;\n"
      "  checker inner;\n"
      "  endchecker\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// checker_or_generate_item_declaration ::= genvar_declaration
TEST(CheckerItemsA18, CheckerGenvar) {
  auto r = Parse(
      "checker my_chk;\n"
      "  genvar i;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// checker_or_generate_item_declaration ::= clocking_declaration
TEST(CheckerItemsA18, CheckerClocking) {
  auto r = Parse(
      "checker my_chk;\n"
      "  clocking cb @(posedge clk);\n"
      "  endclocking\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// checker_or_generate_item_declaration ::= default clocking id ;
TEST(CheckerItemsA18, CheckerDefaultClocking) {
  auto r = Parse(
      "checker my_chk;\n"
      "  clocking cb @(posedge clk);\n"
      "  endclocking\n"
      "  default clocking cb;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// checker_or_generate_item_declaration ::= default disable iff expr ;
TEST(CheckerItemsA18, CheckerDefaultDisableIff) {
  auto r = Parse(
      "checker my_chk;\n"
      "  default disable iff rst;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// checker_or_generate_item_declaration ::= ;
TEST(CheckerItemsA18, CheckerNullItem) {
  auto r = Parse(
      "checker my_chk;\n"
      "  ;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// checker_generate_item ::= loop_generate_construct
TEST(CheckerItemsA18, CheckerGenFor) {
  auto r = Parse(
      "checker my_chk;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 4; i = i + 1) begin : gen\n"
      "    wire w;\n"
      "  end\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(HasItemOfKind(r.cu->checkers[0]->items,
                            ModuleItemKind::kGenerateFor));
}

// checker_generate_item ::= generate_region
TEST(CheckerItemsA18, CheckerGenerateRegion) {
  auto r = Parse(
      "checker my_chk;\n"
      "  generate\n"
      "    wire w;\n"
      "  endgenerate\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// checker_generate_item ::= elaboration_severity_system_task
TEST(CheckerItemsA18, CheckerElabTask) {
  auto r = Parse(
      "checker my_chk;\n"
      "  $warning(\"check this\");\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// checker with end label
TEST(CheckerItemsA18, CheckerEndLabel) {
  auto r = Parse(
      "checker my_chk;\n"
      "endchecker : my_chk\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
