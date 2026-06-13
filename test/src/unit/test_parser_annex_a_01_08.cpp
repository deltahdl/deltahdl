#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// -----------------------------------------------------------------------------
// checker_port_list / checker_port_item / checker_port_direction (prods 1-3)
// -----------------------------------------------------------------------------

// checker_port_list ::= checker_port_item { , checker_port_item }, with an
// explicit input and output checker_port_direction observed on the items.
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

// checker_port_item ::= { attribute_instance } ... — the optional attribute
// prefix on a port.
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

// checker_port_item ::= ... formal_port_identifier { variable_dimension } ...
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

// checker_port_item ::= ... [ = property_actual_arg ] — the optional default.
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

// checker_port_item ::= ... [ checker_port_direction ] ... — direction omitted
// (§17.2 infers the first formal as input).
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

// -----------------------------------------------------------------------------
// checker_or_generate_item (prod 4):
//   ... | initial_construct | always_construct | final_construct
//       | assertion_item | continuous_assign | ...
// -----------------------------------------------------------------------------

// initial_construct, always_construct and final_construct as checker items.
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

// assertion_item as a checker item.
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

// continuous_assign as a checker item.
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

// -----------------------------------------------------------------------------
// checker_or_generate_item_declaration (prod 5):
//   [ rand ] data_declaration | function_declaration | checker_declaration
//   | assertion_item_declaration | covergroup_declaration | genvar_declaration
//   | clocking_declaration | default clocking ... ; | default disable iff ... ;
//   | ;
// -----------------------------------------------------------------------------

// [ rand ] data_declaration — both the rand-prefixed and plain branches.
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

// function_declaration as a checker item.
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

// checker_declaration nested inside a checker.
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

// assertion_item_declaration as a checker item (the property_declaration /
// sequence_declaration / let_declaration split belongs to §A.2.10; §A.1.8 only
// requires that one such declaration is accepted as a checker item).
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

// covergroup_declaration as a checker item.
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

// genvar_declaration as a checker item.
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

// clocking_declaration as a checker item.
TEST(CheckerItemsParsing, CheckerClocking) {
  auto r = Parse(
      "checker my_chk;\n"
      "  clocking cb @(posedge clk);\n"
      "  endclocking\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// default clocking clocking_identifier ;
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

// default disable iff expression_or_dist ;
TEST(CheckerItemsParsing, CheckerDefaultDisableIff) {
  auto r = Parse(
      "checker my_chk;\n"
      "  default disable iff rst;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// the empty ; declaration.
TEST(CheckerItemsParsing, CheckerNullItem) {
  auto r = Parse(
      "checker my_chk;\n"
      "  ;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// -----------------------------------------------------------------------------
// checker_generate_item (prod 6):
//   loop_generate_construct | conditional_generate_construct
//   | generate_region | elaboration_severity_system_task
// -----------------------------------------------------------------------------

// loop_generate_construct.
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

// conditional_generate_construct — if form.
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

// conditional_generate_construct — case form.
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

// generate_region.
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

// elaboration_severity_system_task.
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

// -----------------------------------------------------------------------------
// Integration: a single checker exercising a broad mix of checker_or_generate
// items together.
// -----------------------------------------------------------------------------

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

// -----------------------------------------------------------------------------
// Error conditions and edge cases for §A.1.8 productions.
// -----------------------------------------------------------------------------

// Edge: checker_port_list ::= checker_port_item { , checker_port_item } with a
// trailing item whose [checker_port_direction] is omitted (prod 2). The second
// port inherits the direction and type of the preceding checker_port_item.
TEST(CheckerItemsParsing, CheckerPortListInheritedDirection) {
  auto r = Parse(
      "checker chk(input logic a, b);\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_EQ(r.cu->checkers[0]->ports.size(), 2u);
  EXPECT_EQ(r.cu->checkers[0]->ports[0].name, "a");
  EXPECT_EQ(r.cu->checkers[0]->ports[0].direction, Direction::kInput);
  EXPECT_EQ(r.cu->checkers[0]->ports[1].name, "b");
  EXPECT_EQ(r.cu->checkers[0]->ports[1].direction, Direction::kInput);
}

// Error: checker_port_item requires a formal_port_identifier (prod 2); a port
// that supplies only a type is rejected.
TEST(CheckerItemsParsing, CheckerPortMissingIdentifierRejected) {
  auto r = Parse(
      "checker chk(input logic);\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.has_errors);
}

// Error: the `default disable iff expression_or_dist ;` alternative of
// checker_or_generate_item_declaration (prod 5) requires its trailing ';'.
TEST(CheckerItemsParsing, CheckerDefaultDisableIffMissingSemicolonRejected) {
  auto r = Parse(
      "checker chk;\n"
      "  default disable iff rst\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
