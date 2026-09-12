#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"

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
  // A checker port list is read by Parser::ParsePortDecl, which files the
  // missing port identifier under §23.2.2.2 with the ANSI module port it
  // shares rather than under §17.2 with the checker.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected identifier, got ')'", 1, "23.2.2.2"));
}

// Error: the `default disable iff expression_or_dist ;` alternative of
// checker_or_generate_item_declaration (prod 5) requires its trailing ';'.
TEST(CheckerItemsParsing, CheckerDefaultDisableIffMissingSemicolonRejected) {
  auto r = Parse(
      "checker chk;\n"
      "  default disable iff rst\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  // §16.15 owns `default disable iff`, so its trailing ';' is reported there.
  // `endchecker` stands where that ';' must be, on line 3.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected ';', got 'endchecker'", 3, "16.15"));
}

// checker_or_generate_item admits no specify_block or specparam_declaration:
// A.1.4's non_port_module_item lists both, and A.1.8 lists neither, §30.3
// having the specify block "defined within a module" and §6.20.5 a specparam
// "declared inside a module or specify block". Each was accepted in a checker
// body silently and recorded as an item of it.

TEST(CheckerItemsParsing, CheckerSpecifyBlockRejected) {
  auto r = Parse(
      "checker c;\n"
      "  specify\n"
      "    (a => b) = 5;\n"
      "  endspecify\n"
      "  initial x = 0;\n"
      "endchecker\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "specify block must appear inside a module declaration", 2,
      "30.3"));
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kInitialBlock));
}

TEST(CheckerItemsParsing, CheckerSpecparamRejected) {
  auto r = Parse(
      "checker c;\n"
      "  specparam tRise = 150;\n"
      "endchecker\n");
  EXPECT_TRUE(ReportedError(
      r.diags,
      "specparam declaration must appear inside a module or a specify block", 2,
      "6.20.5"));
}

// -----------------------------------------------------------------------------
// checker_port_item's property_formal_type, which A.2.10 spells
// `sequence_formal_type | property` with `sequence_formal_type ::=
// data_type_or_implicit | sequence | untyped`. The port list read the data
// type alone, so a formal of one of the three keyword types was reported as a
// missing identifier.
// -----------------------------------------------------------------------------

// §17.9 Example 1's port list (printed page 520), typedef included, since the
// last formal's type is the enum it declares.
TEST(CheckerItemsParsing, CheckerPortListOfComplexCheckerExample) {
  auto r = Parse(
      "typedef enum { cover_none, cover_all } coverage_level;\n"
      "checker assert_window1 (\n"
      "  logic test_expr,\n"
      "  untyped start_event,\n"
      "  untyped end_event,\n"
      "  event clock = $inferred_clock,\n"
      "  logic reset = $inferred_disable,\n"
      "  string error_msg = \"violation\",\n"
      "  coverage_level clevel = cover_all\n"
      ");\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  const auto& ports = r.cu->checkers[0]->ports;
  ASSERT_EQ(ports.size(), 7u);
  EXPECT_EQ(ports[0].formal_type, PropertyFormalType::kData);
  EXPECT_EQ(ports[0].data_type.kind, DataTypeKind::kLogic);
  EXPECT_EQ(ports[1].name, "start_event");
  EXPECT_EQ(ports[1].formal_type, PropertyFormalType::kUntyped);
  EXPECT_EQ(ports[1].direction, Direction::kInput);
  EXPECT_EQ(ports[2].formal_type, PropertyFormalType::kUntyped);
  EXPECT_EQ(ports[3].data_type.kind, DataTypeKind::kEvent);
  EXPECT_NE(ports[3].default_value, nullptr);
  EXPECT_EQ(ports[6].name, "clevel");
  EXPECT_EQ(ports[6].data_type.kind, DataTypeKind::kNamed);
  EXPECT_NE(ports[6].default_value, nullptr);
}

// The `sequence` and `property` forms beside `untyped`, each an input.
TEST(CheckerItemsParsing, CheckerPortSequenceAndPropertyFormals) {
  auto r = Parse(
      "checker chk(sequence s, property p, untyped u, input logic x);\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  const auto& ports = r.cu->checkers[0]->ports;
  ASSERT_EQ(ports.size(), 4u);
  EXPECT_EQ(ports[0].formal_type, PropertyFormalType::kSequence);
  EXPECT_EQ(ports[0].direction, Direction::kInput);
  EXPECT_EQ(ports[1].formal_type, PropertyFormalType::kProperty);
  EXPECT_EQ(ports[1].direction, Direction::kInput);
  EXPECT_EQ(ports[2].formal_type, PropertyFormalType::kUntyped);
  EXPECT_EQ(ports[3].formal_type, PropertyFormalType::kData);
  EXPECT_EQ(ports[3].data_type.kind, DataTypeKind::kLogic);
}

// A formal written as a bare identifier after a keyword-typed one takes that
// type, as §17.2 has it take "the type of the previous formal argument".
TEST(CheckerItemsParsing, CheckerPortKeywordTypeInheritedByBareFormal) {
  auto r = Parse(
      "checker chk(sequence s, t);\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_EQ(r.cu->checkers[0]->ports.size(), 2u);
  EXPECT_EQ(r.cu->checkers[0]->ports[1].name, "t");
  EXPECT_EQ(r.cu->checkers[0]->ports[1].formal_type,
            PropertyFormalType::kSequence);
}

// checker_port_list is checker_port_item alone: a formal with its type
// omitted followed by a typed one is two checker_port_items, not A.1.3's
// list_of_ports, which the parser took `a ,` for and then had no port form for
// `logic b`.
TEST(CheckerItemsParsing, CheckerPortListIsNotANonAnsiList) {
  auto r = Parse(
      "checker chk(a, logic b);\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_FALSE(r.cu->checkers[0]->is_non_ansi_ports);
  ASSERT_EQ(r.cu->checkers[0]->ports.size(), 2u);
  EXPECT_EQ(r.cu->checkers[0]->ports[0].name, "a");
  EXPECT_EQ(r.cu->checkers[0]->ports[0].formal_type,
            PropertyFormalType::kUntyped);
  EXPECT_EQ(r.cu->checkers[0]->ports[1].name, "b");
  EXPECT_EQ(r.cu->checkers[0]->ports[1].data_type.kind, DataTypeKind::kLogic);
}

// checker_port_item names its formal with a formal_port_identifier alone;
// the `. port_identifier ( [ expression ] )` form is A.1.3's
// ansi_port_declaration, and was accepted here as a non-ANSI list.
TEST(CheckerItemsParsing, CheckerPortExplicitNamedFormRejected) {
  auto r = Parse(
      "checker chk(.a(x));\n"
      "endchecker\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "checker formal 'a' is named by an identifier "
                            "alone",
                            1, "A.1.8"));
}

// -----------------------------------------------------------------------------
// checker_or_generate_item admits what it lists and nothing A.1.4's module
// body reaches beyond it. Each item below was accepted in a checker body
// silently and recorded as an item of it; each is now reported under A.1.8 at
// its keyword and still read, so that the body resumes after it.
// -----------------------------------------------------------------------------

// checker_or_generate_item_declaration has function_declaration and no
// task_declaration.
TEST(CheckerItemsParsing, CheckerTaskDeclarationRejected) {
  auto r = Parse(
      "checker c;\n"
      "  task t();\n"
      "  endtask\n"
      "  initial x = 0;\n"
      "endchecker\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a task declaration is not an item of a checker", 2, "A.1.8"));
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kInitialBlock));
}

// A class_declaration is A.1.11's package_or_generate_item_declaration's, and
// no checker item.
TEST(CheckerItemsParsing, CheckerClassDeclarationRejected) {
  auto r = Parse(
      "checker c;\n"
      "  class k;\n"
      "  endclass\n"
      "endchecker\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a class declaration is not an item of a checker", 2, "A.1.8"));
}

// Neither parameter_declaration nor local_parameter_declaration is a checker
// item, and A.1.2's checker_declaration carries no parameter_port_list: the
// elaboration-time constants a checker takes are formal arguments, as §17.9's
// `coverage_level clevel = cover_all` has it.
TEST(CheckerItemsParsing, CheckerParameterDeclarationRejected) {
  auto r = Parse(
      "checker c;\n"
      "  localparam int W = 4;\n"
      "  parameter int D = 2;\n"
      "endchecker\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "a parameter declaration is not an item of a "
                            "checker",
                            2, "A.1.8"));
  EXPECT_TRUE(ReportedError(r.diags,
                            "a parameter declaration is not an item of a "
                            "checker",
                            3, "A.1.8"));
}

// parameter_override is A.1.4's module_or_generate_item's.
TEST(CheckerItemsParsing, CheckerDefparamRejected) {
  auto r = Parse(
      "checker c;\n"
      "  defparam u.p = 1;\n"
      "endchecker\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a defparam statement is not an item of a checker", 2, "A.1.8"));
}

// net_alias is A.1.4's module_common_item's.
TEST(CheckerItemsParsing, CheckerNetAliasRejected) {
  auto r = Parse(
      "checker c;\n"
      "  alias a = b;\n"
      "endchecker\n");
  EXPECT_TRUE(ReportedError(r.diags, "a net alias is not an item of a checker",
                            2, "A.1.8"));
}

// bind_directive is A.1.4's module_or_generate_item's.
TEST(CheckerItemsParsing, CheckerBindDirectiveRejected) {
  auto r = Parse(
      "checker c;\n"
      "  bind m chk u();\n"
      "endchecker\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a bind directive is not an item of a checker", 2, "A.1.8"));
}

// timeunits_declaration is an item of a module, an interface, a program and
// a package, the scopes §3.14.2.2 gives a time scope, and of no checker.
TEST(CheckerItemsParsing, CheckerTimeunitRejected) {
  auto r = Parse(
      "checker c;\n"
      "  timeunit 1ns;\n"
      "endchecker\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "a timeunit or timeprecision declaration is not "
                            "an item of a checker",
                            2, "A.1.8"));
}

// gate_instantiation is A.1.4's module_or_generate_item's.
TEST(CheckerItemsParsing, CheckerGateInstantiationRejected) {
  auto r = Parse(
      "checker c;\n"
      "  and g(o, a, b);\n"
      "endchecker\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a gate instantiation is not an item of a checker", 2, "A.1.8"));
}

// A.1.4's module_item opens with `port_declaration ;` and checker_or_generate
// _item does not: a checker's formals are its checker_port_list. The
// declaration was reported as an unexpected token of a module body, under
// §23.2.4.
TEST(CheckerItemsParsing, CheckerBodyPortDeclarationRejected) {
  auto r = Parse(
      "checker c;\n"
      "  input clk;\n"
      "  initial x = 0;\n"
      "endchecker\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a port declaration is not an item of a checker", 2, "A.1.8"));
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kInitialBlock));
}

// §17.2: "modules, interfaces, programs, and packages shall not be declared
// inside checkers". The first three are items the elaborator reports; a
// package is no item of any body, and was reported as an unexpected token of
// a module body, under §23.2.4, with the package's own items then read as
// the checker's.
TEST(CheckerItemsParsing, CheckerPackageDeclarationRejected) {
  auto r = Parse(
      "checker c;\n"
      "  package p;\n"
      "    int q;\n"
      "  endpackage\n"
      "  initial x = 0;\n"
      "endchecker\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a package cannot be declared inside checker 'c'", 2, "17.2"));
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_FALSE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kVarDecl));
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kInitialBlock));
}

// Footnote 6 to checker_generate_item: "it shall be illegal for a
// checker_generate_item to include any item that would be illegal in a
// checker_declaration outside a checker_generate_item".
TEST(CheckerItemsParsing, CheckerGenerateBlockAdmitsCheckerItemsOnly) {
  auto r = Parse(
      "checker c;\n"
      "  if (1) begin : g\n"
      "    task t();\n"
      "    endtask\n"
      "  end\n"
      "endchecker\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a task declaration is not an item of a checker", 3, "A.1.8"));
}

}  // namespace
