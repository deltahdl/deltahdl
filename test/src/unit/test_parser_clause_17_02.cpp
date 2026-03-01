// §17.2: Checker declaration

#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

using CheckerParseTest = ProgramTestParse;

namespace {

// =============================================================================
// §17.1 Basic checker declaration
// =============================================================================
TEST_F(CheckerParseTest, EmptyChecker) {
  auto* unit = Parse("checker my_check; endchecker");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_EQ(unit->checkers[0]->name, "my_check");
  EXPECT_EQ(unit->checkers[0]->decl_kind, ModuleDeclKind::kChecker);
  EXPECT_TRUE(unit->checkers[0]->ports.empty());
  EXPECT_TRUE(unit->checkers[0]->items.empty());
}

// =============================================================================
// §17.2 Checker ports
// =============================================================================
TEST_F(CheckerParseTest, CheckerWithInputPorts) {
  auto* unit = Parse(R"(
    checker port_check(input logic clk, input logic rst);
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  ASSERT_GE(unit->checkers[0]->ports.size(), 2u);
  EXPECT_EQ(unit->checkers[0]->ports[0].name, "clk");
  EXPECT_EQ(unit->checkers[0]->ports[0].direction, Direction::kInput);
  EXPECT_EQ(unit->checkers[0]->ports[1].name, "rst");
  EXPECT_EQ(unit->checkers[0]->ports[1].direction, Direction::kInput);
}

TEST_F(CheckerParseTest, CheckerWithOutputPorts) {
  auto* unit = Parse(R"(
    checker out_check(input logic clk, output logic valid);
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  ASSERT_GE(unit->checkers[0]->ports.size(), 2u);
  EXPECT_EQ(unit->checkers[0]->ports[1].name, "valid");
  EXPECT_EQ(unit->checkers[0]->ports[1].direction, Direction::kOutput);
}

TEST_F(CheckerParseTest, CheckerWithNoPorts) {
  auto* unit = Parse(R"(
    checker no_ports;
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_TRUE(unit->checkers[0]->ports.empty());
}

TEST_F(CheckerParseTest, CheckerWithEmptyParenPorts) {
  auto* unit = Parse(R"(
    checker empty_parens();
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_TRUE(unit->checkers[0]->ports.empty());
}

// =============================================================================
// §17.3 Checker body with properties and sequences
// =============================================================================
TEST_F(CheckerParseTest, CheckerWithPropertyDecl) {
  auto* unit = Parse(R"(
    checker prop_check(input logic clk, input logic a, input logic b);
      property p1;
        a |-> b;
      endproperty
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_FALSE(unit->checkers[0]->items.empty());
  EXPECT_TRUE(
      HasItemOfKind(unit->checkers[0]->items, ModuleItemKind::kPropertyDecl));
}

TEST_F(CheckerParseTest, CheckerWithSequenceDecl) {
  auto* unit = Parse(R"(
    checker seq_check(input logic clk, input logic a);
      sequence s1;
        a;
      endsequence
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_FALSE(unit->checkers[0]->items.empty());
  EXPECT_TRUE(
      HasItemOfKind(unit->checkers[0]->items, ModuleItemKind::kSequenceDecl));
}

// =============================================================================
// §17.8 Checker coexists with module and program
// =============================================================================
TEST_F(CheckerParseTest, CheckerCoexistsWithModuleAndProgram) {
  auto* unit = Parse(R"(
    module m; endmodule
    program p; endprogram
    checker c; endchecker
  )");
  EXPECT_EQ(unit->modules.size(), 1u);
  EXPECT_EQ(unit->programs.size(), 1u);
  EXPECT_EQ(unit->checkers.size(), 1u);
}

// =============================================================================
// §17.9 Checker with assert property
// =============================================================================
TEST_F(CheckerParseTest, CheckerWithAssertProperty) {
  auto* unit = Parse(R"(
    checker assert_check(input logic clk, input logic a, input logic b);
      assert property (@(posedge clk) a |-> b);
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(unit->checkers[0]->items, ModuleItemKind::kAssertProperty));
}

// =============================================================================
// §17.13 Checker with continuous assignment
// =============================================================================
TEST_F(CheckerParseTest, CheckerWithContAssign) {
  auto* unit = Parse(R"(
    checker assign_check;
      logic a, b;
      assign a = b;
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(unit->checkers[0]->items, ModuleItemKind::kContAssign));
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
  EXPECT_TRUE(HasItemKind(items, ModuleItemKind::kInitialBlock));
  EXPECT_TRUE(HasItemKind(items, ModuleItemKind::kAlwaysBlock));
  EXPECT_TRUE(HasItemKind(items, ModuleItemKind::kFinalBlock));
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
  EXPECT_TRUE(HasItemKind(items, ModuleItemKind::kGenerateFor));
  EXPECT_TRUE(HasItemKind(items, ModuleItemKind::kGenerateIf));
  EXPECT_TRUE(HasItemKind(items, ModuleItemKind::kElabSystemTask));
}

}  // namespace
