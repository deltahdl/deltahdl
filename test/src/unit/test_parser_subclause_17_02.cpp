#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST_F(CheckerParseTest, EmptyChecker) {
  auto* unit = Parse("checker my_check; endchecker");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_EQ(unit->checkers[0]->name, "my_check");
  EXPECT_EQ(unit->checkers[0]->decl_kind, ModuleDeclKind::kChecker);
  EXPECT_TRUE(unit->checkers[0]->ports.empty());
  EXPECT_TRUE(unit->checkers[0]->items.empty());
}

TEST_F(VerifyParseTest, CheckerWithPorts) {
  auto* unit = Parse(R"(
    checker port_check(input logic clk, input logic rst);
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_EQ(unit->checkers[0]->name, "port_check");
  EXPECT_GE(unit->checkers[0]->ports.size(), 2u);
}

TEST_F(VerifyParseTest, MultipleCheckers) {
  auto* unit = Parse(R"(
    checker c1;
    endchecker
    checker c2;
    endchecker
  )");
  EXPECT_EQ(unit->checkers.size(), 2u);
}

TEST_F(VerifyParseTest, CheckerCoexistsWithModule) {
  auto* unit = Parse(R"(
    module m;
    endmodule
    checker c;
    endchecker
  )");
  EXPECT_EQ(unit->modules.size(), 1u);
  EXPECT_EQ(unit->checkers.size(), 1u);
}

TEST(CheckerDeclaration, EndLabelMatchesCheckerName) {
  auto r = Parse("checker ck; endchecker : ck\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->name, "ck");
}

TEST(CheckerDeclaration, MissingEndcheckerIsError) {
  EXPECT_FALSE(ParseOk("checker c;"));
}

TEST(CheckerDeclaration, EndLabelMismatchIsError) {
  // §17.2: the optional name following endchecker must match the checker name.
  auto r = Parse("checker ck; endchecker : other\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.has_errors);
}

TEST(CheckerDeclaration, OutputDirectionFormalParses) {
  // §17.2: checker_port_direction admits output as well as input.
  auto r = Parse("checker chk(output bit a, input bit b); endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_GE(r.cu->checkers[0]->ports.size(), 2u);
  EXPECT_EQ(r.cu->checkers[0]->ports[0].direction, Direction::kOutput);
  EXPECT_EQ(r.cu->checkers[0]->ports[1].direction, Direction::kInput);
}

TEST(CheckerDeclaration, WithAssertion) {
  auto r = Parse(
      "checker chk(input logic clk, input logic req, input logic gnt);\n"
      "  assert property (@(posedge clk) req |-> ##[1:3] gnt);\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kAssertProperty));
}

TEST(CheckerDeclaration, WithModelingCode) {
  auto r = Parse(
      "checker chk;\n"
      "  logic flag;\n"
      "  initial flag = 0;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kVarDecl));
  EXPECT_TRUE(
      HasItemOfKind(r.cu->checkers[0]->items, ModuleItemKind::kInitialBlock));
}

TEST(CheckerDeclaration, FirstFormalOmittedDirectionDefaultsToInput) {
  auto r = Parse("checker chk(logic a, logic b); endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_GE(r.cu->checkers[0]->ports.size(), 2u);
  // §17.2: the first formal defaults to input when its direction is omitted,
  // and the following formal inherits that direction.
  EXPECT_EQ(r.cu->checkers[0]->ports[0].direction, Direction::kInput);
  EXPECT_EQ(r.cu->checkers[0]->ports[1].direction, Direction::kInput);
}

TEST(CheckerDeclaration, OmittedDirectionInheritsExplicitOutput) {
  auto r = Parse("checker chk(output bit a, bit b); endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_GE(r.cu->checkers[0]->ports.size(), 2u);
  // §17.2: a formal with no explicit direction inherits the previous formal's.
  EXPECT_EQ(r.cu->checkers[0]->ports[0].direction, Direction::kOutput);
  EXPECT_EQ(r.cu->checkers[0]->ports[1].direction, Direction::kOutput);
}

TEST(CheckerDeclaration, WithMixedContents) {
  EXPECT_TRUE(
      ParseOk("checker chk(input logic clk, input logic a, input logic b);\n"
              "  logic internal;\n"
              "  always_comb internal = a & b;\n"
              "  assert property (@(posedge clk) a |-> b);\n"
              "  cover property (@(posedge clk) a && b);\n"
              "endchecker\n"));
}

// Returns true if a nested checker declaration appears among `items`.
static bool HasNestedChecker(const std::vector<ModuleItem*>& items) {
  for (const auto* item : items) {
    if (item->kind == ModuleItemKind::kNestedModuleDecl &&
        item->nested_module_decl &&
        item->nested_module_decl->decl_kind == ModuleDeclKind::kChecker) {
      return true;
    }
  }
  return false;
}

// §17.2: a checker may be declared in a module. The construct parses in that
// syntactic position and is recorded as a nested checker declaration.
TEST(CheckerDeclaration, DeclaredInsideModule) {
  auto r = Parse(
      "module m;\n"
      "  checker c; endchecker\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasNestedChecker(r.cu->modules[0]->items));
}

// §17.2: a checker may be declared in an interface.
TEST(CheckerDeclaration, DeclaredInsideInterface) {
  auto r = Parse(
      "interface ifc;\n"
      "  checker c; endchecker\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  EXPECT_TRUE(HasNestedChecker(r.cu->interfaces[0]->items));
}

// §17.2: a checker may be declared in a program.
TEST(CheckerDeclaration, DeclaredInsideProgram) {
  auto r = Parse(
      "program prog;\n"
      "  checker c; endchecker\n"
      "endprogram\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->programs.size(), 1u);
  EXPECT_TRUE(HasNestedChecker(r.cu->programs[0]->items));
}

// §17.2: a checker may be declared in a package.
TEST(CheckerDeclaration, DeclaredInsidePackage) {
  auto r = Parse(
      "package pkg;\n"
      "  checker c; endchecker\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  EXPECT_TRUE(HasNestedChecker(r.cu->packages[0]->items));
}

// §17.2: a checker may be declared in a generate block.
TEST(CheckerDeclaration, DeclaredInsideGenerateBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  if (1) begin : g\n"
              "    checker c; endchecker\n"
              "  end\n"
              "endmodule\n"));
}

// §17.2: a checker body may contain a default clocking specification and a
// default disable iff declaration, from which the checker's clock and disable
// contexts are taken.
TEST(CheckerDeclaration, BodyAllowsClockingAndDisableContexts) {
  EXPECT_TRUE(
      ParseOk("checker c(input logic clk, input logic rst);\n"
              "  clocking cb @(posedge clk); endclocking\n"
              "  default clocking cb;\n"
              "  default disable iff (rst);\n"
              "  a1: assert property (@(posedge clk) 1'b1);\n"
              "endchecker\n"));
}

// §17.2: a checker body may contain initial, always_comb, always_latch,
// always_ff, and final procedures.
TEST(CheckerDeclaration, BodyAllowsProcedureForms) {
  EXPECT_TRUE(
      ParseOk("checker c(input logic clk, input logic en);\n"
              "  logic a, b;\n"
              "  always_ff @(posedge clk) a <= b;\n"
              "  always_latch if (en) b = a;\n"
              "  final begin end\n"
              "endchecker\n"));
}

// §17.2: a checker body may contain deferred assertions (assert #0) as well as
// concurrent assertion statements such as assume property.
TEST(CheckerDeclaration, BodyAllowsDeferredAndAssumeAssertions) {
  EXPECT_TRUE(
      ParseOk("checker c(input logic clk, input logic a, input logic b);\n"
              "  a1: assert #0 ($onehot0({a, b}));\n"
              "  a2: assume property (@(posedge clk) a);\n"
              "endchecker\n"));
}

// §17.2: a checker body may contain declarations of let constructs, sequences,
// properties, and functions, plus covergroup and genvar declarations.
TEST(CheckerDeclaration, BodyAllowsVerificationDeclarations) {
  EXPECT_TRUE(
      ParseOk("checker c(input logic clk, input logic a);\n"
              "  genvar i;\n"
              "  let g = a;\n"
              "  sequence s; @(posedge clk) a; endsequence\n"
              "  property p; @(posedge clk) a; endproperty\n"
              "  function bit f(bit x); return x; endfunction\n"
              "  covergroup cg @(posedge clk); cp: coverpoint a; endgroup\n"
              "  cg cg1 = new();\n"
              "endchecker\n"));
}

// §17.2: a checker body may contain generate blocks (a checker_generate_item
// such as a conditional generate construct) that in turn hold checker body
// elements.
TEST(CheckerDeclaration, BodyAllowsGenerateBlock) {
  EXPECT_TRUE(
      ParseOk("checker c(input logic a);\n"
              "  if (1) begin : g\n"
              "    logic x;\n"
              "    always_comb x = a;\n"
              "  end\n"
              "endchecker\n"));
}

// §17.2: a checker body may contain other checker instantiations.
TEST(CheckerDeclaration, BodyAllowsNestedCheckerInstantiation) {
  EXPECT_TRUE(
      ParseOk("checker inner(input logic x); endchecker\n"
              "checker outer(input logic clk);\n"
              "  inner i1(clk);\n"
              "endchecker\n"));
}

// §17.2: a checker declaration may specify a default value for a singular input
// port using the same syntax as sequences and properties. The parser records
// the default expression on the port.
TEST(CheckerDeclaration, InputPortDefaultValueParses) {
  auto r = Parse("checker c(input logic a = 1'b1); endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_GE(r.cu->checkers[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->ports[0].direction, Direction::kInput);
  EXPECT_NE(r.cu->checkers[0]->ports[0].default_value, nullptr);
}

// §17.2: the type of a checker output argument shall not be untyped. An output
// formal that omits its type is rejected (the counterpart accept path is
// covered by the typed-output tests above).
TEST(CheckerDeclaration, UntypedOutputFormalIsError) {
  auto r = Parse("checker c(output a); endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.has_errors);
}

// §17.2: an output formal that carries a type is accepted, confirming the
// prohibition targets only the untyped form and not outputs in general.
TEST(CheckerDeclaration, TypedOutputFormalIsAccepted) {
  auto r = Parse("checker c(output bit a); endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_GE(r.cu->checkers[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->ports[0].direction, Direction::kOutput);
}

// §17.2: a checker declaration may specify an initial value for a singular
// output port using the same syntax as an input default value.
TEST(CheckerDeclaration, OutputPortInitialValueParses) {
  auto r = Parse("checker c(output int ctr = 0); endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_GE(r.cu->checkers[0]->ports.size(), 1u);
  EXPECT_EQ(r.cu->checkers[0]->ports[0].direction, Direction::kOutput);
  EXPECT_NE(r.cu->checkers[0]->ports[0].default_value, nullptr);
}

}  // namespace
