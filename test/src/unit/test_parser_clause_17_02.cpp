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

TEST(CheckerDeclarations, CheckerContainsDeclarations) {
  auto r = Parse(
      "checker chk;\n"
      "  logic flag;\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_FALSE(r.cu->checkers[0]->items.empty());
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

}  // namespace
