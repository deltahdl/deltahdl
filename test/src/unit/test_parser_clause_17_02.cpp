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

}  // namespace
