#include "fixture_parser.h"
#include "fixture_program.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST_F(VerifyParseTest, CheckerWithAssumeProperty) {
  auto* unit = Parse(R"(
    checker observer_model(bit valid, reset);
      default clocking @$global_clock; endclocking
      rand bit flag;
      m1: assume property (reset |=> !flag);
      m2: assume property (!reset && flag |=> flag);
      m3: assume property ($rising_gclk(flag) |-> valid);
    endchecker : observer_model
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_EQ(unit->checkers[0]->name, "observer_model");
  EXPECT_FALSE(unit->checkers[0]->items.empty());
}

}  // namespace
