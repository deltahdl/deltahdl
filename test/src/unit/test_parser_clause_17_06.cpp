// §17.6: Covergroups in checkers

#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

using CheckerParseTest = ProgramTestParse;

namespace {

TEST_F(VerifyParseTest, CheckerWithCovergroupAndClocking) {
  auto* unit = Parse(R"(
    checker my_check(logic clk, active);
      bit active_d1 = 1'b0;
      always_ff @(posedge clk) begin
        active_d1 <= active;
      end
      covergroup cg_active @(posedge clk);
        cp_active : coverpoint active
        {
          bins idle = { 1'b0 };
          bins active = { 1'b1 };
        }
        option.per_instance = 1;
      endgroup
    endchecker : my_check
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_EQ(unit->checkers[0]->name, "my_check");
  EXPECT_FALSE(unit->checkers[0]->items.empty());
}

// =============================================================================
// §17.14 Checker with covergroup
// =============================================================================
TEST_F(CheckerParseTest, CheckerWithCovergroup) {
  auto* unit = Parse(R"(
    checker cov_check(input logic clk, input logic x);
      covergroup cg @(posedge clk);
        coverpoint x;
      endgroup
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_TRUE(
      HasItemOfKind(unit->checkers[0]->items, ModuleItemKind::kCovergroupDecl));
}

}  // namespace
