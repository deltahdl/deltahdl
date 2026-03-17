#include "fixture_parser.h"
#include "fixture_program.h"

using namespace delta;

namespace {

TEST(DataReadApiParsing, CovergroupWithCoverpoint) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      logic [2:0] addr;
      covergroup cg @(addr);
        coverpoint addr;
      endgroup
    endmodule
  )"));
}

TEST_F(VerifyParseTest, BasicCovergroup) {
  auto* unit = Parse(R"(
    module m;
      covergroup cg @(posedge clk);
        coverpoint x;
      endgroup
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

TEST_F(VerifyParseTest, CovergroupEndLabel) {
  auto* unit = Parse(R"(
    module m;
      covergroup my_cg @(posedge clk);
        coverpoint x;
      endgroup : my_cg
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

}  // namespace
