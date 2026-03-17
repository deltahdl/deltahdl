#include "fixture_program.h"

using namespace delta;

namespace {

TEST_F(VerifyParseTest, CovergroupWithOption) {
  auto* unit = Parse(R"(
    module m;
      covergroup cg @(posedge clk);
        option.per_instance = 1;
        coverpoint x;
      endgroup
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

}  // namespace
