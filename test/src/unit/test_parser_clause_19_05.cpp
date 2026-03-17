#include "fixture_program.h"

using namespace delta;

namespace {

TEST_F(VerifyParseTest, CovergroupWithIff) {
  auto* unit = Parse(R"(
    module m;
      covergroup cg @(posedge clk);
        coverpoint x iff (en);
      endgroup
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

}  // namespace
