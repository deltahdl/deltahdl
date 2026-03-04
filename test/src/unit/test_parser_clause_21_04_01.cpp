#include "fixture_program.h"
#include "fixture_simulator.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST_F(ApiParseTest, ReadmembSystemCall) {
  auto* unit = Parse(R"(
    module m;
      logic [7:0] mem [0:255];
      initial $readmemb("data.bin", mem);
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
}

}
