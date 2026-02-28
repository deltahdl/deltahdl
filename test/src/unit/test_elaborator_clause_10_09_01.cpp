// §10.9.1: Array assignment patterns


#include "simulator/lowerer.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/variable.h"

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(ElabCh511, ArrayInitPattern_SimpleArrayOk) {
  // §5.11 / §10.9.1: Expressions shall match element for element.
  SimFixture f;
  ElaborateSrc(
      "module top();\n"
      "  int arr[1:0] = '{10, 20};\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
