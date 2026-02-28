// §30.4: Module path declarations

#include "simulator/specify.h"

#include "fixture_simulator.h"
#include "fixture_specify.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST_F(SpecifyTest, RuntimeMultiplePathDelays) {
  SpecifyManager mgr;
  PathDelay pd1;
  pd1.src_port = "in1";
  pd1.dst_port = "out1";
  pd1.delays[0] = 5;
  mgr.AddPathDelay(pd1);

  PathDelay pd2;
  pd2.src_port = "in2";
  pd2.dst_port = "out2";
  pd2.delays[0] = 8;
  pd2.path_kind = SpecifyPathKind::kFull;
  mgr.AddPathDelay(pd2);

  EXPECT_EQ(mgr.PathDelayCount(), 2u);
  EXPECT_EQ(mgr.GetPathDelay("in1", "out1"), 5u);
  EXPECT_EQ(mgr.GetPathDelay("in2", "out2"), 8u);
}

// Path declarations do not interfere with behavioral initial block
TEST(SimA702, PathDeclsDoNotInterfereBehavioral) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  specify\n"
      "    (x => y) = 5;\n"
      "    (posedge clk *> q, qb) = (3, 5);\n"
      "    if (en) (x => y) = 10;\n"
      "    ifnone (x => y) = 15;\n"
      "  endspecify\n"
      "  initial begin\n"
      "    a = 8'd11;\n"
      "    b = 8'd22;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 11u}, {"b", 22u}});
}

}  // namespace
