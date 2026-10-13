#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(EventTriggerElaborator, BlockingTriggerElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  event ev;\n"
             "  initial -> ev;\n"
             "endmodule\n"));
}

TEST(EventTriggerElaborator, NonblockingTriggerElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  event ev;\n"
             "  initial ->> ev;\n"
             "endmodule\n"));
}

TEST(EventTriggerElaborator, NonblockingTriggerWithDelayElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  event ev;\n"
             "  initial ->> #5 ev;\n"
             "endmodule\n"));
}

TEST(EventTriggerElaborator, NonblockingTriggerWithEventControlElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  event ev;\n"
             "  logic clk;\n"
             "  initial ->> @(posedge clk) ev;\n"
             "endmodule\n"));
}

TEST(EventTriggerElaborator, TriggerAndWaitElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  event ev;\n"
             "  initial begin\n"
             "    #5 -> ev;\n"
             "  end\n"
             "  initial begin\n"
             "    @(ev);\n"
             "  end\n"
             "endmodule\n"));
}

// §15.5.1: a trigger makes a named event occur, so its target is an event,
// which a variable of type int is not.
TEST(EventTriggerElaborator, TriggerOfAnIntVariableIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int n;\n"
      "  initial -> n;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "trigger target 'n' is not a named event", 3,
                            "15.5.1"));
}

// §15.5.1: a nonblocking trigger's target is an event as a blocking one's is.
TEST(EventTriggerElaborator, NonblockingTriggerOfALogicVariableIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic l;\n"
      "  initial ->> #1 l;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "trigger target 'l' is not a named event", 3,
                            "15.5.1"));
}

// §15.5.1: an event, an element of an array of events, an event of a typedef
// of event, a class's event property, an event formal hiding a module variable
// of its name, an event a block declares and one of the compilation unit's
// scope are each a trigger's target.
TEST(EventTriggerElaborator, TriggerOfEveryFormOfEventElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "event ue;\n"
      "module m;\n"
      "  typedef event ev_t;\n"
      "  class C; event ce; endclass\n"
      "  event e, arr[2];\n"
      "  ev_t te;\n"
      "  int ev;\n"
      "  C h = new;\n"
      "  task trig(event ev);\n"
      "    -> ev;\n"
      "  endtask\n"
      "  initial begin\n"
      "    event local_e;\n"
      "    -> e;\n"
      "    -> arr[1];\n"
      "    -> te;\n"
      "    -> h.ce;\n"
      "    -> ue;\n"
      "    ->> local_e;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
