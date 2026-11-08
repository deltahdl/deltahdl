#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(EventTriggeredElaborator, WaitTriggeredElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  event ev;\n"
             "  initial wait(ev.triggered);\n"
             "endmodule\n"));
}

TEST(EventTriggeredElaborator, ForkTriggerAndWaitTriggeredElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  event blast;\n"
             "  initial begin\n"
             "    fork\n"
             "      -> blast;\n"
             "      wait(blast.triggered);\n"
             "    join\n"
             "  end\n"
             "endmodule\n"));
}

TEST(EventTriggeredElaborator, TriggeredCallFormElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  event ev;\n"
             "  logic b;\n"
             "  initial b = ev.triggered();\n"
             "endmodule\n"));
}

TEST(EventTriggeredElaborator, AMemberOtherThanTriggeredIsReported) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  class C; event ev;\n"
      "    function void hold(); ev.rand_mode(0); endfunction\n"
      "  endclass\n"
      "  event ev; event evs [2]; C h = new; bit x;\n"
      "  initial begin\n"
      "    ev.foo();\n"
      "    x = evs[1].nope;\n"
      "    h.ev.foo();\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(
      diags, "'rand_mode' is not a built-in method of the event 'ev'", 3,
      "15.5.3"));
  EXPECT_TRUE(ReportedError(
      diags, "'foo' is not a built-in method of the event 'ev'", 7, "15.5.3"));
  EXPECT_TRUE(
      ReportedError(diags, "'nope' is not a built-in method of the event 'evs'",
                    8, "15.5.3"));
  EXPECT_TRUE(ReportedError(
      diags, "'foo' is not a built-in method of the event 'ev'", 9, "15.5.3"));
}

TEST(EventTriggeredElaborator, TriggeredOnAnyEventIsAccepted) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  class C; event ev; endclass\n"
             "  event ev; event evs [2]; C h = new; bit x;\n"
             "  initial begin\n"
             "    x = ev.triggered();\n"
             "    x = evs[0].triggered;\n"
             "    x = h.ev.triggered();\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
