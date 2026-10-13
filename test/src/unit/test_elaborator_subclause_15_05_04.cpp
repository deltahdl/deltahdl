#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(WaitOrderElaborator, BasicWaitOrderElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  event a, b, c;\n"
             "  initial wait_order(a, b, c);\n"
             "endmodule\n"));
}

TEST(WaitOrderElaborator, WaitOrderWithActionElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  event a, b;\n"
             "  initial wait_order(a, b) $display(\"ok\");\n"
             "endmodule\n"));
}

TEST(WaitOrderElaborator, WaitOrderWithElseElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  event a, b;\n"
             "  initial\n"
             "    wait_order(a, b) $display(\"ok\");\n"
             "    else $display(\"fail\");\n"
             "endmodule\n"));
}

// §15.5.4: wait_order waits for the events it lists to be triggered in order,
// so each operand is an event, which a variable of type int is not.
TEST(WaitOrderElaborator, WaitOrderOnAnIntOperandIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  event a;\n"
      "  int n;\n"
      "  initial wait_order (a, n);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "wait_order operand 'n' is not a named event", 4,
                            "15.5.4"));
}

// §15.5.4: an event, an element of an array of events and an event of a
// typedef of event are each a wait_order operand.
TEST(WaitOrderElaborator, WaitOrderOnEventsArrayElementsAndTypedefsElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef event ev_t;\n"
      "  event a, arr[2];\n"
      "  ev_t te;\n"
      "  initial wait_order (a, arr[0], te) else $display(\"out of order\");\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
