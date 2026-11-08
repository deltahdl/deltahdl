#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(EventWaitElaborator, WaitInInitialBlockElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  event ev;\n"
             "  initial @(ev);\n"
             "endmodule\n"));
}

TEST(EventWaitElaborator, WaitWithBodyElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  event ev;\n"
             "  logic x;\n"
             "  initial @(ev) x = 1;\n"
             "endmodule\n"));
}

TEST(EventWaitElaborator, BareWaitSyntaxElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  event ev;\n"
             "  initial @ev;\n"
             "endmodule\n"));
}

TEST(EventWaitElaborator, WaitOnTaskCallRejected) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  task t; endtask\n"
      "  initial @(t());\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "task 't' cannot be called in an event expression",
                            3, "9.4.2"));
}

TEST(EventWaitElaborator, HierarchicalEventWaitElaborates) {
  EXPECT_TRUE(
      ElabOk("module child;\n"
             "  event ev;\n"
             "endmodule\n"
             "module top;\n"
             "  child c1();\n"
             "  initial @(c1.ev);\n"
             "endmodule\n"));
}

}  // namespace
