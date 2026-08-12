#include "fixture_elaborator.h"

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

// §15.5.2 states only how a process waits, "The @ operator blocks the calling
// process until the given event is triggered", and states no rule about what an
// event expression may call. That rule is §9.4.2, which permits a method in an
// event control expression only "as long as the type of the return value is
// singular and the method is defined as a function, not a task", so the
// rejection of `@(t())` is reported under §9.4.2.
TEST(EventWaitElaborator, WaitOnTaskCallRejected) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  task t; endtask\n"
      "  initial @(t());\n"
      "endmodule\n",
      f);
  const Diagnostic* diag =
      FindDiag(f, "task 't' cannot be called in an event expression");
  ASSERT_NE(diag, nullptr);
  EXPECT_EQ(diag->subclause, "9.4.2");
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
