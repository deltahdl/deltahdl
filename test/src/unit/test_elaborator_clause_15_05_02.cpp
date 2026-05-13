#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §15.5.2: Event wait @(ev) in initial block elaborates.
TEST(EventWaitElaborator, WaitInInitialBlockElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  event ev;\n"
      "  initial @(ev);\n"
      "endmodule\n"));
}

// §15.5.2: Event wait with body statement elaborates.
TEST(EventWaitElaborator, WaitWithBodyElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  event ev;\n"
      "  logic x;\n"
      "  initial @(ev) x = 1;\n"
      "endmodule\n"));
}

// §15.5.2: Bare @ev syntax (no parentheses) elaborates.
TEST(EventWaitElaborator, BareWaitSyntaxElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  event ev;\n"
      "  initial @ev;\n"
      "endmodule\n"));
}

// §15.5.2: Event wait inside begin/end block elaborates.
TEST(EventWaitElaborator, WaitInsideBeginEndElaborates) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  event ev;\n"
      "  logic [31:0] result;\n"
      "  initial begin\n"
      "    @(ev);\n"
      "    result = 42;\n"
      "  end\n"
      "endmodule\n"));
}

// §15.5.2 builds on §9.4.2's event control operator. A task call used in
// place of a hierarchical_event_identifier in an @-wait is therefore
// rejected for the same reason §9.4.2 rejects task calls in event
// expressions.
TEST(EventWaitElaborator, WaitOnTaskCallRejected) {
  EXPECT_FALSE(ElabOk(
      "module m;\n"
      "  task t; endtask\n"
      "  initial @(t());\n"
      "endmodule\n"));
}

// §15.5.2: The wait syntax is "@ hierarchical_event_identifier;" — a
// hierarchical reference to a named event in another instance is a legal
// waited-on identifier and must elaborate.
TEST(EventWaitElaborator, HierarchicalEventWaitElaborates) {
  EXPECT_TRUE(ElabOk(
      "module child;\n"
      "  event ev;\n"
      "endmodule\n"
      "module top;\n"
      "  child c1();\n"
      "  initial @(c1.ev);\n"
      "endmodule\n"));
}

}  // namespace
