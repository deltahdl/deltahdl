#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(SyncEventParse, WaitForClockingSignalChange) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  clocking ram_bus @(posedge clk);\n"
              "    input ack_l;\n"
              "  endclocking\n"
              "  initial @(ram_bus.ack_l) $display(\"ack\");\n"
              "endmodule\n"));
}

TEST(SyncEventParse, PosedgeClockingSignal) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  clocking ram_bus @(posedge clk);\n"
              "    input enable;\n"
              "  endclocking\n"
              "  initial @(posedge ram_bus.enable) $display(\"en\");\n"
              "endmodule\n"));
}

TEST(SyncEventParse, NegedgeClockingSignalSlice) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  clocking dom @(posedge clk);\n"
              "    input sign;\n"
              "  endclocking\n"
              "  initial @(negedge dom.sign[a]) $display(\"neg\");\n"
              "endmodule\n"));
}

TEST(SyncEventParse, CompoundOrEvent) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  clocking dom @(posedge clk);\n"
              "    input sig1, sig2;\n"
              "  endclocking\n"
              "  initial @(posedge dom.sig1 or dom.sig2) $display(\"or\");\n"
              "endmodule\n"));
}

TEST(SyncEventParse, MixedEdgeCompoundEvent) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  clocking dom @(posedge clk);\n"
              "    input sig1, sig2;\n"
              "  endclocking\n"
              "  initial @(negedge dom.sig1 or posedge dom.sig2)"
              " $display(\"mixed\");\n"
              "endmodule\n"));
}

TEST(SyncEventParse, EdgeKeywordOnClockingSignal) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  clocking dom @(posedge clk);\n"
              "    input sig1;\n"
              "  endclocking\n"
              "  initial @(edge dom.sig1) $display(\"edge\");\n"
              "endmodule\n"));
}

TEST(SyncEventParse, InoutSignalSyncEvent) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  clocking cb @(posedge clk);\n"
              "    inout data;\n"
              "  endclocking\n"
              "  initial @(cb.data) $display(\"inout\");\n"
              "endmodule\n"));
}

TEST(SyncEventParse, WaitForClockingBlockEvent) {
  // §14.15: an @ expression that names a clocking block on its own (rather than
  // one of its signals) waits for that block's next clocking event, e.g.
  // @(ram_bus);.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  clocking ram_bus @(posedge clk);\n"
              "    input ack_l;\n"
              "  endclocking\n"
              "  initial @(ram_bus) $display(\"tick\");\n"
              "endmodule\n"));
}

}  // namespace
