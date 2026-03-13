#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(SyncEventElab, WaitForClockingBlockEventElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  clocking cb @(posedge clk);\n"
             "    input data;\n"
             "  endclocking\n"
             "  initial @(cb) $display(cb.data);\n"
             "endmodule\n"));
}

TEST(SyncEventElab, WaitForClockingSignalChangeElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  clocking cb @(posedge clk);\n"
             "    input ack;\n"
             "  endclocking\n"
             "  initial @(cb.ack) $display(\"ack\");\n"
             "endmodule\n"));
}

TEST(SyncEventElab, PosedgeClockingSignalElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  clocking cb @(posedge clk);\n"
             "    input enable;\n"
             "  endclocking\n"
             "  initial @(posedge cb.enable) $display(\"en\");\n"
             "endmodule\n"));
}

TEST(SyncEventElab, CompoundEventElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  clocking dom @(posedge clk);\n"
             "    input sig1, sig2;\n"
             "  endclocking\n"
             "  initial @(posedge dom.sig1 or dom.sig2) $display(\"or\");\n"
             "endmodule\n"));
}

TEST(SyncEventElab, InoutSyncEventElaborates) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  clocking cb @(posedge clk);\n"
             "    inout data;\n"
             "  endclocking\n"
             "  initial @(cb.data) $display(\"inout\");\n"
             "endmodule\n"));
}

}  // namespace
