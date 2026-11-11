#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(ClassHandleArgument, AnInputHandleReachesTheCallersObject) {
  SimFixture f;
  auto out = RunCapture(
      "class C; int x; endclass\n"
      "module t;\n"
      "  function void fi(input C p); p.x = 5; endfunction\n"
      "  task ti(C p); p.x = 6; endtask\n"
      "  C h, k;\n"
      "  initial begin\n"
      "    h = new; h.x = 1; k = h;\n"
      "    fi(h); $write(\"%0d %0d \", h.x, h === k);\n"
      "    ti(h); $display(\"%0d %0d\", h.x, h === k);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "5 1 6 1\n");
}

TEST(ClassHandleArgument, RebindingAnInputFormalLeavesTheActualAlone) {
  SimFixture f;
  auto out = RunCapture(
      "class C; int x; endclass\n"
      "module t;\n"
      "  function void fr(input C p); p = new; p.x = 9; endfunction\n"
      "  task tn(C p); p = null; endtask\n"
      "  C h, k;\n"
      "  initial begin\n"
      "    h = new; h.x = 1; k = h;\n"
      "    fr(h); $write(\"%0d %0d \", h.x, h === k);\n"
      "    tn(h); $display(\"%0d %0d\", h.x, h === k);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1 1 1\n");
}

TEST(ClassHandleArgument, AnOutputFormalsHandleIsCopiedBackOnReturn) {
  SimFixture f;
  auto out = RunCapture(
      "class C; int x; endclass\n"
      "module t;\n"
      "  function void fo(output C p); p = new; p.x = 7; endfunction\n"
      "  task tw(output C p); p = new; p.x = 4; #2; endtask\n"
      "  C h, k;\n"
      "  initial begin\n"
      "    h = new; h.x = 1; k = h;\n"
      "    fo(h); $write(\"%0d %0d %0d \", h.x, h === k, k.x);\n"
      "    h = k;\n"
      "    fork tw(h); #1 $write(\"%0d %0d \", h.x, h === k); join\n"
      "    $display(\"%0d %0d\", h.x, h === k);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "7 0 1 1 1 4 0\n");
}

TEST(ClassHandleArgument, AnUnassignedOutputFormalReturnsNull) {
  SimFixture f;
  auto out = RunCapture(
      "class C; int x; endclass\n"
      "module t;\n"
      "  task tu(output C p); endtask\n"
      "  function void fu(output C p); endfunction\n"
      "  C h, g;\n"
      "  initial begin\n"
      "    h = new; g = new;\n"
      "    tu(h); fu(g);\n"
      "    $display(\"%0d %0d\", h == null, g == null);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1\n");
}

TEST(ClassHandleArgument, AnInoutFormalsHandleIsCopiedInAndBack) {
  SimFixture f;
  auto out = RunCapture(
      "class C; int x; endclass\n"
      "module t;\n"
      "  function int fio(inout C p);\n"
      "    int r; r = p.x; p = new; p.x = 8; return r;\n"
      "  endfunction\n"
      "  task tio(inout C p); p.x = 3; p = new; p.x = 6; #2; endtask\n"
      "  C h, k;\n"
      "  int r;\n"
      "  initial begin\n"
      "    h = new; h.x = 1; k = h;\n"
      "    r = fio(h); $write(\"%0d %0d %0d %0d \", r, h.x, h === k, k.x);\n"
      "    h = k;\n"
      "    fork tio(h); #1 $write(\"%0d %0d \", h.x, h === k); join\n"
      "    $display(\"%0d %0d %0d\", h.x, h === k, k.x);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 8 0 1 3 1 6 0 3\n");
}

TEST(ClassHandleArgument, EveryDirectionOnAClassMethodsFormal) {
  SimFixture f;
  auto out = RunCapture(
      "class B; int x; endclass\n"
      "class D extends B; int y; endclass\n"
      "class M;\n"
      "  function void mi(B p); p.x = 5; p = null; endfunction\n"
      "  function void mo(output B p); D d = new; d.x = 7; p = d; endfunction\n"
      "  function void mio(inout B p); p.x = p.x + 10; p = new; p.x = 8;\n"
      "  endfunction\n"
      "  task mr(ref B p); p = new; p.x = 4; endtask\n"
      "endclass\n"
      "module t;\n"
      "  M m; B b, k; D d, dd;\n"
      "  initial begin\n"
      "    m = new; d = new; d.x = 1;\n"
      "    m.mi(d); $write(\"%0d %0d \", d.x, d != null);\n"
      "    m.mo(b); $write(\"%0d %0d \", b.x, $cast(dd, b));\n"
      "    k = b; m.mio(b); $write(\"%0d %0d %0d \", b.x, b === k, k.x);\n"
      "    k = b; m.mr(b); $display(\"%0d %0d\", b.x, b === k);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "5 1 7 1 8 0 17 4 0\n");
}

TEST(ClassHandleArgument, HandlesPassedInPackagesInterfacesAndPrograms) {
  SimFixture f;
  auto out = RunCapture(
      "package pk;\n"
      "  class C; int x; endclass\n"
      "  function automatic void pf(C p, output C q);\n"
      "    p.x = 3; q = p; p = null;\n"
      "  endfunction\n"
      "endpackage\n"
      "import pk::*;\n"
      "interface ifc;\n"
      "  task automatic it(inout C p);\n"
      "    p.x = p.x * 2; p = new; p.x = 50;\n"
      "  endtask\n"
      "endinterface\n"
      "program pr;\n"
      "  task automatic pt(C p); p.x = p.x + 100; p = null; endtask\n"
      "  C o;\n"
      "  initial begin\n"
      "    #1 o = new; o.x = 1; pt(o); $display(\"%0d %0d\", o.x, o != null);\n"
      "  end\n"
      "endprogram\n"
      "module t;\n"
      "  ifc i();\n"
      "  pr pi();\n"
      "  C h, g, k;\n"
      "  initial begin\n"
      "    h = new; pf(h, g); $write(\"%0d %0d \", h.x, g === h);\n"
      "    k = h; i.it(h); $display(\"%0d %0d %0d\", h.x, k.x, h === k);\n"
      "    #2;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "3 1 50 6 0\n101 1\n");
}

const char* const kPacketClass =
    "class Packet ;\n"
    "  bit [3:0] command;\n"
    "  bit [40:0] address;\n"
    "  bit [4:0] initiator_id;\n"
    "  integer time_requested;\n"
    "  integer time_issued;\n"
    "  integer status;\n"
    "  typedef enum {ERR_OVERFLOW = 10, ERR_UNDERFLOW = 1123} PCKT_TYPE;\n"
    "  const integer buffer_size = 100;\n"
    "  const integer header_size;\n"
    "  function new();\n"
    "    command = 4'd0;\n"
    "    address = 41'b0;\n"
    "    initiator_id = 5'bx;\n"
    "    header_size = 10;\n"
    "  endfunction\n"
    "  task clean();\n"
    "    command = 0; address = 0; initiator_id = 5'bx;\n"
    "  endtask\n"
    "  task issue_request( int delay );\n"
    "  endtask\n"
    "  function integer current_status();\n"
    "    current_status = status;\n"
    "  endfunction\n"
    "endclass\n";

TEST(PacketClass, TheWholeClassElaboratesAndConstructsWithItsValues) {
  SimFixture f;
  auto out = RunCapture(std::string(kPacketClass) +
                            "module t;\n"
                            "  Packet p;\n"
                            "  initial begin\n"
                            "    p = new;\n"
                            "    $display(\"%0d %b %b %0d %0d %b %b %b %0d\",\n"
                            "      p.command, p.address, p.initiator_id,\n"
                            "      p.header_size, p.buffer_size, p.status,\n"
                            "      p.time_requested, p.time_issued,\n"
                            "      $bits(p.address));\n"
                            "  end\n"
                            "endmodule\n",
                        f);
  EXPECT_EQ(out, "0 " + std::string(41, '0') + " 00000 10 100 " +
                     std::string(32, 'x') + " " + std::string(32, 'x') + " " +
                     std::string(32, 'x') + " 41\n");
  EXPECT_EQ(f.diag.ErrorCount(), 0u);
  EXPECT_EQ(f.diag.WarningCount(), 0u);
}

TEST(PacketClass, ItsMethodsRunOnAConstructedObject) {
  SimFixture f;
  auto out =
      RunCapture(std::string(kPacketClass) +
                     "module t;\n"
                     "  Packet p;\n"
                     "  initial begin\n"
                     "    p = new;\n"
                     "    p.command = 3; p.address = '1;\n"
                     "    p.initiator_id = 5'b10101;\n"
                     "    p.clean();\n"
                     "    $write(\"%0d %0d %b \", p.command, p.address,\n"
                     "      p.initiator_id);\n"
                     "    p.status = 3;\n"
                     "    $write(\"%0d \", p.current_status());\n"
                     "    p.issue_request(5);\n"
                     "    $display(\"done\");\n"
                     "  end\n"
                     "endmodule\n",
                 f);
  EXPECT_EQ(out, "0 0 00000 3 done\n");
}

TEST(PacketClass, ItsEnumerationConstantReadsThroughTheClassScope) {
  SimFixture f;
  auto out =
      RunCapture(std::string(kPacketClass) +
                     "module t;\n"
                     "  Packet::PCKT_TYPE e;\n"
                     "  initial begin\n"
                     "    e = Packet::ERR_UNDERFLOW;\n"
                     "    $display(\"%0d %s %0d\", Packet::ERR_UNDERFLOW,\n"
                     "      e.name(), $bits(Packet::ERR_UNDERFLOW));\n"
                     "  end\n"
                     "endmodule\n",
                 f);
  EXPECT_EQ(out, "1123 ERR_UNDERFLOW 32\n");
}

TEST(PacketClass, DISABLED_ItsEnumerationConstantIsOfTheClassScopeType) {
  SimFixture f;
  auto out =
      RunCapture(std::string(kPacketClass) +
                     "module t;\n"
                     "  Packet::PCKT_TYPE e;\n"
                     "  initial\n"
                     "    $display(\"%0d\", $typename(Packet::ERR_UNDERFLOW)"
                     " == $typename(e));\n"
                     "endmodule\n",
                 f);
  EXPECT_EQ(out, "1\n");
}

}  // namespace
