#include <gtest/gtest.h>

#include <cstdint>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "fixture_elaborator.h"
#include "helpers_generate_block_items.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(VirtualInterfaceElaboration, AdditionOperatorInForkArm_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  virtual simple_bus a, b, c;\n"
      "  initial fork\n"
      "    c = a + b;\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on virtual interface", 5,
                            "25.9"));
}

TEST(VirtualInterfaceElaboration, AdditionOperatorInForInitialization_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  virtual simple_bus a, b, c;\n"
      "  int i;\n"
      "  initial for (c = a + b; i < 1; i = i + 1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on virtual interface", 5,
                            "25.9"));
}

TEST(VirtualInterfaceElaboration, AdditionOperatorInForStep_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  virtual simple_bus a, b, c;\n"
      "  int i;\n"
      "  initial for (i = 0; i < 1; c = a + b) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on virtual interface", 5,
                            "25.9"));
}

TEST(VirtualInterfaceElaboration, AdditionOperatorInAssertionPassStmt_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  virtual simple_bus a, b, c;\n"
      "  initial assert (1) c = a + b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on virtual interface", 4,
                            "25.9"));
}

TEST(VirtualInterfaceElaboration, AdditionOperatorInAssertionFailStmt_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  virtual simple_bus a, b, c;\n"
      "  initial assert (1) else c = a + b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on virtual interface", 4,
                            "25.9"));
}

TEST(VirtualInterfaceElaboration, AdditionOperatorInRandcaseItem_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  virtual simple_bus a, b, c;\n"
      "  initial randcase\n"
      "    1 : c = a + b;\n"
      "  endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on virtual interface", 5,
                            "25.9"));
}

TEST(VirtualInterfaceElaboration,
     AdditionOperatorInRandsequenceCodeBlock_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  virtual simple_bus a, b, c;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { c = a + b; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on virtual interface", 6,
                            "25.9"));
}

TEST(VirtualInterfaceClockingAccess, ClockingBlockAccessInForkArm_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  virtual simple_bus vif;\n"
      "  logic x;\n"
      "  initial fork\n"
      "    x = vif.cb.sig;\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'cb' is not a clocking block or member of interface 'simple_bus'", 6,
      "25.9"));
}

TEST(VirtualInterfaceClockingAccess,
     ClockingBlockAccessInForInitialization_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  virtual simple_bus vif;\n"
      "  logic x;\n"
      "  int i;\n"
      "  initial for (x = vif.cb.sig; i < 1; i = i + 1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'cb' is not a clocking block or member of interface 'simple_bus'", 6,
      "25.9"));
}

TEST(VirtualInterfaceClockingAccess, ClockingBlockAccessInForStep_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  virtual simple_bus vif;\n"
      "  logic x;\n"
      "  int i;\n"
      "  initial for (i = 0; i < 1; x = vif.cb.sig) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'cb' is not a clocking block or member of interface 'simple_bus'", 6,
      "25.9"));
}

TEST(VirtualInterfaceClockingAccess,
     ClockingBlockAccessInAssertionPassStmt_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  virtual simple_bus vif;\n"
      "  logic x;\n"
      "  initial assert (1) x = vif.cb.sig;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'cb' is not a clocking block or member of interface 'simple_bus'", 5,
      "25.9"));
}

TEST(VirtualInterfaceClockingAccess,
     ClockingBlockAccessInAssertionFailStmt_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  virtual simple_bus vif;\n"
      "  logic x;\n"
      "  initial assert (1) else x = vif.cb.sig;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'cb' is not a clocking block or member of interface 'simple_bus'", 5,
      "25.9"));
}

TEST(VirtualInterfaceClockingAccess, ClockingBlockAccessInRandcaseItem_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  virtual simple_bus vif;\n"
      "  logic x;\n"
      "  initial randcase\n"
      "    1 : x = vif.cb.sig;\n"
      "  endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'cb' is not a clocking block or member of interface 'simple_bus'", 6,
      "25.9"));
}

TEST(VirtualInterfaceClockingAccess,
     ClockingBlockAccessInRandsequenceCodeBlock_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  virtual simple_bus vif;\n"
      "  logic x;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { x = vif.cb.sig; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'cb' is not a clocking block or member of interface 'simple_bus'", 7,
      "25.9"));
}

TEST(ArrayOfVirtualInterfaceInit, IncompatibleElementInForkArm_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface bus_a; endinterface\n"
      "interface bus_b; endinterface\n"
      "module top;\n"
      "  bus_b u();\n"
      "  typedef virtual bus_a vbus;\n"
      "  initial fork\n"
      "    static vbus v[1] = '{u};\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "interface instance 'u' of type 'bus_b' is not "
                            "compatible with virtual interface element type "
                            "'bus_a'",
                            7, "25.9"));
}

TEST(ArrayOfVirtualInterfaceInit,
     IncompatibleElementInRandsequenceCodeBlock_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface bus_a; endinterface\n"
      "interface bus_b; endinterface\n"
      "module top;\n"
      "  bus_b u();\n"
      "  typedef virtual bus_a vbus;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { vbus v[1] = '{u}; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "interface instance 'u' of type 'bus_b' is not "
                            "compatible with virtual interface element type "
                            "'bus_a'",
                            8, "25.9"));
}

TEST(VirtualInterfaceElaboration, ComponentAsCallArgInContAssign_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface pkt_if; logic v; endinterface\n"
      "module top;\n"
      "  virtual pkt_if pif;\n"
      "  wire q;\n"
      "  function logic idf(input logic z); return z; endfunction\n"
      "  assign q = idf(pif.v);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "virtual interface cannot be used in continuous assignment", 6, "25.9"));
}

TEST(VirtualInterfaceElaboration, ComponentInNestedCallArgInContAssign_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface ctrl_if; logic e; endinterface\n"
      "module top;\n"
      "  virtual ctrl_if cif;\n"
      "  wire r;\n"
      "  function logic hold(input logic p); return p; endfunction\n"
      "  function logic wrap(input logic p); return hold(p); endfunction\n"
      "  assign r = wrap(hold(cif.e));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "virtual interface cannot be used in continuous assignment", 7, "25.9"));
}

TEST(VirtualInterfaceElaboration, ComponentInSensitivityIffCondition_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface gate_if; logic g; endinterface\n"
      "module top;\n"
      "  virtual gate_if gif;\n"
      "  logic clk, d, q;\n"
      "  always @(posedge clk iff gif.g) q <= d;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "virtual interface cannot appear in event "
                            "expression",
                            5, "25.9"));
}

TEST(VirtualInterfaceElaboration, ComponentAsCallArgInProceduralStmt_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface log_if; logic s; endinterface\n"
      "module top;\n"
      "  log_if u();\n"
      "  virtual log_if lif;\n"
      "  logic w;\n"
      "  function logic thru(input logic t); return t; endfunction\n"
      "  initial begin\n"
      "    lif = u;\n"
      "    w = thru(lif.s);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(VirtualInterfaceElaboration, CallWithoutComponentInContAssign_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface mem_if; logic m; endinterface\n"
      "module top;\n"
      "  virtual mem_if mif;\n"
      "  logic y;\n"
      "  wire z;\n"
      "  function logic same(input logic k); return k; endfunction\n"
      "  assign z = same(y);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

constexpr const char* kViSourceRefusal =
    "virtual interface can only be assigned from another virtual interface, an "
    "interface instance, or null";

TEST(VirtualInterfaceElaboration, SourceIsAnInstanceArrayElement_Ok) {
  ElabFixture f;
  ElaborateSrc(
      "interface SBus; int a; endinterface\n"
      "module top;\n"
      "  SBus s[0:1]();\n"
      "  virtual SBus v;\n"
      "  initial v = s[1];\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kViSourceRefusal, 5, "25.9"));
}

TEST(VirtualInterfaceElaboration, SourceIsAGenerateBlockInstance_Ok) {
  ElabFixture f;
  ElaborateSrc(
      "interface SBus; int a; endinterface\n"
      "module top;\n"
      "  for (genvar i = 0; i < 3; i++) begin : g\n"
      "    SBus s();\n"
      "  end\n"
      "  virtual SBus v;\n"
      "  initial v = g[1].s;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kViSourceRefusal, 7, "25.9"));
}

TEST(VirtualInterfaceElaboration, SourceIsAnInterfacePort_Ok) {
  ElabFixture f;
  ElaborateSrc(
      "interface SBus; int a; endinterface\n"
      "program P(SBus b);\n"
      "  virtual SBus v;\n"
      "  initial v = b;\n"
      "endprogram\n"
      "module top;\n"
      "  SBus s();\n"
      "  P p(s);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kViSourceRefusal, 4, "25.9"));
}

TEST(VirtualInterfaceElaboration, SourceIsAFunctionsResult_Ok) {
  ElabFixture f;
  ElaborateSrc(
      "interface SBus; int a; endinterface\n"
      "class Pool;\n"
      "  virtual SBus vs[2];\n"
      "  function virtual SBus pick(int i); return vs[i]; endfunction\n"
      "endclass\n"
      "module top;\n"
      "  Pool p;\n"
      "  virtual SBus got;\n"
      "  initial got = p.pick(1);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(
      ReportedError(f.diag.Diagnostics(), kViSourceRefusal, 9, "25.9"));
}

TEST(VirtualInterfaceElaboration, NestedInterfaceInstanceIsAMember_Ok) {
  ElabFixture f;
  ElaborateSrc(
      "interface inner_if; int v; endinterface\n"
      "interface outer_if;\n"
      "  int w;\n"
      "  inner_if in();\n"
      "endinterface\n"
      "module top;\n"
      "  outer_if o();\n"
      "  virtual outer_if vo;\n"
      "  initial begin\n"
      "    vo = o;\n"
      "    vo.in.v = 5;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "'in' is not a clocking block or member of "
                             "interface 'outer_if'",
                             11, "25.9"));
}

TEST(VirtualInterfaceCallElaboration, ACallNamingNothingTheInterfaceDeclares) {
  ElabFixture f;
  ElaborateSrc(
      "package p; function void pf(); endfunction endpackage\n"
      "interface other; task nosuch(); endtask endinterface\n"
      "interface ifc; logic x; task t(); endtask endinterface\n"
      "module top;\n"
      "  class C; function void g(); endfunction C h; endclass\n"
      "  ifc i (); virtual ifc v = i; C c = new;\n"
      "  initial if (0) begin\n"
      "    v.nosuch();\n"
      "    v.t(); c.g(); p::pf(); c.h.g();\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'nosuch' names no task or function of interface "
                            "'ifc'",
                            8, "25.9"));
  for (const Diagnostic& diag : f.diag.Diagnostics()) {
    if (diag.severity != DiagSeverity::kError) continue;
    EXPECT_NE(diag.loc.line, 9u) << diag.message;
  }
}

TEST(VirtualInterfaceCallElaboration,
     ACallThroughABlocksOrAPropertysVirtualInterface) {
  ElabFixture f;
  ElaborateSrc(
      "package p; class K; K f; function void t(); endfunction endclass "
      "endpackage\n"
      "interface ifc; task t(); endtask endinterface\n"
      "class H; virtual ifc vif; static virtual ifc sv; H k; "
      "function void m(); endfunction endclass\n"
      "module top;\n"
      "  import p::*;\n"
      "  class C; virtual ifc cv; endclass\n"
      "  function H mkh(); return null; endfunction\n"
      "  ifc i (); virtual ifc v = i; H h = new; C c = new; "
      "K kk = new;\n"
      "  initial if (0) begin\n"
      "    virtual ifc w;\n"
      "    w = i;\n"
      "    w.nosuch();\n"
      "    h.vif.nosuch();\n"
      "    w.t(); h.vif.t(); c.cv.t(); mkh().m(); H::sv.t(); h.k.vif.t(); "
      "top.v.t(); kk.f.t();\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'nosuch' names no task or function of interface "
                            "'ifc'",
                            12, "25.9"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'nosuch' names no task or function of interface "
                            "'ifc'",
                            13, "25.9"));
  for (const Diagnostic& diag : f.diag.Diagnostics()) {
    if (diag.severity != DiagSeverity::kError) continue;
    EXPECT_NE(diag.loc.line, 14u) << diag.message;
  }
}

TEST(VirtualInterfaceCallElaboration,
     ACallThroughAPackageClasssVirtualInterface) {
  ElabFixture f;
  ElaborateSrc(
      "interface ifc; task t(); endtask endinterface\n"
      "package p; class K; virtual ifc vif; function void m(); endfunction "
      "endclass class Q; virtual ifc vif; endclass endpackage\n"
      "package r; class R; virtual ifc vif; endclass endpackage\n"
      "package e; endpackage\n"
      "import r::R;\n"
      "module top;\n"
      "  import p::K; import e::*; import p::Q;\n"
      "  typedef struct { K h; } S;\n"
      "  K k = new; p::Q q = new; R rr = new; S s;\n"
      "  initial if (0) begin\n"
      "    k.vif.nosuch();\n"
      "    q.vif.nosuch();\n"
      "    rr.vif.nosuch();\n"
      "    k.vif.t(); s.h.m();\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  for (const uint32_t kLine : {11u, 12u, 13u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "'nosuch' names no task or function of "
                              "interface 'ifc'",
                              kLine, "25.9"))
        << kLine;
  }
  for (const Diagnostic& diag : f.diag.Diagnostics()) {
    if (diag.severity != DiagSeverity::kError) continue;
    EXPECT_NE(diag.loc.line, 14u) << diag.message;
  }
}

TEST(VirtualInterfaceCallElaboration,
     ACallThroughATypedefdClassHandlesVirtualInterface) {
  ElabFixture f;
  ElaborateSrc(
      "interface ifc; task t(); endtask endinterface\n"
      "class H; virtual ifc vif; endclass\n"
      "package p; class K; virtual ifc vif; endclass typedef K KT; "
      "typedef K KI; endpackage\n"
      "package q; class QC; virtual ifc vif; endclass typedef QC QT; "
      "endpackage\n"
      "import q::*;\n"
      "typedef H HU;\n"
      "module top;\n"
      "  import p::*;\n"
      "  typedef H HT; typedef HT HT2;\n"
      "  HT2 a = new; HU b = new; KI c = new; p::KT d = new; QT e = new;\n"
      "  initial if (0) begin\n"
      "    a.vif.nosuch();\n"
      "    b.vif.nosuch();\n"
      "    c.vif.nosuch();\n"
      "    d.vif.nosuch();\n"
      "    e.vif.nosuch();\n"
      "    a.vif.t(); d.vif.t();\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  for (const uint32_t kLine : {12u, 13u, 14u, 15u, 16u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "'nosuch' names no task or function of "
                              "interface 'ifc'",
                              kLine, "25.9"))
        << kLine;
  }
  for (const Diagnostic& diag : f.diag.Diagnostics()) {
    if (diag.severity != DiagSeverity::kError) continue;
    EXPECT_NE(diag.loc.line, 17u) << diag.message;
  }
}

TEST(VirtualInterfaceCallElaboration, AnEightTypedefChainReachesTheClass) {
  ElabFixture f;
  ElaborateSrc(
      "interface ifc; task t(); endtask endinterface\n"
      "class H; virtual ifc vif; endclass\n"
      "module top;\n"
      "  typedef H T1; typedef T1 T2; typedef T2 T3; typedef T3 T4;\n"
      "  typedef T4 T5; typedef T5 T6; typedef T6 T7; typedef T7 T8;\n"
      "  T8 g = new;\n"
      "  initial if (0) g.vif.nosuch();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'nosuch' names no task or function of interface "
                            "'ifc'",
                            7, "25.9"));
}

TEST(VirtualInterfaceElaboration,
     VirtualInterfaceInsideGenerateBlocksIsRejected) {
  EXPECT_TRUE(RejectedInsideGenerateBlocks(
      {"interface I; endinterface ", "virtual I v; wire w;", "assign w = v;"},
      "virtual interface cannot be used in continuous assignment", "25.9"));
  EXPECT_TRUE(RejectedInsideGenerateBlocks(
      {"interface I; endinterface ", "virtual I v; logic y;",
       "always @(v) y = 0;"},
      "virtual interface cannot appear in event expression", "25.9"));
  EXPECT_TRUE(AcceptedInsideGenerateBlocks(
      {"interface I; endinterface ", "virtual I v;", "initial v = null;"}));
}

}  // namespace
