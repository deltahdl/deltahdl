#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr std::string_view kNoSuch =
    "'nosuch' names no task or function of interface 'ifc'";

::testing::AssertionResult NoErrorOnLine(const ElabFixture& f, uint32_t line) {
  for (const Diagnostic& diag : f.diag.Diagnostics()) {
    if (diag.severity == DiagSeverity::kError && diag.loc.line == line) {
      return ::testing::AssertionFailure() << diag.message;
    }
  }
  return ::testing::AssertionSuccess();
}

TEST(VirtualInterfaceArrayElaboration, AnElementOfAnArrayIsSelected) {
  ElabFixture f;
  ElaborateSrc(
      "interface ifc; task t(); endtask endinterface\n"
      "module top;\n"
      "  ifc i (); virtual ifc va[2]; virtual ifc vb[2][2]; virtual ifc v;\n"
      "  logic b; logic arr[2]; wire nw[2];\n"
      "  initial begin\n"
      "    va[0] = i; va[0].t(); vb[0][1] = i; b = arr[0] | nw[1];\n"
      "    b = v[0];\n"
      "    b = va[0][1];\n"
      "    b = vb[0][1][0];\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(NoErrorOnLine(f, 6));
  for (const uint32_t kLine : {7u, 8u, 9u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "bit-select on virtual interface is illegal",
                              kLine, "25.9"))
        << kLine;
  }
}

TEST(VirtualInterfaceCallElaboration, ACallThroughAnElementOfAnArray) {
  ElabFixture f;
  ElaborateSrc(
      "interface ifc; task t(); endtask endinterface\n"
      "class H; virtual ifc vifs[2]; virtual ifc vif; endclass\n"
      "module top;\n"
      "  ifc i (); virtual ifc va[2]; virtual ifc vb[2][2]; virtual ifc v;\n"
      "  H h = new;\n"
      "  initial if (0) begin\n"
      "    va[0].nosuch();\n"
      "    vb[1][0].nosuch();\n"
      "    h.vifs[0].nosuch();\n"
      "    va[1].t(); vb[0][1].t(); h.vifs[1].t(); i.t();\n"
      "    v[0].t();\n"
      "    h.vif[0].nosuch();\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  for (const uint32_t kLine : {7u, 8u, 9u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoSuch, kLine, "25.9"))
        << kLine;
  }
  EXPECT_TRUE(NoErrorOnLine(f, 10));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "bit-select on virtual interface is illegal", 11,
                            "25.9"));
}

TEST(VirtualInterfaceCallElaboration, ACallThroughANestedClasssProperty) {
  ElabFixture f;
  ElaborateSrc(
      "interface ifc; task t(); endtask endinterface\n"
      "class H;\n"
      "  class Other; endclass\n"
      "  class Inner; virtual ifc vif; endclass\n"
      "  typedef Inner T;\n"
      "endclass\n"
      "module top;\n"
      "  typedef H HA;\n"
      "  H::Inner i = new; H::T ht; HA::Inner hai;\n"
      "  initial if (0) begin\n"
      "    i.vif.nosuch();\n"
      "    i.vif.t(); ht.vif.t(); hai.vif.t();\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoSuch, 11, "25.9"));
  EXPECT_TRUE(NoErrorOnLine(f, 12));
}

TEST(VirtualInterfaceCallElaboration, APackageTypedefNamesItsPackagesType) {
  ElabFixture f;
  ElaborateSrc(
      "interface ifc; task t(); endtask endinterface\n"
      "package p; class K; virtual ifc vif; endclass typedef K C; "
      "typedef C B; endpackage\n"
      "module top;\n"
      "  import p::*;\n"
      "  typedef B C;\n"
      "  C x = new;\n"
      "  initial if (0) x.vif.nosuch();\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoSuch, 7, "25.9"));
}

TEST(VirtualInterfaceCallElaboration, AForwardTypedefLeadsToTheClassAfterIt) {
  ElabFixture f;
  ElaborateSrc(
      "interface ifc; task t(); endtask endinterface\n"
      "module top;\n"
      "  typedef class F; typedef F FH;\n"
      "  FH g;\n"
      "  initial if (0) g.vif.nosuch();\n"
      "  class F; virtual ifc vif; endclass\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoSuch, 5, "25.9"));
}

TEST(VirtualInterfaceCallElaboration, APackageTypedefOfAnImportedClass) {
  ElabFixture f;
  ElaborateSrc(
      "interface ifc; task t(); endtask endinterface\n"
      "package q; class QK; virtual ifc vif; endclass endpackage\n"
      "package p; import q::*; typedef QK PT; typedef int PI; endpackage\n"
      "module top;\n"
      "  p::PT a = new; p::PI n;\n"
      "  initial if (0) begin\n"
      "    a.vif.nosuch();\n"
      "    n.vif.t();\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoSuch, 7, "25.9"));
  for (const Diagnostic& diag : f.diag.Diagnostics()) {
    if (diag.message.find("names no task") == std::string::npos) continue;
    EXPECT_EQ(diag.loc.line, 7u) << diag.message;
  }
}

TEST(VirtualInterfaceCallElaboration, ACallInAModulesTask) {
  ElabFixture f;
  ElaborateSrc(
      "interface ifc; task t(); endtask endinterface\n"
      "module top;\n"
      "  virtual ifc v;\n"
      "  class C; extern function void run(); function void help(); "
      "endfunction endclass\n"
      "  function void C::run(); help(); endfunction\n"
      "  task go(virtual ifc a, input virtual ifc arr[2]); virtual ifc w;\n"
      "    v.nosuch();\n"
      "    a.nosuch();\n"
      "    w.nosuch();\n"
      "    arr[1].nosuch();\n"
      "    v.t(); a.t(); w.t(); arr[0].t(); later();\n"
      "  endtask\n"
      "  function void later(); endfunction\n"
      "endmodule\n",
      f, "top");
  for (const uint32_t kLine : {7u, 8u, 9u, 10u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoSuch, kLine, "25.9"))
        << kLine;
  }
  EXPECT_TRUE(NoErrorOnLine(f, 5));
  EXPECT_TRUE(NoErrorOnLine(f, 11));
}

TEST(VirtualInterfaceArrayElaboration, ASelectIntoAPropertysVirtualInterface) {
  ElabFixture f;
  ElaborateSrc(
      "interface ifc; task t(); endtask endinterface\n"
      "class H; virtual ifc vif; virtual ifc vifs[2]; logic arr[2]; "
      "endclass\n"
      "module top;\n"
      "  H h = new; logic b;\n"
      "  initial if (0) begin\n"
      "    b = h.vif[0];\n"
      "    b = h.vifs[0][1];\n"
      "    b = h.arr[0]; h.vifs[1].t();\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  for (const uint32_t kLine : {6u, 7u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "bit-select on virtual interface is illegal",
                              kLine, "25.9"))
        << kLine;
  }
  EXPECT_TRUE(NoErrorOnLine(f, 8));
}

TEST(VirtualInterfaceArrayElaboration, AValueRangeSelectsFromNothing) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  logic [1:0] x; logic b;\n"
      "  initial begin\n"
      "    b = x inside {[0:1]};\n"
      "    case (x) inside [0:1]: b = 1; default: b = 0; endcase\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(VirtualInterfaceCallElaboration, ACallInAClassMethod) {
  ElabFixture f;
  ElaborateSrc(
      "interface ifc; task t(); endtask endinterface\n"
      "class C; virtual ifc vif;\n"
      "  task run(); vif.nosuch(); endtask\n"
      "  task ok(int a); vif.t(); ok(1); endtask\n"
      "  class In; virtual ifc iv; task r(); iv.nosuch(); endtask endclass\n"
      "  extern task late();\n"
      "  task w(); int d; d(); endtask\n"
      "endclass\n"
      "class D extends C; task r(); vif.nosuch(); endtask endclass\n"
      "class E extends C; int vif; task r(); vif.nosuch(); endtask endclass\n"
      "task C::late(); vif.nosuch(); endtask\n"
      "package p;\n"
      "  class K; virtual ifc vif; task r(); vif.nosuch(); endtask endclass\n"
      "endpackage\n"
      "module top;\n"
      "  class M; virtual ifc vif; task r(); vif.nosuch(); endtask endclass\n"
      "endmodule\n",
      f, "top");
  for (const uint32_t kLine : {3u, 5u, 9u, 11u, 13u, 16u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoSuch, kLine, "25.9"))
        << kLine;
  }
  EXPECT_TRUE(NoErrorOnLine(f, 4));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kNoSuch, 10, "25.9"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "'d' names a variable or a net, and a call names a task or a function", 7,
      "A.8.2"));
}

TEST(VirtualInterfaceCallElaboration, AMethodOutOfTheBodyOfNoClass) {
  ElabFixture f;
  ElaborateSrc(
      "interface ifc; task t(); endtask endinterface\n"
      "task Nope::t2(); vif.nosuch(); endtask\n"
      "module top; endmodule\n",
      f, "top");
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kNoSuch, 2, "25.9"));
}

TEST(VirtualInterfaceCallElaboration, ACallThroughThis) {
  ElabFixture f;
  ElaborateSrc(
      "interface ifc; task t(); endtask endinterface\n"
      "class C; virtual ifc vif; virtual ifc vifs[2]; int n;\n"
      "  task r(); this.vif.nosuch(); endtask\n"
      "  task r2(); this.vifs[0].nosuch(); endtask\n"
      "  task ok(); this.vif.t(); this.vifs[1].t(); endtask\n"
      "  task other(); this.n.nosuch(); this.none.nosuch(); endtask\n"
      "endclass\n"
      "class D extends C; task r3(); this.vif.nosuch(); endtask endclass\n"
      "module top; endmodule\n",
      f, "top");
  for (const uint32_t kLine : {3u, 4u, 8u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoSuch, kLine, "25.9"))
        << kLine;
  }
  EXPECT_TRUE(NoErrorOnLine(f, 5));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kNoSuch, 6, "25.9"));
}

TEST(VirtualInterfaceCallElaboration, ACallThroughTheModulesVariableInAClass) {
  ElabFixture f;
  ElaborateSrc(
      "interface ifc; task t(); endtask endinterface\n"
      "module top;\n"
      "  virtual ifc v; virtual ifc w;\n"
      "  class M; int w; task r(); v.nosuch(); endtask\n"
      "    task r2(); w.nosuch(); v.t(); endtask endclass\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoSuch, 4, "25.9"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kNoSuch, 5, "25.9"));
}

TEST(VirtualInterfaceCallElaboration, ACallInAGenerateBlock) {
  ElabFixture f;
  ElaborateSrc(
      "interface ifc; task t(); endtask endinterface\n"
      "module top;\n"
      "  ifc i (); virtual ifc v = i;\n"
      "  if (1) begin : g\n"
      "    virtual ifc gv; wire gn; localparam int P = 1;\n"
      "    task automatic gt(int a); endtask\n"
      "    initial begin v.nosuch(); gt(1); gv.t(); end\n"
      "    if (0) begin : g2 initial gv.nosuch(); end\n"
      "    else begin : g3 initial v.nosuch(); end\n"
      "  end\n"
      "  case (1) 1: begin : c initial v.nosuch(); end default: ; endcase\n"
      "  for (genvar k = 0; k < 2; k++) begin : l initial v.nosuch(); end\n"
      "  initial gt(1);\n"
      "endmodule\n",
      f, "top");
  for (const uint32_t kLine : {7u, 8u, 9u, 11u, 12u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kNoSuch, kLine, "25.9"))
        << kLine;
  }
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), "undeclared identifier 'gt'",
                             7, "23.9"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "undeclared identifier 'gt'",
                            13, "23.9"));
}

TEST(VirtualInterfaceArrayElaboration, ASelectIntoTheMethodsOwnProperty) {
  ElabFixture f;
  ElaborateSrc(
      "interface ifc; task t(); endtask endinterface\n"
      "class C; virtual ifc vif; virtual ifc vifs[2]; logic arr[2]; logic b;\n"
      "  task r(); b = vif[0]; endtask\n"
      "  task r2(); b = this.vif[0]; endtask\n"
      "  task r3(); b = vifs[0][1]; endtask\n"
      "  task ok(); b = arr[0]; vifs[0].t(); endtask\n"
      "  task hid(); logic [1:0] vif; b = vif[0]; endtask\n"
      "endclass\n"
      "class D extends C; task r4(); b = vif[0]; endtask endclass\n"
      "module top; endmodule\n",
      f, "top");
  for (const uint32_t kLine : {3u, 4u, 5u, 9u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "bit-select on virtual interface is illegal",
                              kLine, "25.9"))
        << kLine;
  }
  EXPECT_TRUE(NoErrorOnLine(f, 6));
  EXPECT_TRUE(NoErrorOnLine(f, 7));
}

TEST(VirtualInterfaceOutsideReference, ReferenceInAProceduralBodyIsRefused) {
  ElabFixture f;
  ElaborateSrc(
      "interface ifc; logic a;\n"
      "  initial begin a = 0; a = top.x; a = 1; end\n"
      "endinterface\n"
      "interface jfc; logic a;\n"
      "  function automatic logic get(); return top.x; endfunction\n"
      "endinterface\n"
      "module top; logic x; ifc i(); jfc j(); virtual ifc v; virtual jfc w;\n"
      "endmodule\n",
      f, "top");
  for (const char* name : {"ifc", "jfc"}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              std::string("interface '") + name +
                                  "' contains references to objects outside "
                                  "its body and cannot be used as a virtual "
                                  "interface",
                              7, "25.9"));
  }
}

TEST(VirtualInterfaceOutsideReference, NamesTheBodyDeclaresAreInside) {
  EXPECT_TRUE(ElabOk(
      "package pk; typedef struct { int f; } s_t; s_t v; endpackage\n"
      "interface ifc; logic a;\n"
      "  typedef struct { int f; } t_t;\n"
      "  function automatic int get(t_t arg); return arg.f; endfunction\n"
      "  initial begin : blk\n"
      "    t_t loc; t_t arr[2];\n"
      "    int n;\n"
      "    n = loc.f + pk::v.f + blk.n;\n"
      "    foreach (arr[k]) n = arr[k].f;\n"
      "  end\n"
      "endinterface\n"
      "module top; ifc i(); virtual ifc v; endmodule\n"));
}

TEST(VirtualInterfaceModportAssignment, InstanceModportSelectsTheType) {
  ElabFixture f;
  ElaborateSrc(
      "interface PBus #(parameter WIDTH=8); logic [WIDTH-1:0] addr, data;\n"
      "  modport phy(input addr, ref data); modport mon(input addr);\n"
      "endinterface\n"
      "module top; PBus #(32) p32(); PBus p8();\n"
      "  virtual PBus #(32) v32; virtual PBus.phy v8; virtual PBus w;\n"
      "  initial begin\n"
      "    v32 = p32.phy;\n"
      "    v8 = p8.mon;\n"
      "    v8 = p8.phy;\n"
      "    w = p8.addr;\n"
      "  end\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "virtual interface with modport cannot be "
                            "assigned to virtual interface without modport",
                            7, "25.9"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "virtual interface modports do not match", 8,
                            "25.9"));
  EXPECT_TRUE(NoErrorOnLine(f, 9));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "virtual interface with modport cannot be "
                             "assigned to virtual interface without modport",
                             10, "25.9"));
}

TEST(VirtualInterfaceElaboration, ANestedInterfaceTypesAVirtualInterface) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  interface bus #(parameter W = 1); logic [W-1:0] d;\n"
      "    modport mp(input d);\n"
      "  endinterface\n"
      "  bus #(4) b();\n"
      "  virtual bus #(4) vb; virtual bus.mp vm;\n"
      "  virtual bus.nope vn;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(NoErrorOnLine(f, 6));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "modport 'nope' not found in interface 'bus'", 7,
                            "25.9"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "unknown interface 'bus' in virtual interface "
                             "declaration",
                             7, "25.9"));
}

TEST(VirtualInterfaceModportAssignment, ANestedInstancesModportSelectsTheType) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  interface bus; logic d;\n"
      "    modport mp(input d); modport mq(output d);\n"
      "  endinterface\n"
      "  bus b(); virtual bus.mp vm;\n"
      "  initial vm = b.mq;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "virtual interface modports do not match", 6,
                            "25.9"));
}

std::string UnknownInterface(std::string_view name) {
  return "unknown interface '" + std::string(name) +
         "' in virtual interface declaration";
}

TEST(VirtualInterfaceElaboration, EveryVirtualInterfaceTypeOfAModuleIsChecked) {
  ElabFixture f;
  ElaborateSrc(
      "interface bus; logic d; modport mp(input d); endinterface\n"
      "module top;\n"
      "  typedef virtual nope1 t1;\n"
      "  task t(virtual nope2 a); virtual nope3 l; endtask\n"
      "  initial begin virtual nope4 p; end\n"
      "  class C; virtual nope5 cv; endclass\n"
      "  typedef virtual bus.nomp t2;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), UnknownInterface("nope1"), 3,
                            "25.9"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), UnknownInterface("nope2"), 4,
                            "25.9"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), UnknownInterface("nope3"), 4,
                            "25.9"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), UnknownInterface("nope4"), 5,
                            "25.9"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), UnknownInterface("nope5"), 6,
                            "25.9"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "modport 'nomp' not found in interface 'bus'", 7,
                            "25.9"));
}

TEST(VirtualInterfaceElaboration,
     ADeclaredInterfaceTypesEveryVirtualInterface) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "interface ubus; endinterface\n"
      "module top;\n"
      "  interface bus; endinterface\n"
      "  typedef virtual bus t1;\n"
      "  task t(virtual bus a); virtual ubus l; endtask\n"
      "  initial begin virtual bus p; end\n"
      "  class C; virtual ubus cv; virtual bus nv; endclass\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(VirtualInterfaceElaboration, AUnitOrPackageVirtualInterfaceTypeIsChecked) {
  ElabFixture f;
  ElaborateSrc(
      "interface bus; endinterface\n"
      "typedef virtual nope1 t1;\n"
      "virtual nope2 uv;\n"
      "class D; virtual nope3 dv; endclass\n"
      "package pk;\n"
      "  typedef virtual nope4 t4; virtual nope5 pv;\n"
      "  task pt(virtual nope6 a); endtask\n"
      "  virtual bus ok;\n"
      "endpackage\n"
      "module top; endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), UnknownInterface("nope1"), 2,
                            "25.9"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), UnknownInterface("nope2"), 3,
                            "25.9"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), UnknownInterface("nope3"), 4,
                            "25.9"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), UnknownInterface("nope4"), 6,
                            "25.9"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), UnknownInterface("nope5"), 6,
                            "25.9"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), UnknownInterface("nope6"), 7,
                            "25.9"));
  EXPECT_TRUE(NoErrorOnLine(f, 8));
}

}  // namespace
