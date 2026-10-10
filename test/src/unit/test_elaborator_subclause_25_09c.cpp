// §25.9 "Virtual interfaces": a call through a virtual interface names a task
// or a function of the interface the virtual interface refers to an instance
// of, and an array of virtual interfaces is indexed as any array is. The calls
// test_elaborator_subclause_25_09b.cpp writes reach the virtual interface
// through a variable or a class property; the cases here reach the class that
// holds the property through a nested class, a typedef its own scope resolves
// and a forward typedef, index an array of virtual interfaces, and stand in
// the methods of a class and in generate blocks.

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

// Whether `f` holds no error on line `line`.
::testing::AssertionResult NoErrorOnLine(const ElabFixture& f, uint32_t line) {
  for (const Diagnostic& diag : f.diag.Diagnostics()) {
    if (diag.severity == DiagSeverity::kError && diag.loc.line == line) {
      return ::testing::AssertionFailure() << diag.message;
    }
  }
  return ::testing::AssertionSuccess();
}

// §25.9 with §7.4: `virtual ifc va[2]` declares an array of virtual
// interfaces, and va[0] selects one of them, through which the interface's task
// is called; it is no select of a virtual interface (#5813). A select into the
// element, va[0][1], or into an element of the two-dimensional vb, vb[0][1][0],
// selects into a virtual interface, as v[0] does, and each is reported (#5817);
// selects of a logic array and of an array net are not.
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

// §25.9 with §7.4: a call through an element of an array of virtual
// interfaces, one select per unpacked dimension, names a task or a function of
// the interface, and one naming nothing it declares is reported, whether the
// array is a variable (#5819) or a class property (#5820). A call through an
// interface instance is no virtual interface call, and the valid calls are not
// reported; v[0], a select of a single virtual interface, names none, and is
// reported as the select it is. h.vif[0] selects into a single property, no
// element of an array, and its call is not followed.
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

// §25.9 with §8.24: a class nested in another, H::Inner, is found behind the
// enclosing class's scope, past a sibling nested class, so a call through its
// virtual interface property naming nothing the interface declares is
// reported (#5812). H::T, a typedef of H rather than a class nested in it, and
// HA::Inner, behind a typedef rather than a class, name no class this search
// finds, and the valid calls through them are not reported.
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

// §25.9 with §6.18 and §26.2: the module's C names the package's B, and B
// names C as the package sees it, the package's C, the class K, never the
// module's C (#5814).
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

// §25.9 with §6.18: a forward typedef, `typedef class F;`, names no type, so
// the typedef after it naming F reaches the class F declared later in the
// module.
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

// §25.9 with §26.3: a package's typedef naming a class the package imports
// from another reaches that class, and a call through its property naming
// nothing the interface declares is reported; a package typedef of int names
// no class, and the call through the variable of it is no virtual interface
// call.
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

// §25.9 with §13.3: a call in a task the module declares, through the
// module's virtual interface, a formal argument, an element of an array
// argument or a variable the task declares, naming nothing the interface
// declares, is reported as one in a procedural block is (#5822). The valid
// calls and a call of a function declared after the task are not, and neither
// is a call of a class's own method in the class's method defined out of its
// body, which is the class's subroutine rather than the module's.
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

// §25.9 with §7.4: a select into a class property that is a single virtual
// interface, h.vif[0], or past the last dimension of a property's array of
// them, h.vifs[0][1], selects into a virtual interface and is reported
// (#5821); a select of a logic array property, and a call through an element
// of the array, are not.
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

// §11.4.13: the value range [0:1] of an inside set is a select with no
// expression it selects from, and the walk that looks for selects into a
// virtual interface leaves it and reports nothing, whether the set follows
// an inside operator or labels an item of a case inside statement.
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

// §25.9 with §8.3: a call in a method of a class, through a virtual interface
// property the class declares (line 3), one a class nested in it declares
// (line 5), one it inherits (§8.13, line 9), or one of a class a package or a
// module declares (lines 13 and 16), naming nothing the interface declares, is
// reported (#5823), as is one in a method defined out of its class's body
// (§8.24, line 11). A property of a derived class shadows the base's of its
// name, and the call through it, no virtual interface, is not checked against
// the interface (line 10); the valid calls are not reported (line 4). A call
// of a method's local variable names data (A.8.2, line 7).
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

// §8.24: a method defined out of the body of a class the scope does not
// declare, Nope::t2, has no class scope to be walked in, and the call it
// writes through a name no property bears is not checked against an
// interface.
TEST(VirtualInterfaceCallElaboration, AMethodOutOfTheBodyOfNoClass) {
  ElabFixture f;
  ElaborateSrc(
      "interface ifc; task t(); endtask endinterface\n"
      "task Nope::t2(); vif.nosuch(); endtask\n"
      "module top; endmodule\n",
      f, "top");
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(), kNoSuch, 2, "25.9"));
}

// §25.9 with §8.11: a method reaches a property of its own class, or one it
// inherits, through `this`, and a call through this.vif, or through an element
// of this.vifs, naming nothing the interface declares is reported (#5824).
// this.n names a property that is no virtual interface and this.none names no
// property, and neither call is checked against the interface.
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

// §25.9 with §23.9: a method of a class a module declares sees the module's
// variables, and a call through the module's virtual interface v naming
// nothing the interface declares is reported (#5825). The class's property w
// hides the module's virtual interface of its name, and the call through it is
// not checked against the interface.
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

// §25.9 with §27: a procedure of a generate block, whether the block is a
// conditional construct's (line 7), its else branch's (line 9), a case
// construct's (line 11) or a loop's (line 12), or nested in another (line 8),
// is checked as the module's own are (#5826), through the module's virtual
// interface and through one the block declares. A task the block declares is
// called there (line 7) and nowhere after the block (line 13, §23.9); the
// block's net and its parameter declare nothing a call names.
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

}  // namespace
