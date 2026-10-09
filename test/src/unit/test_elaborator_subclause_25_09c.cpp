// §25.9 "Virtual interfaces": a call through a virtual interface names a task
// or a function of the interface the virtual interface refers to an instance
// of, and an array of virtual interfaces is indexed as any array is. The calls
// test_elaborator_subclause_25_09b.cpp writes reach the virtual interface
// through a variable or a class property; the cases here reach the class that
// holds the property through a nested class, a typedef its own scope resolves
// and a forward typedef, and index an array of virtual interfaces.

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

}  // namespace
