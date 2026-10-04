#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

// §37.7 Modport: the clause is a single VPI object-model diagram with no
// numbered "Details". It defines the modport object (vpiModport) carrying one
// property and two relationships:
//   - "-> name, str: vpiName" - a modport reports its name through
//     vpi_get_str(vpiName);
//   - interface <-> modport - the enclosing interface iterates to its modports
//   and
//     a modport reaches its enclosing interface;
//   - modport <-> io decl - a modport iterates to the io declarations it groups
//   and
//     an io decl reaches its enclosing modport.
// None of these need modport-specific production code: the name flows through
// the generic vpi_get_str(vpiName) branch (a modport is not a port, port bit,
// or atomic statement, so it returns its stored name), forward traversal is the
// generic vpi_iterate child walk, and reverse traversal is the generic
// vpi_handle parent lookup. These tests install a context and observe that
// existing machinery applying each diagram element to a modport.

// The fixture installs a context so the public
// vpi_get_str/vpi_iterate/vpi_scan/ vpi_handle entry points run their real
// dispatch over the test objects.
class Modport : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// Property: a modport reports its name through vpi_get_str(vpiName). A modport
// is none of the kinds the vpiName branch special-cases (port, port bit, atomic
// statement), so the generic name path hands back its stored identifier.
TEST_F(Modport, ReportsItsNameViaVpiName) {
  VpiObject modport;
  modport.type = vpiModport;
  modport.name = "phy";

  EXPECT_STREQ(vpi_get_str(vpiName, VpiHandleOf(&modport)), "phy");
}

// Edge interface <-> modport, both directions. Forward: the enclosing interface
// iterates to its modport children via vpi_iterate(vpiModport, interface).
// Reverse: the modport reaches its enclosing interface via
// vpi_handle(vpiInterface, modport).
TEST_F(Modport, InterfaceAndModportTraverseBothWays) {
  VpiObject iface;
  iface.type = vpiInterface;

  VpiObject modport;
  modport.type = vpiModport;
  modport.name = "phy";
  modport.parent = &iface;
  iface.children = {&modport};

  // Forward: interface iterates to the modport it groups.
  vpiHandle iter = vpi_iterate(vpiModport, VpiHandleOf(&iface));
  ASSERT_NE(iter, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(iter)), &modport);
  EXPECT_EQ(vpi_scan(iter), nullptr);

  // Reverse: the modport reaches its enclosing interface.
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiInterface, VpiHandleOf(&modport))),
            &iface);
}

// Edge modport <-> io decl, both directions. Forward: the modport iterates to
// the io declarations it groups via vpi_iterate(vpiIODecl, modport). Reverse:
// an io decl reaches its enclosing modport via vpi_handle(vpiModport, iodecl).
TEST_F(Modport, ModportAndIoDeclTraverseBothWays) {
  VpiObject modport;
  modport.type = vpiModport;

  VpiObject in_decl;
  in_decl.type = vpiIODecl;
  in_decl.parent = &modport;
  VpiObject out_decl;
  out_decl.type = vpiIODecl;
  out_decl.parent = &modport;
  modport.children = {&in_decl, &out_decl};

  // Forward: the modport iterates to the io declarations it groups.
  vpiHandle iter = vpi_iterate(vpiIODecl, VpiHandleOf(&modport));
  ASSERT_NE(iter, nullptr);
  int count = 0;
  while (vpi_scan(iter) != nullptr) ++count;
  EXPECT_EQ(count, 2);

  // Reverse: an io decl reaches its enclosing modport.
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiModport, VpiHandleOf(&in_decl))),
            &modport);
}

// Edge for C3 forward: a modport that groups no io declarations yields no
// iterator. The generic iteration reports an empty walk as a null handle rather
// than an iterator that scans nothing - the empty-iterator branch, distinct
// from the populated walk above.
TEST_F(Modport, ModportWithNoIoDeclsIteratesToNone) {
  VpiObject modport;
  modport.type = vpiModport;

  EXPECT_EQ(vpi_iterate(vpiIODecl, VpiHandleOf(&modport)), nullptr);
}

// Edge for C2 reverse: a modport with no enclosing interface reaches none
// through vpi_handle(vpiInterface, modport) - the reverse parent lookup reports
// NULL when no interface parent is recorded, distinct from the matching-parent
// path above.
TEST_F(Modport, ModportWithoutEnclosingInterfaceReachesNone) {
  VpiObject modport;
  modport.type = vpiModport;

  EXPECT_EQ(vpi_handle(vpiInterface, VpiHandleOf(&modport)), nullptr);
}

// Edge for C2 forward negative: an interface that groups no modports yields no
// iterator through vpi_iterate(vpiModport, interface). This is the forward edge
// of the interface<->modport relationship reported empty (a null handle rather
// than an iterator that scans nothing) - a different reference object (an
// interface) and relation than the empty io-decl walk observed above.
TEST_F(Modport, InterfaceWithNoModportsIteratesToNone) {
  VpiObject iface;
  iface.type = vpiInterface;

  EXPECT_EQ(vpi_iterate(vpiModport, VpiHandleOf(&iface)), nullptr);
}

// Edge for C3 reverse negative: an io decl with no enclosing modport reaches
// none through vpi_handle(vpiModport, iodecl). This is the reverse edge of the
// modport<->io-decl relationship reported empty - the parent lookup returns
// NULL when no modport parent is recorded, a different reference object (an io
// decl) and relation than the missing-interface case above.
TEST_F(Modport, IoDeclWithoutEnclosingModportReachesNone) {
  VpiObject io_decl;
  io_decl.type = vpiIODecl;

  EXPECT_EQ(vpi_handle(vpiModport, VpiHandleOf(&io_decl)), nullptr);
}

// An interface declaring two modports, the second naming as an input a port
// the first names as an output, instantiated once, run with a PLI application
// registered.
class ModportsOfARun : public VpiDesignRun {
 protected:
  static constexpr const char* kTwoModports =
      "interface ifc; logic a, b;\n"
      "  modport mp(input a, output b);\n"
      "  modport mq(input b);\n"
      "endinterface\n"
      "module top; ifc i0(); endmodule\n";

  // The names of the objects of `type` `ref` reaches, in the order they are
  // scanned.
  static std::vector<std::string> ScannedNames(int type, vpiHandle ref) {
    std::vector<std::string> names;
    vpiHandle it = vpi_iterate(type, ref);
    if (it == nullptr) return names;
    while (vpiHandle obj = vpi_scan(it)) {
      names.emplace_back(vpi_get_str(vpiName, obj));
    }
    return names;
  }

  // The object of `type` named `name` that `ref` reaches.
  static vpiHandle Named(int type, vpiHandle ref, const std::string& name) {
    vpiHandle it = vpi_iterate(type, ref);
    if (it == nullptr) return nullptr;
    while (vpiHandle obj = vpi_scan(it)) {
      if (name == vpi_get_str(vpiName, obj)) return obj;
    }
    return nullptr;
  }

  static vpiHandle Instance() {
    return vpi_handle_by_name(VpiText("top.i0"), nullptr);
  }
};

// §37.7: an interface instance reaches a modport per modport its interface
// declares, each named as it was declared, in the order they were written.
TEST_F(ModportsOfARun, AnInterfaceInstanceIteratesItsModports) {
  Run(kTwoModports);
  EXPECT_EQ(ScannedNames(vpiModport, Instance()),
            (std::vector<std::string>{"mp", "mq"}));
}

// §37.7: a modport reaches back the interface instance it belongs to.
TEST_F(ModportsOfARun, AModportReachesItsInterfaceInstance) {
  Run(kTwoModports);
  vpiHandle mp = Named(vpiModport, Instance(), "mp");
  ASSERT_NE(mp, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiInterface, mp)), VpiObjectOf(Instance()));
}

// §37.7: a modport reaches an io decl per port it names, in the order they
// were written.
TEST_F(ModportsOfARun, AModportIteratesItsIoDecls) {
  Run(kTwoModports);
  EXPECT_EQ(ScannedNames(vpiIODecl, Named(vpiModport, Instance(), "mp")),
            (std::vector<std::string>{"a", "b"}));
  EXPECT_EQ(ScannedNames(vpiIODecl, Named(vpiModport, Instance(), "mq")),
            (std::vector<std::string>{"b"}));
}

// §37.13 detail 1 with §37.7: an io decl of a modport reports the direction
// that modport gave the port, so one port reads as an output through one
// modport and an input through another.
TEST_F(ModportsOfARun, AnIoDeclReportsItsModportsDirection) {
  Run(kTwoModports);
  vpiHandle mp = Named(vpiModport, Instance(), "mp");
  vpiHandle mq = Named(vpiModport, Instance(), "mq");
  EXPECT_EQ(vpi_get(vpiDirection, Named(vpiIODecl, mp, "a")), vpiInput);
  EXPECT_EQ(vpi_get(vpiDirection, Named(vpiIODecl, mp, "b")), vpiOutput);
  EXPECT_EQ(vpi_get(vpiDirection, Named(vpiIODecl, mq, "b")), vpiInput);
}

// §37.13 detail 1 with §37.7: an io decl of a modport's ref port reports
// vpiRef.
TEST_F(ModportsOfARun, AnIoDeclOfARefPortReportsVpiRef) {
  Run("interface ifc; logic a; modport mr(ref a); endinterface\n"
      "module top; ifc i0(); endmodule\n");
  vpiHandle mr = Named(vpiModport, Instance(), "mr");
  EXPECT_EQ(vpi_get(vpiDirection, Named(vpiIODecl, mr, "a")), vpiRef);
}

// §37.7: an io decl of a modport reaches back the modport it belongs to.
TEST_F(ModportsOfARun, AnIoDeclReachesItsModport) {
  Run(kTwoModports);
  vpiHandle mq = Named(vpiModport, Instance(), "mq");
  ASSERT_NE(mq, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiModport, Named(vpiIODecl, mq, "b"))),
            VpiObjectOf(mq));
}

// §37.7: a module instance has no modports.
TEST_F(ModportsOfARun, AModuleInstanceHasNoModports) {
  Run(kTwoModports);
  EXPECT_EQ(
      vpi_iterate(vpiModport, vpi_handle_by_name(VpiText("top"), nullptr)),
      nullptr);
}

}  // namespace
}  // namespace delta
