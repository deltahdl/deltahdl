#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

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

  EXPECT_STREQ(vpi_get_str(vpiName, &modport), "phy");
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
  vpiHandle iter = vpi_iterate(vpiModport, &iface);
  ASSERT_NE(iter, nullptr);
  EXPECT_EQ(vpi_scan(iter), &modport);
  EXPECT_EQ(vpi_scan(iter), nullptr);

  // Reverse: the modport reaches its enclosing interface.
  EXPECT_EQ(vpi_handle(vpiInterface, &modport), &iface);
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
  vpiHandle iter = vpi_iterate(vpiIODecl, &modport);
  ASSERT_NE(iter, nullptr);
  int count = 0;
  while (vpi_scan(iter) != nullptr) ++count;
  EXPECT_EQ(count, 2);

  // Reverse: an io decl reaches its enclosing modport.
  EXPECT_EQ(vpi_handle(vpiModport, &in_decl), &modport);
}

// Edge for C3 forward: a modport that groups no io declarations yields no
// iterator. The generic iteration reports an empty walk as a null handle rather
// than an iterator that scans nothing - the empty-iterator branch, distinct
// from the populated walk above.
TEST_F(Modport, ModportWithNoIoDeclsIteratesToNone) {
  VpiObject modport;
  modport.type = vpiModport;

  EXPECT_EQ(vpi_iterate(vpiIODecl, &modport), nullptr);
}

// Edge for C2 reverse: a modport with no enclosing interface reaches none
// through vpi_handle(vpiInterface, modport) - the reverse parent lookup reports
// NULL when no interface parent is recorded, distinct from the matching-parent
// path above.
TEST_F(Modport, ModportWithoutEnclosingInterfaceReachesNone) {
  VpiObject modport;
  modport.type = vpiModport;

  EXPECT_EQ(vpi_handle(vpiInterface, &modport), nullptr);
}

}  // namespace
}  // namespace delta
