#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.76 Alias statement: the object model diagram for a net alias statement.
// The clause carries no BNF, no numbered Details, and no 'shall' sentences - it
// is the diagram alone, plus an informative example (alias a=b=c=d yields three
// aliases, d being the right-hand side of all three). The diagram draws four
// arrows. Two are labelled: an alias statement reaches its left-hand side
// expression through vpiLhs and its right-hand side expression through vpiRhs.
// Two are untagged, and they run between the statement and the dotted
// `instance` enclosure in opposite directions and with different arrowheads: a
// single arrow from the statement to the instance and a double arrow from the
// instance back. §37.4.3 makes an untagged relation's type the target
// enclosure's words with "vpi" in front and a single arrow a vpi_handle() while
// a double one is a vpi_iterate(), so the pair is vpi_handle(vpiInstance,
// alias_stmt) - the instance the statement is written in - and
// vpi_iterate(vpiAliasStmt, instance) - every alias statement that instance
// holds. They are two relations rather than one bidirectional link, and only
// one of them is answered by a child walk: §37.10 makes `instance` a class
// grouping the package, module, interface and program kinds, so nothing carries
// vpiInstance for its own type and the instance is not a child but an enclosing
// scope, while `alias stmt` is drawn as an object definition and so is a kind
// an object carries.
//
// Each labelled edge needs dedicated production code because both sides are
// expression kinds (a reference, an operation, a concatenation, ...), not the
// vpiLhs / vpiRhs relation tags, so the generic child walk in vpi_handle -
// which matches by exact relation tag - cannot find them; they are held as the
// designated lhs / rhs pointers shared with the §37.79 assignment family. These
// tests observe the production path for all four arrows through the public
// vpi_handle and vpi_iterate dispatch.

// The fixture installs a context so the public vpi_handle entry point runs its
// real dispatch over the test objects.
class AliasStatement : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

// Both edges on one alias statement: vpiLhs and vpiRhs are distinct designated
// pointers, so the dispatch returns the left-hand expression for vpiLhs and the
// right-hand expression for vpiRhs - the alias statement's two labelled diagram
// edges observed together and kept apart.
TEST_F(AliasStatement, LhsAndRhsAreDistinctEdges) {
  VpiObject lhs;
  lhs.type = vpiRefObj;
  VpiObject rhs;
  rhs.type = vpiOperation;

  VpiObject alias_stmt;
  alias_stmt.type = vpiAliasStmt;
  alias_stmt.lhs = &lhs;
  alias_stmt.rhs = &rhs;

  EXPECT_EQ(vpi_handle(vpiLhs, &alias_stmt), &lhs);
  EXPECT_EQ(vpi_handle(vpiRhs, &alias_stmt), &rhs);
}

// Gating: the alias statement's vpiLhs / vpiRhs branches are scoped to the
// alias statement kind, so they do not surface a designated lhs / rhs pointer
// for an object of some other kind. A non-alias object with those pointers set
// is left to the generic traversal, which matches by exact relation tag and
// reports null.
TEST_F(AliasStatement, EdgesAreScopedToTheAliasStatement) {
  VpiObject lhs;
  lhs.type = vpiRefObj;
  VpiObject rhs;
  rhs.type = vpiOperation;

  VpiObject not_alias;
  not_alias.type = vpiBegin;  // not an alias statement
  not_alias.lhs = &lhs;
  not_alias.rhs = &rhs;

  EXPECT_EQ(vpi_handle(vpiLhs, &not_alias), nullptr);
  EXPECT_EQ(vpi_handle(vpiRhs, &not_alias), nullptr);
}

// The untagged single arrow to `instance`: an alias statement reaches the
// instance it is written in through vpi_handle(vpiInstance, ...). §37.10 makes
// that a walk outward to the nearest enclosing package, module, interface or
// program, so an intervening non-instance scope - a named begin, say - does not
// stop it and is not mistaken for the instance.
TEST_F(AliasStatement, AliasStatementReachesTheInstanceItIsWrittenIn) {
  VpiObject module;
  module.type = vpiModule;

  VpiObject block;  // a non-instance scope between the statement and the module
  block.type = vpiNamedBegin;
  block.parent = &module;

  VpiObject alias_stmt;
  alias_stmt.type = vpiAliasStmt;
  alias_stmt.parent = &block;

  EXPECT_EQ(vpi_handle(vpiInstance, &alias_stmt), &module);

  // An alias statement written in a package reaches that package: the arrow is
  // drawn to the class, so every kind it groups answers it.
  VpiObject package;
  package.type = vpiPackage;

  VpiObject package_alias;
  package_alias.type = vpiAliasStmt;
  package_alias.parent = &package;

  EXPECT_EQ(vpi_handle(vpiInstance, &package_alias), &package);

  // One enclosed by no instance at all reaches none.
  VpiObject orphan;
  orphan.type = vpiAliasStmt;

  EXPECT_EQ(vpi_handle(vpiInstance, &orphan), nullptr);
}

// The untagged double arrow back from `instance`: an instance reaches every
// alias statement it holds through vpi_iterate(vpiAliasStmt, ...), in order,
// and the children of other kinds are not among them. The three statements here
// are the clause's own example, "alias a=b=c=d", which it says yields three
// aliases with d the right-hand side for all: each has its own left-hand side
// and all three share one right-hand side.
TEST_F(AliasStatement, InstanceIteratesTheAliasStatementsItHolds) {
  VpiObject a;
  a.type = vpiRefObj;
  VpiObject b;
  b.type = vpiRefObj;
  VpiObject c;
  c.type = vpiRefObj;
  VpiObject d;
  d.type = vpiRefObj;

  VpiObject alias_a;
  alias_a.type = vpiAliasStmt;
  alias_a.lhs = &a;
  alias_a.rhs = &d;
  VpiObject alias_b;
  alias_b.type = vpiAliasStmt;
  alias_b.lhs = &b;
  alias_b.rhs = &d;
  VpiObject alias_c;
  alias_c.type = vpiAliasStmt;
  alias_c.lhs = &c;
  alias_c.rhs = &d;

  VpiObject net;  // a child of another kind, which the iteration steps over
  net.type = vpiNet;

  VpiObject module;
  module.type = vpiModule;
  module.children = {&alias_a, &net, &alias_b, &alias_c};

  vpiHandle it = vpi_iterate(vpiAliasStmt, &module);
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(vpi_scan(it), &alias_a);
  EXPECT_EQ(vpi_scan(it), &alias_b);
  EXPECT_EQ(vpi_scan(it), &alias_c);
  EXPECT_EQ(vpi_scan(it), nullptr);

  // The example's right-hand side is one expression for all three, and each
  // statement keeps its own left-hand side.
  EXPECT_EQ(vpi_handle(vpiRhs, &alias_a), &d);
  EXPECT_EQ(vpi_handle(vpiRhs, &alias_b), &d);
  EXPECT_EQ(vpi_handle(vpiRhs, &alias_c), &d);
  EXPECT_EQ(vpi_handle(vpiLhs, &alias_a), &a);
  EXPECT_EQ(vpi_handle(vpiLhs, &alias_b), &b);
  EXPECT_EQ(vpi_handle(vpiLhs, &alias_c), &c);
}

// An instance holding no alias statement iterates none: the relation reports
// nothing rather than surfacing the children of other kinds it does hold.
TEST_F(AliasStatement, InstanceWithNoAliasStatementIteratesNone) {
  VpiObject net;
  net.type = vpiNet;

  VpiObject module;
  module.type = vpiModule;
  module.children = {&net};

  EXPECT_EQ(vpi_iterate(vpiAliasStmt, &module), nullptr);
}

}  // namespace
}  // namespace delta
