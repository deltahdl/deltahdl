#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.76 Alias statement: the object model diagram for a net alias statement.
// The clause carries no BNF, no numbered Details, and no 'shall' sentences - it
// is the diagram alone, plus an informative example (alias a=b=c=d yields three
// aliases). The diagram draws two labelled expression edges from an alias
// statement: it reaches its left-hand side expression through vpiLhs and its
// right-hand side expression through vpiRhs. Its remaining edge, the
// bidirectional structural link to the enclosing instance, carries no relation
// tag of its own and is left to the generic traversal.
//
// Each labelled edge needs dedicated production code because both sides are
// expression kinds (a reference, an operation, a concatenation, ...), not the
// vpiLhs / vpiRhs relation tags, so the generic child walk in VpiHandleC -
// which matches by exact relation tag - cannot find them; they are held as the
// designated lhs / rhs pointers shared with the §37.79 assignment family. These
// tests observe the production path applying the rule through the public
// vpi_handle dispatch.

// The fixture installs a context so the public VpiHandleC entry point runs its
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

  EXPECT_EQ(VpiHandleC(vpiLhs, &alias_stmt), &lhs);
  EXPECT_EQ(VpiHandleC(vpiRhs, &alias_stmt), &rhs);
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

  EXPECT_EQ(VpiHandleC(vpiLhs, &not_alias), nullptr);
  EXPECT_EQ(VpiHandleC(vpiRhs, &not_alias), nullptr);
}

}  // namespace
}  // namespace delta
