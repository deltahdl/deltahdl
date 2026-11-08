#include <gtest/gtest.h>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class AliasStatement : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

TEST_F(AliasStatement, LhsAndRhsAreDistinctEdges) {
  VpiObject lhs;
  lhs.type = vpiRefObj;
  VpiObject rhs;
  rhs.type = vpiOperation;

  VpiObject alias_stmt;
  alias_stmt.type = vpiAliasStmt;
  alias_stmt.lhs = &lhs;
  alias_stmt.rhs = &rhs;

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLhs, VpiHandleOf(&alias_stmt))), &lhs);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiRhs, VpiHandleOf(&alias_stmt))), &rhs);
}

TEST_F(AliasStatement, EdgesAreScopedToTheAliasStatement) {
  VpiObject lhs;
  lhs.type = vpiRefObj;
  VpiObject rhs;
  rhs.type = vpiOperation;

  VpiObject not_alias;
  not_alias.type = vpiBegin;
  not_alias.lhs = &lhs;
  not_alias.rhs = &rhs;

  EXPECT_EQ(vpi_handle(vpiLhs, VpiHandleOf(&not_alias)), nullptr);
  EXPECT_EQ(vpi_handle(vpiRhs, VpiHandleOf(&not_alias)), nullptr);
}

TEST_F(AliasStatement, AliasStatementReachesTheInstanceItIsWrittenIn) {
  VpiObject module;
  module.type = vpiModule;

  VpiObject block;
  block.type = vpiNamedBegin;
  block.parent = &module;

  VpiObject alias_stmt;
  alias_stmt.type = vpiAliasStmt;
  alias_stmt.parent = &block;

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiInstance, VpiHandleOf(&alias_stmt))),
            &module);

  VpiObject package;
  package.type = vpiPackage;

  VpiObject package_alias;
  package_alias.type = vpiAliasStmt;
  package_alias.parent = &package;

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiInstance, VpiHandleOf(&package_alias))),
            &package);

  VpiObject orphan;
  orphan.type = vpiAliasStmt;

  EXPECT_EQ(vpi_handle(vpiInstance, VpiHandleOf(&orphan)), nullptr);
}

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

  VpiObject net;
  net.type = vpiNet;

  VpiObject module;
  module.type = vpiModule;
  module.children = {&alias_a, &net, &alias_b, &alias_c};

  vpiHandle it = vpi_iterate(vpiAliasStmt, VpiHandleOf(&module));
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(it)), &alias_a);
  EXPECT_EQ(VpiObjectOf(vpi_scan(it)), &alias_b);
  EXPECT_EQ(VpiObjectOf(vpi_scan(it)), &alias_c);
  EXPECT_EQ(vpi_scan(it), nullptr);

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiRhs, VpiHandleOf(&alias_a))), &d);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiRhs, VpiHandleOf(&alias_b))), &d);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiRhs, VpiHandleOf(&alias_c))), &d);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLhs, VpiHandleOf(&alias_a))), &a);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLhs, VpiHandleOf(&alias_b))), &b);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLhs, VpiHandleOf(&alias_c))), &c);
}

TEST_F(AliasStatement, InstanceWithNoAliasStatementIteratesNone) {
  VpiObject net;
  net.type = vpiNet;

  VpiObject module;
  module.type = vpiModule;
  module.children = {&net};

  EXPECT_EQ(vpi_iterate(vpiAliasStmt, VpiHandleOf(&module)), nullptr);
}

}  // namespace
}  // namespace delta
