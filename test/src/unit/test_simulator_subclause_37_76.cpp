#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <tuple>
#include <vector>

#include "fixture_vpi_run.h"
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

class AliasesOfARun : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    Run("interface ifc; wire a, b; alias a = b; endinterface\n"
        "module top; wire [7:0] w, v, u, k; wire [3:0] p, r, s, t, r2, s2;\n"
        "  wire x, y, a, b; ifc i0();\n"
        "  alias w[0] = x;\n"
        "  alias w[7:4] = p;\n"
        "  alias {r, s} = v;\n"
        "  alias y = w[1];\n"
        "  alias t = u[3:0];\n"
        "  alias k = {r2, s2};\n"
        "  if (1) begin : g wire a, b; alias a = b; end\n"
        "  for (genvar n = 0; n < 2; n++) begin : gl wire a, b; alias a = b; "
        "end\n"
        "endmodule\n");
  }

  static vpiHandle AliasAt(size_t n) {
    const std::vector<vpiHandle> kAliases = ObjectsOf(vpiAliasStmt, By("top"));
    return n < kAliases.size() ? kAliases[n] : nullptr;
  }

  static vpiHandle SideOf(int side, size_t n) {
    vpiHandle alias = AliasAt(n);
    return alias == nullptr ? nullptr : vpi_handle(side, alias);
  }

  static void ExpectSelectOf(vpiHandle select, int kind, const char* net) {
    ASSERT_NE(select, nullptr) << net;
    EXPECT_EQ(vpi_get(vpiType, select), kind) << net;
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, select)),
              VpiObjectOf(By(std::string("top.") + net)))
        << net;
  }

  static vpiHandle AliasJoining(const std::string& lhs) {
    for (const char* owner : {"top", "top.g", "top.gl[0]", "top.gl[1]"}) {
      for (vpiHandle alias : ObjectsOf(vpiAliasStmt, By(owner))) {
        if (VpiObjectOf(vpi_handle(vpiLhs, alias)) == VpiObjectOf(By(lhs))) {
          return alias;
        }
      }
    }
    return nullptr;
  }
};

TEST_F(AliasesOfARun, EachStatementOfAModuleIsAnAliasStatement) {
  const std::vector<vpiHandle> kAliases = ObjectsOf(vpiAliasStmt, By("top"));
  ASSERT_GE(kAliases.size(), 6U);
  for (vpiHandle alias : kAliases) {
    EXPECT_EQ(vpi_get(vpiType, alias), vpiAliasStmt);
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiInstance, alias)),
              VpiObjectOf(By("top")));
  }
}

TEST_F(AliasesOfARun, ABitSelectSideIsABitOfItsNet) {
  ExpectSelectOf(SideOf(vpiLhs, 0), vpiNetBit, "w");
  EXPECT_EQ(IntegerOf(vpi_handle(vpiIndex, SideOf(vpiLhs, 0))), 0);
  EXPECT_EQ(VpiObjectOf(SideOf(vpiRhs, 0)), VpiObjectOf(By("top.x")));
  ExpectSelectOf(SideOf(vpiRhs, 3), vpiNetBit, "w");
  EXPECT_EQ(IntegerOf(vpi_handle(vpiIndex, SideOf(vpiRhs, 3))), 1);
  EXPECT_EQ(VpiObjectOf(SideOf(vpiLhs, 3)), VpiObjectOf(By("top.y")));
}

TEST_F(AliasesOfARun, APartSelectSideIsAPartSelectOfItsNet) {
  ExpectSelectOf(SideOf(vpiLhs, 1), vpiPartSelect, "w");
  EXPECT_EQ(IntegerOf(vpi_handle(vpiLeftRange, SideOf(vpiLhs, 1))), 7);
  EXPECT_EQ(IntegerOf(vpi_handle(vpiRightRange, SideOf(vpiLhs, 1))), 4);
  ExpectSelectOf(SideOf(vpiRhs, 4), vpiPartSelect, "u");
  EXPECT_EQ(IntegerOf(vpi_handle(vpiLeftRange, SideOf(vpiRhs, 4))), 3);
  EXPECT_EQ(IntegerOf(vpi_handle(vpiRightRange, SideOf(vpiRhs, 4))), 0);
}

TEST_F(AliasesOfARun, AConcatenationSideIsAConcatenationOfItsNets) {
  for (const auto& [side, n, first, second] :
       std::vector<std::tuple<int, size_t, const char*, const char*>>{
           {vpiLhs, 2, "top.r", "top.s"}, {vpiRhs, 5, "top.r2", "top.s2"}}) {
    vpiHandle concat = SideOf(side, n);
    EXPECT_EQ(OpOf(concat), vpiConcatOp) << n;
    const std::vector<vpiHandle> kParts = OperandsOf(concat);
    ASSERT_EQ(kParts.size(), 2U) << n;
    EXPECT_EQ(VpiObjectOf(kParts[0]), VpiObjectOf(By(first))) << n;
    EXPECT_EQ(VpiObjectOf(kParts[1]), VpiObjectOf(By(second))) << n;
  }
}

TEST_F(AliasesOfARun, AnInterfaceAliasReachesItsSidesAndItsInstance) {
  vpiHandle ifc = By("top.i0");
  const std::vector<vpiHandle> kAliases = ObjectsOf(vpiAliasStmt, ifc);
  ASSERT_EQ(kAliases.size(), 1U);
  EXPECT_EQ(vpi_get(vpiType, kAliases[0]), vpiAliasStmt);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiInstance, kAliases[0])),
            VpiObjectOf(ifc));
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiLhs, kAliases[0])),
            VpiObjectOf(By("top.i0.a")));
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiRhs, kAliases[0])),
            VpiObjectOf(By("top.i0.b")));
}

TEST_F(AliasesOfARun, AGenerateBlockAliasJoinsTheBlocksOwnNets) {
  for (const char* block : {"top.g", "top.gl[0]", "top.gl[1]"}) {
    const std::string kScope(block);
    vpiHandle alias = AliasJoining(kScope + ".a");
    ASSERT_NE(alias, nullptr) << block;
    EXPECT_EQ(vpi_get(vpiType, alias), vpiAliasStmt) << block;
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiRhs, alias)),
              VpiObjectOf(By(kScope + ".b")))
        << block;
    EXPECT_NE(VpiObjectOf(vpi_handle(vpiRhs, alias)), VpiObjectOf(By("top.b")))
        << block;
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiInstance, alias)),
              VpiObjectOf(By("top")))
        << block;
  }
}

}  // namespace
}  // namespace delta
