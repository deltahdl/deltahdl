#include <gtest/gtest.h>

#include <string>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class LookupByNameOfARun : public VpiDesignRun {
 protected:
  static vpiHandle In(const std::string& name, vpiHandle scope) {
    return vpi_handle_by_name(VpiText(name.c_str()), scope);
  }

  static std::string FullNameIn(const std::string& name, vpiHandle scope) {
    vpiHandle obj = In(name, scope);
    return obj == nullptr ? "" : vpi_get_str(vpiFullName, obj);
  }
};

constexpr const char* kNested =
    "module sub; int x = 1; endmodule\n"
    "module top; int t = 2; sub u(); initial $noop; endmodule\n";

TEST_F(LookupByNameOfARun, ANameFromTheTopReachesANestedObject) {
  Run(kNested);
  EXPECT_EQ(FullNameIn("top.u.x", nullptr), "top.u.x");
  EXPECT_EQ(FullNameIn("top.t", nullptr), "top.t");
  EXPECT_EQ(FullNameIn("top.u", nullptr), "top.u");
}

TEST_F(LookupByNameOfARun, DISABLED_ANullScopeFindsNoSimpleNameBelowTheTop) {
  Run(kNested);
  ASSERT_NE(By("top.u"), nullptr);
  EXPECT_EQ(In("u", nullptr), nullptr);
  EXPECT_EQ(In("t", nullptr), nullptr);
  EXPECT_EQ(In("x", nullptr), nullptr);
}

TEST_F(LookupByNameOfARun, DISABLED_ANullScopeFindsNoPathStartingBelowTheTop) {
  Run(kNested);
  ASSERT_NE(By("top.u.x"), nullptr);
  EXPECT_EQ(In("u.x", nullptr), nullptr);
}

TEST_F(LookupByNameOfARun, AHierarchicalNameIsReadRelativeToItsScope) {
  Run(kNested);
  vpiHandle top = By("top");
  ASSERT_NE(top, nullptr);
  EXPECT_EQ(FullNameIn("u.x", top), "top.u.x");
  EXPECT_EQ(FullNameIn("u", top), "top.u");
}

TEST_F(LookupByNameOfARun, AScopeFindsNothingOfTheScopeAroundIt) {
  Run(kNested);
  vpiHandle u = By("top.u");
  ASSERT_NE(u, nullptr);
  EXPECT_EQ(FullNameIn("x", u), "top.u.x");
  EXPECT_EQ(In("t", u), nullptr);
  EXPECT_EQ(In("top", u), nullptr);
}

TEST_F(LookupByNameOfARun, AFullNameGivenWithAScopeIsSoughtInsideIt) {
  Run(kNested);
  vpiHandle top = By("top");
  ASSERT_NE(top, nullptr);
  EXPECT_EQ(In("top.u.x", top), nullptr);
  EXPECT_EQ(In("top.t", top), nullptr);
}

constexpr const char* kScopes =
    "package pk; int pv = 1; endpackage\n"
    "interface ifc; int iv = 2; endinterface\n"
    "module top; int mv = 3; ifc i();\n"
    "  task automatic tk; int tv; endtask\n"
    "  function automatic int fn; int fv; return 0; endfunction\n"
    "  initial begin : blk int bv; $noop; end\n"
    "endmodule\n";

TEST_F(LookupByNameOfARun, AnInterfaceInstanceScopeConfinesTheSearch) {
  Run(kScopes);
  vpiHandle i = By("top.i");
  ASSERT_NE(i, nullptr);
  EXPECT_EQ(FullNameIn("iv", i), "top.i.iv");
  EXPECT_EQ(In("mv", i), nullptr);
}

TEST_F(LookupByNameOfARun, ANamedBlockScopeConfinesTheSearch) {
  Run(kScopes);
  vpiHandle blk = By("top.blk");
  ASSERT_NE(blk, nullptr);
  EXPECT_EQ(FullNameIn("bv", blk), "top.blk.bv");
  EXPECT_EQ(In("mv", blk), nullptr);
}

TEST_F(LookupByNameOfARun, ATaskOrFunctionScopeConfinesTheSearch) {
  Run(kScopes);
  vpiHandle tk = By("top.tk");
  vpiHandle fn = By("top.fn");
  ASSERT_NE(tk, nullptr);
  ASSERT_NE(fn, nullptr);
  EXPECT_EQ(FullNameIn("tv", tk), "top.tk.tv");
  EXPECT_EQ(In("mv", tk), nullptr);
  EXPECT_EQ(FullNameIn("fv", fn), "top.fn.fv");
  EXPECT_EQ(In("mv", fn), nullptr);
}

TEST_F(LookupByNameOfARun, APackageScopeConfinesTheSearch) {
  Run(kScopes);
  vpiHandle pk = By("pk");
  ASSERT_NE(pk, nullptr);
  EXPECT_EQ(FullNameIn("pv", pk), "pk::pv");
  EXPECT_EQ(In("mv", pk), nullptr);
  EXPECT_EQ(In("pv", By("top")), nullptr);
}

TEST_F(LookupByNameOfARun, ATaskAndAFunctionAreFoundByTheirNames) {
  Run(kScopes);
  EXPECT_EQ(vpi_get(vpiType, By("top.tk")), vpiTask);
  EXPECT_EQ(vpi_get(vpiType, By("top.fn")), vpiFunction);
}

TEST_F(LookupByNameOfARun, AProgramInstanceIsFoundByItsName) {
  Run("program prg; int gv; endprogram\n"
      "module top; prg g(); initial $noop; endmodule\n");
  vpiHandle g = By("top.g");
  ASSERT_NE(g, nullptr);
  EXPECT_EQ(vpi_get(vpiType, g), vpiProgram);
  EXPECT_STREQ(vpi_get_str(vpiFullName, g), "top.g");
}

}  // namespace
}  // namespace delta
