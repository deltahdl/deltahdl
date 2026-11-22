#include <gtest/gtest.h>

#include <string>
#include <utility>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class ReturnStatement : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

TEST_F(ReturnStatement, ReturnReachesReturnedValueAmongOtherChildren) {
  VpiObject other;
  other.type = vpiNullStmt;
  VpiObject value;
  value.type = vpiOperation;

  VpiObject return_stmt;
  return_stmt.type = vpiReturnStmt;
  return_stmt.children = {&other, &value};

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiCondition, VpiHandleOf(&return_stmt))),
            &value);
}

TEST_F(ReturnStatement, EachExpressionKindAValueCarriesIsReached) {
  for (int value_kind : {vpiOperation, vpiConstant, vpiRefObj, vpiFuncCall,
                         vpiParameter, vpiBitSelect}) {
    VpiObject value;
    value.type = value_kind;

    VpiObject return_stmt;
    return_stmt.type = vpiReturnStmt;
    return_stmt.children = {&value};

    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiCondition, VpiHandleOf(&return_stmt))),
              &value)
        << "value kind " << value_kind;
  }
}

TEST_F(ReturnStatement, VoidReturnReportsNoValue) {
  VpiObject return_stmt;
  return_stmt.type = vpiReturnStmt;

  EXPECT_EQ(vpi_handle(vpiCondition, VpiHandleOf(&return_stmt)), nullptr);
}

TEST_F(ReturnStatement, ReturnConditionRelationIsScopedToReturnStatements) {
  VpiObject expr;
  expr.type = vpiOperation;

  VpiObject not_a_return;
  not_a_return.type = vpiBegin;
  not_a_return.children = {&expr};

  EXPECT_EQ(vpi_handle(vpiCondition, VpiHandleOf(&not_a_return)), nullptr);
}

TEST(ReturnModel, NoObjectHasNoReturnExpression) {
  EXPECT_EQ(VpiReturnConditionExpr(nullptr), nullptr);
}

class ReturnsOfARun : public VpiDesignRun {
 protected:
  static std::string FunctionsOf(const std::string& p) {
    return "function int " + p + "k(int a); return a; endfunction\n" +
           "function int " + p + "c(int a); return 7; endfunction\n" +
           "function int " + p + "o(int a); return a + 1; endfunction\n" +
           "function int " + p + "r(int a); return a; endfunction\n" +
           "function int " + p + "f(int a); return " + p +
           "k(a); endfunction\n";
  }

  void RunEveryPlace() {
    Run(FunctionsOf("u") + "package pk;\n" + FunctionsOf("p") +
        "endpackage\nmodule top;\n" + FunctionsOf("m") +
        "  if (1) begin : g\n" + FunctionsOf("g") + "  end\n  class C;\n" +
        FunctionsOf("c") +
        "  endclass\n"
        "  int v;\n"
        "  function int mv(); return v; endfunction\n"
        "  function int mb(); begin return 4; end endfunction\n"
        "  task tk; return; endtask\n"
        "  function void fv; return; endfunction\n"
        "endmodule\n");
  }

  static vpiHandle UnitFunction(const char* name) {
    vpiHandle found = nullptr;
    vpiHandle it = vpi_iterate(vpiPackage, nullptr);
    while (vpiHandle pkg = it == nullptr ? nullptr : vpi_scan(it)) {
      if (vpiHandle f = Named(vpiTaskFunc, pkg, name)) found = f;
    }
    return found;
  }

  static vpiHandle FunctionIn(const std::string& place, const std::string& n) {
    if (place == "u") return UnitFunction(n.c_str());
    if (place == "p") return Named(vpiTaskFunc, By("pk"), n);
    if (place == "g") return Named(vpiTaskFunc, By("top.g"), n);
    if (place == "c") {
      return Named(vpiMethods, Named(vpiClassDefn, By("top"), "C"), n);
    }
    return Named(vpiTaskFunc, By("top"), n);
  }

  static vpiHandle ReturnOf(vpiHandle fn) {
    vpiHandle stmt = fn == nullptr ? nullptr : vpi_handle(vpiStmt, fn);
    if (stmt == nullptr) return nullptr;
    EXPECT_EQ(vpi_get(vpiType, stmt), vpiReturnStmt);
    EXPECT_STREQ(vpi_get_str(vpiType, stmt), "vpiReturnStmt");
    return stmt;
  }

  static const std::vector<std::pair<std::string, const char*>>& Places() {
    static const std::vector<std::pair<std::string, const char*>> kPlaces{
        {"u", "compilation unit"},
        {"p", "package"},
        {"m", "module"},
        {"g", "generate block"},
        {"c", "class method"}};
    return kPlaces;
  }
};

TEST_F(ReturnsOfARun, AReturnInEachPlaceReachesEachKindOfValue) {
  RunEveryPlace();
  for (const auto& [p, where] : Places()) {
    vpiHandle c = ReturnOf(FunctionIn(p, p + "c"));
    ASSERT_NE(c, nullptr) << where;
    vpiHandle constant = vpi_handle(vpiCondition, c);
    ASSERT_NE(constant, nullptr) << where;
    EXPECT_EQ(vpi_get(vpiType, constant), vpiConstant) << where;
    vpiHandle o = ReturnOf(FunctionIn(p, p + "o"));
    ASSERT_NE(o, nullptr) << where;
    vpiHandle op = vpi_handle(vpiCondition, o);
    ASSERT_NE(op, nullptr) << where;
    EXPECT_EQ(vpi_get(vpiType, op), vpiOperation) << where;
    EXPECT_EQ(vpi_get(vpiOpType, op), vpiAddOp) << where;
    vpiHandle f = ReturnOf(FunctionIn(p, p + "f"));
    ASSERT_NE(f, nullptr) << where;
    vpiHandle call = vpi_handle(vpiCondition, f);
    ASSERT_NE(call, nullptr) << where;
    EXPECT_EQ(vpi_get(vpiType, call), vpiFuncCall) << where;
    EXPECT_EQ(vpi_get_str(vpiName, call), p + "k") << where;
  }
}

TEST_F(ReturnsOfARun, DISABLED_AReturnedVariableInEachPlaceIsReached) {
  RunEveryPlace();
  for (const auto& [p, where] : Places()) {
    vpiHandle r = ReturnOf(FunctionIn(p, p + "r"));
    ASSERT_NE(r, nullptr) << where;
    vpiHandle ref = vpi_handle(vpiCondition, r);
    ASSERT_NE(ref, nullptr) << where;
    EXPECT_STREQ(vpi_get_str(vpiName, ref), "a") << where;
  }
  vpiHandle v = ReturnOf(Named(vpiTaskFunc, By("top"), "mv"));
  ASSERT_NE(v, nullptr);
  vpiHandle var = vpi_handle(vpiCondition, v);
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(VpiObjectOf(var), VpiObjectOf(Named(vpiVariables, By("top"), "v")));
}

TEST_F(ReturnsOfARun, TheValueIsASingleHandleAndNotAnIteration) {
  RunEveryPlace();
  for (const auto& [p, where] : Places()) {
    vpiHandle o = ReturnOf(FunctionIn(p, p + "o"));
    ASSERT_NE(o, nullptr) << where;
    EXPECT_NE(vpi_handle(vpiCondition, o), nullptr) << where;
    EXPECT_EQ(vpi_iterate(vpiCondition, o), nullptr) << where;
  }
}

TEST_F(ReturnsOfARun, ABareReturnOfATaskOrVoidFunctionHasNoValue) {
  RunEveryPlace();
  for (const char* name : {"tk", "fv"}) {
    vpiHandle bare = ReturnOf(Named(vpiTaskFunc, By("top"), name));
    ASSERT_NE(bare, nullptr) << name;
    EXPECT_EQ(vpi_handle(vpiCondition, bare), nullptr) << name;
  }
}

TEST_F(ReturnsOfARun, AReturnInsideABeginOfABodyIsAReturnStatement) {
  RunEveryPlace();
  vpiHandle fn = Named(vpiTaskFunc, By("top"), "mb");
  ASSERT_NE(fn, nullptr);
  vpiHandle block = vpi_handle(vpiStmt, fn);
  ASSERT_NE(block, nullptr);
  EXPECT_EQ(vpi_get(vpiType, block), vpiBegin);
  EXPECT_EQ(KindsOf(vpiStmt, block), std::vector<int>{vpiReturnStmt});
  vpiHandle it = vpi_iterate(vpiStmt, block);
  ASSERT_NE(it, nullptr);
  vpiHandle ret = vpi_scan(it);
  ASSERT_NE(ret, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiType, ret), "vpiReturnStmt");
  vpiHandle value = vpi_handle(vpiCondition, ret);
  ASSERT_NE(value, nullptr);
  EXPECT_EQ(vpi_get(vpiType, value), vpiConstant);
}

}  // namespace
}  // namespace delta
