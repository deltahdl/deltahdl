#include <gtest/gtest.h>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class BuiltInCallsThroughMembers : public VpiDesignRun {
 protected:
  static vpiHandle FirstStatement() {
    vpiHandle stmts = vpi_iterate(vpiStmt, By("top.b"));
    if (stmts == nullptr) return nullptr;
    vpiHandle first = vpi_scan(stmts);
    vpi_release_handle(stmts);
    return first;
  }
};

TEST_F(BuiltInCallsThroughMembers, AStructuresQueueMemberTakesItsMethods) {
  Run("module top; typedef struct { int q[$]; } s_t; s_t s;\n"
      "  initial begin : b s.q.delete(); end\n"
      "endmodule\n");
  vpiHandle call = FirstStatement();
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(vpi_get(vpiType, call), vpiMethodFuncCall);
  EXPECT_EQ(vpi_get_str(vpiName, call), nullptr);
}

TEST_F(BuiltInCallsThroughMembers, AClassQueuePropertysCallIsAMethodCall) {
  Run("module top; class C; int q[$]; endclass\n"
      "  C h = new; int r;\n"
      "  initial begin : b r = h.q.size(); end\n"
      "endmodule\n");
  vpiHandle assign = FirstStatement();
  ASSERT_NE(assign, nullptr);
  vpiHandle call = vpi_handle(vpiRhs, assign);
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(vpi_get(vpiType, call), vpiMethodFuncCall);
  EXPECT_STREQ(vpi_get_str(vpiName, call), "size");
}

TEST_F(BuiltInCallsThroughMembers, AClassStringPropertyTakesStringMethods) {
  Run("module top; class C; string str; endclass\n"
      "  C h = new; int r;\n"
      "  initial begin : b r = h.str.len(); end\n"
      "endmodule\n");
  vpiHandle assign = FirstStatement();
  ASSERT_NE(assign, nullptr);
  vpiHandle call = vpi_handle(vpiRhs, assign);
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(vpi_get(vpiType, call), vpiMethodFuncCall);
  EXPECT_STREQ(vpi_get_str(vpiName, call), "len");
}

TEST_F(BuiltInCallsThroughMembers, AnEnumConstantTakesTheEnumsMethods) {
  Run("module top; typedef enum {A, B} e_t;\n"
      "  initial begin : b void'(A.name()); end\n"
      "endmodule\n");
  vpiHandle call = FirstStatement();
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(vpi_get(vpiType, call), vpiMethodFuncCall);
  EXPECT_EQ(vpi_get_str(vpiName, call), nullptr);
  EXPECT_EQ(vpi_get(vpiUserDefn, call), 0);
}

}  // namespace
}  // namespace delta
