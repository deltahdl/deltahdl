#include <gtest/gtest.h>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

// §37.42 details 2 and 11: a call of a built-in method of a string, an enum or
// an unpacked array (§6.16, §6.19.5, §7.5, §7.9, §7.10.2, §7.12) is a method
// func call applied to the value it is called on, and that value may be
// reached through members as well as named directly.
class BuiltInCallsThroughMembers : public VpiDesignRun {
 protected:
  // The first statement the block top.b holds.
  static vpiHandle FirstStatement() {
    vpiHandle stmts = vpi_iterate(vpiStmt, By("top.b"));
    if (stmts == nullptr) return nullptr;
    vpiHandle first = vpi_scan(stmts);
    vpi_release_handle(stmts);
    return first;
  }
};

// A queue member of a structure variable takes the queue's methods.
TEST_F(BuiltInCallsThroughMembers, AStructuresQueueMemberTakesItsMethods) {
  Run("module top; typedef struct { int q[$]; } s_t; s_t s;\n"
      "  initial begin : b s.q.delete(); end\n"
      "endmodule\n");
  vpiHandle call = FirstStatement();
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(vpi_get(vpiType, call), vpiMethodFuncCall);
  EXPECT_STREQ(vpi_get_str(vpiName, call), "delete");
}

// A queue property of a class takes them too, and a call of one within an
// expression is the method func call rather than an unnamed func call.
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

// A string property's methods are a string's (§6.16).
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

}  // namespace
}  // namespace delta
