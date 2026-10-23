#include <gtest/gtest.h>

#include <cstddef>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

// §37.42 detail 2: a method call applied to a value that no plain variable of
// the scope holds is the call the value's type gives it, as one applied to
// such a variable is: a method of the class the value is a handle of, or a
// built-in method of the string, the enumeration or the array it is (detail
// 11).
class MethodCallsOnValues : public VpiDesignRun {
 protected:
  // The number of method func calls the block top.b holds as statements, each
  // checked to be unnamed (§37.60 detail 1) and no user's (detail 11).
  static std::size_t BuiltInCallsOfTheBlock() {
    std::size_t count = 0;
    for (vpiHandle call : ObjectsOf(vpiMethodFuncCall, By("top.b"))) {
      EXPECT_EQ(vpi_get_str(vpiName, call), nullptr);
      EXPECT_EQ(vpi_get(vpiUserDefn, call), 0);
      ++count;
    }
    return count;
  }

  // That the block top.b holds a method task call of the task `run` a class of
  // the design declares, which the call reaches (§37.42).
  static void ExpectTheBlockCallsRun() {
    vpiHandle call = CallOf(vpiMethodTaskCall, By("top.b"), "run");
    ASSERT_NE(call, nullptr);
    EXPECT_EQ(vpi_get(vpiUserDefn, call), 1);
  }
};

// §9.7 and §6.16: a built-in method's result takes the built-in methods of its
// kind, the enumeration process::status() returns and the string toupper()
// returns (#7719).
TEST_F(MethodCallsOnValues, ABuiltInMethodsResultTakesTheMethodsOfItsKind) {
  Run("module top; process p; string s = \"ab\";\n"
      "  initial begin : b\n"
      "    p = process::self();\n"
      "    void'(p.status().name());\n"
      "    void'(s.toupper().len());\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(BuiltInCallsOfTheBlock(), 2U);
}

// §13.4: the string a function or a class's method is declared to return takes
// the string's methods (#7719).
TEST_F(MethodCallsOnValues, ADeclaredStringResultTakesStringMethods) {
  Run("module top;\n"
      "  class K; function string get(); return \"k\"; endfunction endclass\n"
      "  function string f(); return \"f\"; endfunction\n"
      "  K k = new;\n"
      "  initial begin : b void'(f().len()); void'(k.get().len()); end\n"
      "endmodule\n");
  EXPECT_EQ(BuiltInCallsOfTheBlock(), 2U);
}

// §11.4.12.2: a concatenation of a string, and a multiple one, is a string
// (#7726).
TEST_F(MethodCallsOnValues, AStringConcatenationTakesStringMethods) {
  Run("module top; string s = \"ab\";\n"
      "  initial begin : b void'({s, \"x\"}.len()); void'({2{s}}.len()); end\n"
      "endmodule\n");
  EXPECT_EQ(BuiltInCallsOfTheBlock(), 2U);
}

// §6.24.1: a cast to string, or to an enumeration a typedef names, is a value
// of its casting type (#7726).
TEST_F(MethodCallsOnValues, ACastTakesTheMethodsOfItsCastingType) {
  Run("module top; typedef enum {A, B} e_t; int n = 5;\n"
      "  initial begin : b void'(string'(n).len()); void'(e_t'(1).name()); "
      "end\n"
      "endmodule\n");
  EXPECT_EQ(BuiltInCallsOfTheBlock(), 2U);
}

// §21.3.3: $sformatf returns a string (#7726).
TEST_F(MethodCallsOnValues, AStringSystemFunctionsResultTakesStringMethods) {
  Run("module top; int n = 5;\n"
      "  initial begin : b void'($sformatf(\"%0d\", n).len()); end\n"
      "endmodule\n");
  EXPECT_EQ(BuiltInCallsOfTheBlock(), 1U);
}

// §7.2: a class var a structure member's own structure member holds,
// s.inner.h, is reached through both structures (#7721).
TEST_F(MethodCallsOnValues, ANestedStructureMembersHandleTakesItsMethods) {
  Run("module top; class C; task run(); endtask endclass\n"
      "  typedef struct { int n; C h; } in_t;\n"
      "  typedef struct { int m; in_t inner; } out_t;\n"
      "  out_t s;\n"
      "  initial begin : b s.inner.h = new; s.inner.h.run(); end\n"
      "endmodule\n");
  ExpectTheBlockCallsRun();
}

// §9.3.4 and §23.6: a class var a named block declares, reached from another
// process through the block's name, b1.h, is a handle of its class (#7724).
TEST_F(MethodCallsOnValues, ANamedBlocksHandleReachedByNameTakesItsMethods) {
  Run("module top; class C; task run(); endtask endclass\n"
      "  initial begin begin : b1 static C h = new; static int n; n = 1; end "
      "end\n"
      "  initial begin : b #1; b1.h.run(); end\n"
      "endmodule\n");
  ExpectTheBlockCallsRun();
}

}  // namespace
}  // namespace delta
