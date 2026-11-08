#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(InlineRandomControlVisibility, LocalMemberArgRejectedFromOutside) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  local rand int x;\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    C obj;\n"
      "    obj = new;\n"
      "    obj.randomize(x);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cannot change random mode of local member from outside its class", 8,
      "18.11"));
}

TEST(InlineRandomControlVisibility, ProtectedMemberArgRejectedFromOutside) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  protected rand int x;\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    C obj;\n"
      "    obj = new;\n"
      "    obj.randomize(x);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "cannot change random mode of protected member from outside its "
      "class hierarchy",
      8, "18.11"));
}

TEST(InlineRandomControlVisibility, PublicMemberArgAcceptedFromOutside) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand int x;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    C obj;\n"
             "    obj = new;\n"
             "    obj.randomize(x);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(InlineRandomControlVisibility, LocalMemberArgAcceptedWithinClassScope) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  local rand int x;\n"
             "  function int roll();\n"
             "    return this.randomize(x);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  int r;\n"
             "  initial begin\n"
             "    C obj;\n"
             "    obj = new;\n"
             "    r = obj.roll();\n"
             "  end\n"
             "endmodule\n"));
}

TEST(InlineRandomControlVisibility, ANameNoPropertyOfTheClassIsRejected) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand bit [3:0] x;\n"
             "endclass\n"
             "module m;\n"
             "  int nosuch;\n"
             "  initial begin\n"
             "    C obj;\n"
             "    obj = new;\n"
             "    void'(obj.randomize(nosuch));\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'nosuch' is no property of class 'C', so "
                            "randomize() cannot name it as a random variable",
                            9, "18.11"));
}

TEST(InlineRandomControlVisibility, AnInheritedPropertyAndNullAreAccepted) {
  EXPECT_TRUE(
      ElabOk("class B;\n"
             "  bit [3:0] y;\n"
             "endclass\n"
             "class C extends B;\n"
             "  rand bit [3:0] x;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    C obj;\n"
             "    obj = new;\n"
             "    void'(obj.randomize(y));\n"
             "    void'(obj.randomize(null));\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
