#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// 18.7: a name of an inline constraint block qualified by this binds to the
// class of the object randomize() with is called on, and it is an error
// where that class declares no member of the name.
TEST(InlineConstraints, AThisNameTheClassLacksIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand bit [3:0] x;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    static C c = new;\n"
             "    void'(c.randomize() with { x < this.nosuch + 4; });\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'this.nosuch' names no member of class 'C', the "
                            "class randomize() with is called on",
                            7, "18.7"));
}

// 18.7: a name qualified by super binds to the class the randomized object's
// class extends, so super.x is an error where only the derived class D
// declares x and its base B does not.
TEST(InlineConstraints, ASuperNameTheBaseLacksIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class B;\n"
             "  rand bit [3:0] y;\n"
             "endclass\n"
             "class D extends B;\n"
             "  rand bit [3:0] x;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    static D d = new;\n"
             "    void'(d.randomize() with { y < super.x; });\n"
             "  end\n"
             "endmodule\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'super.x' names no member of class 'B', the "
                            "class randomize() with is called on extends",
                            10, "18.7"));
}

// 18.7: this.x, which the class declares, this.y, which it inherits, and
// super.y, which its base declares, all resolve, and the block elaborates.
TEST(InlineConstraints, ThisAndSuperNamesTheClassesDeclareElaborate) {
  EXPECT_TRUE(
      ElabOk("class B;\n"
             "  rand bit [3:0] y;\n"
             "endclass\n"
             "class D extends B;\n"
             "  rand bit [3:0] x;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    static D d = new;\n"
             "    void'(d.randomize() with { this.x < this.y; super.y > 1; "
             "});\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
