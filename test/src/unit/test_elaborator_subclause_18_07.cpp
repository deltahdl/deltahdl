#include <gtest/gtest.h>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

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

TEST(InlineConstraints, ThisAndSuperEnumLiteralsElaborate) {
  EXPECT_TRUE(
      ElabOk("class B;\n"
             "  rand enum bit [1:0] {COLD, HOT} t;\n"
             "endclass\n"
             "class D extends B;\n"
             "  typedef enum bit [1:0] {IDLE, BUSY} state_e;\n"
             "  rand state_e s;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    static D d = new;\n"
             "    void'(d.randomize() with { s == this.BUSY; t == super.HOT; "
             "});\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
