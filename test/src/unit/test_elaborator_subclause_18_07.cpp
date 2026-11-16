#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

const char kClassQ[] =
    "class C;\n"
    "  rand bit [7:0] x;\n"
    "  int q = 2;\n"
    "endclass\n";

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

void ExpectUndeclared(const std::string& with_clause, const std::string& name) {
  ElabFixture f;
  EXPECT_FALSE(ElabOk(std::string(kClassQ) +
                          "module m;\n"
                          "  initial begin\n"
                          "    static C c = new;\n"
                          "    void'(c.randomize() " +
                          with_clause +
                          ");\n"
                          "  end\n"
                          "endmodule\n",
                      f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "undeclared identifier '" + name + "'", 8, "18.7"));
}

void ExpectAccepted(const std::string& with_clause) {
  EXPECT_TRUE(ElabOk(std::string(kClassQ) +
                     "module m;\n"
                     "  int q = 1;\n"
                     "  initial begin\n"
                     "    static C c = new;\n"
                     "    void'(c.randomize() " +
                     with_clause +
                     ");\n"
                     "  end\n"
                     "endmodule\n"));
}

TEST(InlineConstraints, DISABLED_ANameNeitherScopeDeclaresIsReported) {
  ExpectUndeclared("with { x == nosuch; }", "nosuch");
}

TEST(InlineConstraints, ANameTheObjectDeclaresElaborates) {
  ExpectAccepted("with { x == q; }");
}

TEST(InlineConstraints, DISABLED_ALocalNameOnlyTheObjectDeclaresIsReported) {
  ExpectUndeclared("with { x == local::q; }", "q");
}

TEST(InlineConstraints, ALocalNameTheCallerDeclaresElaborates) {
  ExpectAccepted("with { x == local::q; }");
}

TEST(InlineConstraints,
     DISABLED_AnUnlistedNameOnlyTheObjectDeclaresIsReported) {
  ExpectUndeclared("with (x) { x == q; }", "q");
}

TEST(InlineConstraints, AnUnlistedNameTheCallerDeclaresElaborates) {
  ExpectAccepted("with (x) { x == q; }");
}

TEST(InlineConstraints, DISABLED_AnEmptyListLeavesAnObjectOnlyNameUnresolved) {
  ExpectUndeclared("with () { x == 5; }", "x");
}

TEST(InlineConstraints, AnEmptyListReadsCallerNamesOnly) {
  ExpectAccepted("with () { q == 1; }");
}

TEST(InlineConstraints, AThisNameOnlyTheCallingClassDeclaresIsReported) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  rand bit [7:0] x;\n"
             "endclass\n"
             "class H;\n"
             "  int limit = 100;\n"
             "  function int go(C obj);\n"
             "    return obj.randomize() with { x < this.limit; };\n"
             "  endfunction\n"
             "endclass\n",
             f));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "'this.limit' names no member of class 'C', the "
                            "class randomize() with is called on",
                            7, "18.7"));
}

}  // namespace
