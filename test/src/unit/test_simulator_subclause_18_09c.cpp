#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string RunSrc(const std::string& src) {
  SimFixture f;
  return RunCapture(src, f);
}

std::string InModule(const std::string& classes, const std::string& body) {
  return classes +
         "module t;\n"
         "  initial begin\n" +
         body +
         "  end\n"
         "endmodule\n";
}

const char kGated[] =
    "class P;\n"
    "  rand bit [3:0] x;\n"
    "  constraint c { x == 3; }\n"
    "endclass\n";

TEST(ConstraintModeCases,
     DISABLED_AnUnqualifiedQueryInAMethodSeesTheBlocksState) {
  EXPECT_EQ(RunSrc(InModule("class P;\n"
                            "  rand bit [3:0] x;\n"
                            "  constraint c { x == 3; }\n"
                            "  function int q();\n"
                            "    return c.constraint_mode();\n"
                            "  endfunction\n"
                            "  function void off();\n"
                            "    c.constraint_mode(0);\n"
                            "  endfunction\n"
                            "endclass\n",
                            "    static P p = new;\n"
                            "    $display(\"%0d\", p.q());\n"
                            "    p.off();\n"
                            "    $display(\"%0d\", p.q());\n")),
            "1\n0\n");
}

std::string Toggled(const std::string& off, const std::string& on) {
  return InModule(kGated,
                  "    static P p = new;\n"
                  "    " +
                      off +
                      "\n"
                      "    $display(\"%0d\", p.c.constraint_mode());\n"
                      "    " +
                      on +
                      "\n"
                      "    $display(\"%0d\", p.c.constraint_mode());\n");
}

TEST(ConstraintModeCases, DISABLED_AnOnOffOfTwoOrThreeIsTruncatedToABit) {
  EXPECT_EQ(
      RunSrc(Toggled("p.c.constraint_mode(2);", "p.c.constraint_mode(3);")),
      "0\n1\n");
}

TEST(ConstraintModeCases, AnUnknownOnOffConvertsToOff) {
  EXPECT_EQ(
      RunSrc(Toggled("p.c.constraint_mode(1'bx);", "p.c.constraint_mode(1);")),
      "0\n1\n");
}

TEST(ConstraintModeCases, AnOnOffGivenAsAVariableSetsTheMode) {
  EXPECT_EQ(RunSrc(InModule(kGated,
                            "    static P p = new;\n"
                            "    automatic bit v = 0;\n"
                            "    p.c.constraint_mode(v);\n"
                            "    $display(\"%0d\", p.c.constraint_mode());\n"
                            "    v = 1;\n"
                            "    p.c.constraint_mode(v);\n"
                            "    $display(\"%0d\", p.c.constraint_mode());\n")),
            "0\n1\n");
}

TEST(ConstraintModeCases, TheQueryYieldsAnInt) {
  EXPECT_EQ(RunSrc(InModule(
                kGated,
                "    static P p = new;\n"
                "    $display(\"%0d\", $bits(p.c.constraint_mode()));\n")),
            "32\n");
}

TEST(ConstraintModeCases, TurningOffAnOverridingBlockEnforcesNeitherBlock) {
  EXPECT_EQ(RunSrc(InModule("class B;\n"
                            "  rand bit [3:0] x;\n"
                            "  constraint c { x < 5; }\n"
                            "endclass\n"
                            "class D extends B;\n"
                            "  constraint c { x > 10; }\n"
                            "endclass\n",
                            "    static D d = new;\n"
                            "    static int high = 0, middle = 0;\n"
                            "    repeat (32) begin\n"
                            "      void'(d.randomize());\n"
                            "      if (d.x > 10) high++;\n"
                            "    end\n"
                            "    d.c.constraint_mode(0);\n"
                            "    repeat (128) begin\n"
                            "      void'(d.randomize());\n"
                            "      if (d.x >= 5 && d.x <= 10) middle++;\n"
                            "    end\n"
                            "    $display(\"%0d %0d\", high, middle > 0);\n")),
            "32 1\n");
}

const char kTwoLevels[] =
    "class B;\n"
    "  rand bit [3:0] x;\n"
    "  constraint bc { x == 3; }\n"
    "endclass\n"
    "class D extends B;\n"
    "  rand bit [3:0] y;\n"
    "  constraint dc { y == 4; }\n"
    "endclass\n";

TEST(ConstraintModeCases, TheObjectCallTurnsEveryBlockBackOn) {
  EXPECT_EQ(RunSrc(InModule(kTwoLevels,
                            "    static D d = new;\n"
                            "    d.constraint_mode(0);\n"
                            "    d.constraint_mode(1);\n"
                            "    void'(d.randomize());\n"
                            "    $display(\"%0d %0d %0d %0d\", "
                            "d.bc.constraint_mode(), d.dc.constraint_mode(), "
                            "d.x, d.y);\n")),
            "1 1 3 4\n");
}

TEST(ConstraintModeCases, AThisObjectCallInAMethodTurnsEveryBlockOff) {
  EXPECT_EQ(RunSrc(InModule("class P;\n"
                            "  rand bit [3:0] x, y;\n"
                            "  constraint a { x == 3; }\n"
                            "  constraint b { y == 4; }\n"
                            "  function void off();\n"
                            "    this.constraint_mode(0);\n"
                            "  endfunction\n"
                            "endclass\n",
                            "    static P p = new;\n"
                            "    p.off();\n"
                            "    $display(\"%0d %0d\", p.a.constraint_mode(), "
                            "p.b.constraint_mode());\n")),
            "0 0\n");
}

TEST(ConstraintModeCases, TheObjectCallThroughABaseHandleReachesDerivedBlocks) {
  EXPECT_EQ(RunSrc(InModule(kTwoLevels,
                            "    static D d = new;\n"
                            "    static B b = d;\n"
                            "    b.constraint_mode(0);\n"
                            "    $display(\"%0d %0d\", d.bc.constraint_mode(), "
                            "d.dc.constraint_mode());\n")),
            "0 0\n");
}

TEST(ConstraintModeCases, AThisQualifiedBlockInAMethodIsSetAndQueried) {
  EXPECT_EQ(RunSrc(InModule("class P;\n"
                            "  rand bit [3:0] x;\n"
                            "  constraint c { x == 3; }\n"
                            "  function int set(bit on);\n"
                            "    this.c.constraint_mode(on);\n"
                            "    return this.c.constraint_mode();\n"
                            "  endfunction\n"
                            "endclass\n",
                            "    static P p = new;\n"
                            "    $display(\"%0d\", p.set(0));\n"
                            "    $display(\"%0d\", p.set(1));\n")),
            "0\n1\n");
}

const char kNested[] =
    "class In;\n"
    "  rand bit [3:0] y;\n"
    "  constraint ci { y == 5; }\n"
    "endclass\n"
    "class P;\n"
    "  In inner = new;\n"
    "endclass\n";

TEST(ConstraintModeCases, DISABLED_AnInnerObjectPropertyTakesTheObjectCall) {
  EXPECT_EQ(RunSrc(InModule(
                kNested,
                "    static P p = new;\n"
                "    p.inner.constraint_mode(0);\n"
                "    $display(\"%0d\", p.inner.ci.constraint_mode());\n")),
            "0\n");
}

TEST(ConstraintModeCases, AnInnerObjectPropertyTakesANamedBlockCall) {
  EXPECT_EQ(RunSrc(InModule(
                kNested,
                "    static P p = new;\n"
                "    p.inner.ci.constraint_mode(0);\n"
                "    $display(\"%0d\", p.inner.ci.constraint_mode());\n")),
            "0\n");
}

TEST(ConstraintModeCases, ABaseHandleNamesABlockOfTheDerivedObject) {
  EXPECT_EQ(RunSrc(InModule(kTwoLevels,
                            "    static D d = new;\n"
                            "    static B b = d;\n"
                            "    static int other = 0;\n"
                            "    b.bc.constraint_mode(0);\n"
                            "    repeat (32) begin\n"
                            "      void'(d.randomize());\n"
                            "      if (d.x != 3) other++;\n"
                            "    end\n"
                            "    $display(\"%0d %0d\", d.bc.constraint_mode(), "
                            "other > 0);\n")),
            "0 1\n");
}

TEST(ConstraintModeCases,
     DISABLED_AMemberHandleInTheHoldersMethodTurnsItsObjectsBlockOff) {
  EXPECT_EQ(RunSrc("class A; rand bit [3:0] v; constraint bad { v == 3; } "
                   "endclass\n"
                   "class C;\n"
                   "  rand A a = new;\n"
                   "  constraint c { a.v != 3; }\n"
                   "  function void off(); a.bad.constraint_mode(0); "
                   "endfunction\n"
                   "endclass\n"
                   "module t;\n"
                   "  initial begin\n"
                   "    static C o = new;\n"
                   "    o.off();\n"
                   "    $display(\"%0d %0d\", o.a.bad.constraint_mode(), "
                   "o.randomize());\n"
                   "  end\n"
                   "endmodule\n"),
            "0 1\n");
}

}  // namespace
