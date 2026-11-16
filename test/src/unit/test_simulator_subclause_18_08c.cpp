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

TEST(RandModeCases, ARandcVariableStartsActiveAndQueriesZeroWhenOff) {
  EXPECT_EQ(RunSrc(InModule("class C;\n"
                            "  randc bit [3:0] k;\n"
                            "endclass\n",
                            "    static C c = new;\n"
                            "    $display(\"%0d\", c.k.rand_mode());\n"
                            "    c.k.rand_mode(0);\n"
                            "    $display(\"%0d\", c.k.rand_mode());\n")),
            "1\n0\n");
}

TEST(RandModeCases, ARandMemberOfARandStructureStartsActive) {
  EXPECT_EQ(RunSrc(InModule("class C;\n"
                            "  rand struct { rand bit [3:0] a; } s;\n"
                            "endclass\n",
                            "    static C c = new;\n"
                            "    $display(\"%0d\", c.s.a.rand_mode());\n")),
            "1\n");
}

TEST(RandModeCases, DISABLED_AQueryThroughTheImplicitThisSeesAnActiveVariable) {
  EXPECT_EQ(RunSrc(InModule("class C;\n"
                            "  rand bit [3:0] x;\n"
                            "  function int q();\n"
                            "    return x.rand_mode();\n"
                            "  endfunction\n"
                            "endclass\n",
                            "    static C c = new;\n"
                            "    $display(\"%0d\", c.q());\n"
                            "    c.x.rand_mode(0);\n"
                            "    $display(\"%0d\", c.q());\n")),
            "1\n0\n");
}

TEST(RandModeCases, TheObjectCallLeavesAnInnerObjectsVariablesActive) {
  EXPECT_EQ(RunSrc(InModule("class In;\n"
                            "  rand bit [3:0] x;\n"
                            "endclass\n"
                            "class Out;\n"
                            "  rand In r = new;\n"
                            "endclass\n",
                            "    static Out h = new;\n"
                            "    h.rand_mode(0);\n"
                            "    $display(\"%0d %0d\", h.r.rand_mode(), "
                            "h.r.x.rand_mode());\n")),
            "0 1\n");
}

std::string OnOff(const std::string& set_off, const std::string& set_on) {
  return InModule(
      "class C;\n"
      "  rand bit [3:0] x;\n"
      "endclass\n",
      "    static C c = new;\n"
      "    automatic bit [1:0] v;\n"
      "    " +
          set_off +
          "\n"
          "    $display(\"%0d\", c.x.rand_mode());\n"
          "    " +
          set_on +
          "\n"
          "    $display(\"%0d\", c.x.rand_mode());\n");
}

TEST(RandModeCases, DISABLED_AnOnOffOfTwoOrThreeIsTruncatedToABit) {
  EXPECT_EQ(RunSrc(OnOff("c.x.rand_mode(2);", "c.x.rand_mode(3);")), "0\n1\n");
}

TEST(RandModeCases, DISABLED_AnObjectOnOffOfTwoOrThreeIsTruncatedToABit) {
  EXPECT_EQ(RunSrc(OnOff("c.rand_mode(2);", "c.rand_mode(3);")), "0\n1\n");
}

TEST(RandModeCases, AnOnOffGivenAsAVariableSetsTheMode) {
  EXPECT_EQ(RunSrc(OnOff("begin v = 0; c.x.rand_mode(v); end",
                         "begin v = 1; c.x.rand_mode(v); end")),
            "0\n1\n");
}

TEST(RandModeCases, TheObjectCallThroughADerivedHandleReachesTheBase) {
  EXPECT_EQ(RunSrc(InModule("class B;\n"
                            "  rand bit [3:0] a;\n"
                            "endclass\n"
                            "class D extends B;\n"
                            "  rand bit [3:0] b;\n"
                            "endclass\n",
                            "    static D d = new;\n"
                            "    d.rand_mode(0);\n"
                            "    $display(\"%0d %0d\", d.a.rand_mode(), "
                            "d.b.rand_mode());\n")),
            "0 0\n");
}

std::string ArrayModes(const std::string& decl, const std::string& fill,
                       const std::string& off) {
  return InModule("class C;\n" + decl + "endclass\n",
                  "    static C c = new;\n" + fill + "    " + off +
                      "\n"
                      "    $display(\"%0d %0d %0d\", c.v[0].rand_mode(), "
                      "c.v[1].rand_mode(), c.v[2].rand_mode());\n");
}

TEST(RandModeCases, AQueueElementNamedByItsIndexAloneTurnsOff) {
  EXPECT_EQ(
      RunSrc(ArrayModes("  rand bit [3:0] v[$];\n", "    c.v = '{1, 2, 3};\n",
                        "c.v[1].rand_mode(0);")),
      "1 0 1\n");
}

TEST(RandModeCases, AnAssociativeElementNamedByItsIndexAloneTurnsOff) {
  EXPECT_EQ(RunSrc(ArrayModes("  rand bit [3:0] v[int];\n",
                              "    c.v[0] = 1; c.v[1] = 2; c.v[2] = 3;\n",
                              "c.v[1].rand_mode(0);")),
            "1 0 1\n");
}

TEST(RandModeCases, AWholeDynamicArrayTurnsEveryElementOff) {
  EXPECT_EQ(RunSrc(ArrayModes("  rand bit [3:0] v[];\n", "    c.v = new[3];\n",
                              "c.v.rand_mode(0);")),
            "0 0 0\n");
}

TEST(RandModeCases, AWholeQueueTurnsEveryElementOff) {
  EXPECT_EQ(RunSrc(ArrayModes("  rand bit [3:0] v[$];\n",
                              "    c.v = '{1, 2, 3};\n", "c.v.rand_mode(0);")),
            "0 0 0\n");
}

TEST(RandModeCases, AWholeAssociativeArrayTurnsEveryElementOff) {
  EXPECT_EQ(RunSrc(ArrayModes("  rand bit [3:0] v[int];\n",
                              "    c.v[0] = 1; c.v[1] = 2; c.v[2] = 3;\n",
                              "c.v.rand_mode(0);")),
            "0 0 0\n");
}

TEST(RandModeCases, AWholeStructureTurnsEveryMemberOff) {
  EXPECT_EQ(RunSrc(InModule("class C;\n"
                            "  rand struct { rand bit [3:0] a, b; } s;\n"
                            "endclass\n",
                            "    static C c = new;\n"
                            "    static int held = 0;\n"
                            "    c.s.a = 5;\n"
                            "    c.s.b = 9;\n"
                            "    c.s.rand_mode(0);\n"
                            "    repeat (16) begin\n"
                            "      void'(c.randomize());\n"
                            "      if (c.s.a == 5 && c.s.b == 9) held++;\n"
                            "    end\n"
                            "    $display(\"%0d %0d %0d\", held, "
                            "c.s.a.rand_mode(), c.s.b.rand_mode());\n")),
            "16 0 0\n");
}

std::string ThroughAMethod(const std::string& off) {
  return InModule(
      "class C;\n"
      "  rand bit [3:0] x;\n"
      "  function void stop();\n"
      "    " +
          off +
          "\n"
          "  endfunction\n"
          "endclass\n",
      "    static C c = new;\n"
      "    static int held = 0;\n"
      "    c.x = 6;\n"
      "    c.stop();\n"
      "    repeat (16) begin\n"
      "      void'(c.randomize());\n"
      "      if (c.x == 6) held++;\n"
      "    end\n"
      "    $display(\"%0d %0d\", held, c.x.rand_mode());\n");
}

TEST(RandModeCases, AnExplicitThisInAMethodTakesEffect) {
  EXPECT_EQ(RunSrc(ThroughAMethod("this.x.rand_mode(0);")), "16 0\n");
}

TEST(RandModeCases, DISABLED_AnImplicitThisVariableInAMethodTakesEffect) {
  EXPECT_EQ(RunSrc(ThroughAMethod("x.rand_mode(0);")), "16 0\n");
}

TEST(RandModeCases, DISABLED_AnUnprefixedObjectCallInAMethodTakesEffect) {
  EXPECT_EQ(RunSrc(ThroughAMethod("rand_mode(0);")), "16 0\n");
}

TEST(RandModeCases, AStaticVariablesModeIsSharedAcrossTheHierarchy) {
  EXPECT_EQ(
      RunSrc(InModule("class B;\n"
                      "  static rand bit [3:0] s;\n"
                      "endclass\n"
                      "class D extends B;\n"
                      "endclass\n",
                      "    static B b = new;\n"
                      "    static D d = new;\n"
                      "    static int held = 0;\n"
                      "    B::s = 7;\n"
                      "    d.s.rand_mode(0);\n"
                      "    repeat (16) begin\n"
                      "      void'(b.randomize());\n"
                      "      if (B::s == 7) held++;\n"
                      "    end\n"
                      "    $display(\"%0d %0d\", held, b.s.rand_mode());\n")),
      "16 0\n");
}

}  // namespace
