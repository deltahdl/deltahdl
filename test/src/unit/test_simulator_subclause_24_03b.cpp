#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(ProgramRunEnd, AJoinNoneChildLeftBehindDoesNotHoldTheRun) {
  SimFixture f;
  EXPECT_EQ(
      RunCaptureThroughFinals(ElaborateSrc,
                              "program p;\n"
                              "  initial begin\n"
                              "    fork #5 $display(\"child\"); join_none\n"
                              "    #2;\n"
                              "  end\n"
                              "endprogram\n"
                              "module top;\n"
                              "  p pi();\n"
                              "  initial #9 $display(\"late\");\n"
                              "  final $display(\"end %0t\", $time);\n"
                              "endmodule\n",
                              f),
      "end 2\n");
}

TEST(ProgramRunEnd, TheLaterOfTwoInitialsInOneProgramEndsTheRun) {
  SimFixture f;
  EXPECT_EQ(RunCaptureThroughFinals(ElaborateSrc,
                                    "program p;\n"
                                    "  initial #2 $display(\"a %0t\", $time);\n"
                                    "  initial #5 $display(\"b %0t\", $time);\n"
                                    "endprogram\n"
                                    "module top;\n"
                                    "  p pi();\n"
                                    "  initial #9 $display(\"late\");\n"
                                    "  final $display(\"end %0t\", $time);\n"
                                    "endmodule\n",
                                    f),
            "a 2\nb 5\nend 5\n");
}

TEST(ProgramRunEnd, AnUninstantiatedTopLevelProgramEndsTheRun) {
  SimFixture f;
  EXPECT_EQ(RunCaptureThroughFinals(ElaborateSrcAllTops,
                                    "module t;\n"
                                    "  initial #9 $display(\"late\");\n"
                                    "  final $display(\"end %0t\", $time);\n"
                                    "endmodule\n"
                                    "program p;\n"
                                    "  initial #2 $display(\"p %0t\", $time);\n"
                                    "endprogram\n",
                                    f),
            "p 2\nend 2\n");
}

TEST(ProgramRunEnd, AProgramWithOnlyAFinalGivesNoImplicitFinish) {
  SimFixture f;
  EXPECT_EQ(RunCaptureThroughFinals(ElaborateSrc,
                                    "module top;\n"
                                    "  program p;\n"
                                    "    final $display(\"pf %0t\", $time);\n"
                                    "  endprogram\n"
                                    "  initial #9 $display(\"m %0t\", $time);\n"
                                    "endmodule\n",
                                    f),
            "m 9\npf 9\n");
}

TEST(ProgramThreadEnd, AnEndedProgramKillsOnlyItsOwnDescendants) {
  SimFixture f;
  EXPECT_EQ(RunCaptureThroughFinals(
                ElaborateSrc,
                "program p1;\n"
                "  initial fork #10 $display(\"p1 child\"); join_none\n"
                "endprogram\n"
                "program p2;\n"
                "  initial begin\n"
                "    fork #5 $display(\"p2 child\"); join_none\n"
                "    #20 $display(\"p2 end %0t\", $time);\n"
                "  end\n"
                "endprogram\n"
                "module top;\n"
                "  p1 a();\n"
                "  p2 b();\n"
                "endmodule\n",
                f),
            "p2 child\np2 end 20\n");
}

TEST(ProgramThreadEnd,
     DISABLED_DescendantsLiveUntilTheProgramsLastInitialEnds) {
  SimFixture f;
  EXPECT_EQ(RunCaptureThroughFinals(
                ElaborateSrc,
                "program p;\n"
                "  initial fork #5 $display(\"child %0t\", $time); join_none\n"
                "  initial #10 $display(\"last %0t\", $time);\n"
                "endprogram\n"
                "module top;\n"
                "  p pi();\n"
                "endmodule\n",
                f),
            "child 5\nlast 10\n");
}

TEST(ProgramImplicitInstance, ANestedProgramWithPortsIsNotInstantiated) {
  SimFixture f;
  EXPECT_EQ(RunCaptureThroughFinals(ElaborateSrc,
                                    "module top;\n"
                                    "  program p(input logic a);\n"
                                    "    initial $display(\"ran\");\n"
                                    "  endprogram\n"
                                    "  initial #1 $display(\"m\");\n"
                                    "endmodule\n",
                                    f),
            "m\n");
}

TEST(ProgramImplicitInstance, AProgramWithPortsInAnInterfaceIsNotInstantiated) {
  SimFixture f;
  EXPECT_EQ(RunCaptureThroughFinals(ElaborateSrc,
                                    "interface bus;\n"
                                    "  program p(input logic a);\n"
                                    "    initial $display(\"ran\");\n"
                                    "  endprogram\n"
                                    "  initial #1 $display(\"i\");\n"
                                    "endinterface\n"
                                    "module top;\n"
                                    "  bus b();\n"
                                    "endmodule\n",
                                    f),
            "i\n");
}

TEST(ProgramImplicitInstance, ATopLevelProgramWithPortsIsInstantiated) {
  SimFixture f;
  EXPECT_EQ(RunCaptureThroughFinals(ElaborateSrcAllTops,
                                    "module t;\n"
                                    "endmodule\n"
                                    "program p(input logic a);\n"
                                    "  initial $display(\"ran\");\n"
                                    "endprogram\n",
                                    f),
            "ran\n");
}

TEST(ProgramNesting, TwoNestedProgramsShareTheModulesVariable) {
  SimFixture f;
  EXPECT_EQ(
      RunCaptureThroughFinals(ElaborateSrc,
                              "module top;\n"
                              "  int shared;\n"
                              "  program w;\n"
                              "    initial shared = 6;\n"
                              "  endprogram\n"
                              "  program r;\n"
                              "    initial #1 $display(\"%0d\", shared);\n"
                              "  endprogram\n"
                              "endmodule\n",
                              f),
      "6\n");
}

TEST(ProgramDeclarations, AProgramAutomaticVariableStaysStatic) {
  SimFixture f;
  EXPECT_EQ(RunCaptureThroughFinals(ElaborateSrc,
                                    "module top;\n"
                                    "  program automatic p;\n"
                                    "    int c;\n"
                                    "    task bump(); c++; endtask\n"
                                    "    initial begin\n"
                                    "      bump();\n"
                                    "      bump();\n"
                                    "      $display(\"c=%0d\", c);\n"
                                    "    end\n"
                                    "  endprogram\n"
                                    "  program q;\n"
                                    "    initial #1 $display(\"q=%0d\", p.c);\n"
                                    "  endprogram\n"
                                    "endmodule\n",
                                    f),
            "c=2\nq=2\n");
}

TEST(ProgramDeclarations, TwoProgramsKeepTheirOwnSameNamedData) {
  SimFixture f;
  EXPECT_EQ(RunCaptureThroughFinals(
                ElaborateSrc,
                "module top;\n"
                "  program p1;\n"
                "    int data;\n"
                "    initial data = 1;\n"
                "  endprogram\n"
                "  program p2;\n"
                "    int data;\n"
                "    initial data = 2;\n"
                "  endprogram\n"
                "  program rd;\n"
                "    initial #1 $display(\"%0d %0d\", p1.data, p2.data);\n"
                "  endprogram\n"
                "endmodule\n",
                f),
            "1 2\n");
}

TEST(ProgramDeclarations, DISABLED_TwoProgramsKeepTheirOwnSameNamedTypes) {
  SimFixture f;
  EXPECT_EQ(
      RunCaptureThroughFinals(ElaborateSrc,
                              "module top;\n"
                              "  program p1;\n"
                              "    typedef logic [3:0] t;\n"
                              "    initial $display(\"p1 %0d\", $bits(t));\n"
                              "  endprogram\n"
                              "  program p2;\n"
                              "    typedef logic [7:0] t;\n"
                              "    initial #1 $display(\"p2 %0d\", $bits(t));\n"
                              "  endprogram\n"
                              "endmodule\n",
                              f),
      "p1 4\np2 8\n");
}

TEST(ProgramInstances, EachInstanceReadsAndDrivesOnlyItsOwnPorts) {
  SimFixture f;
  EXPECT_EQ(
      RunCaptureThroughFinals(ElaborateSrc,
                              "program p(input var int v, output int w);\n"
                              "  initial #1 w = v + 1;\n"
                              "endprogram\n"
                              "module top;\n"
                              "  int a = 1, b = 10, wa, wb;\n"
                              "  p u0(a, wa);\n"
                              "  p u1(b, wb);\n"
                              "  final $display(\"%0d %0d\", wa, wb);\n"
                              "endmodule\n",
                              f),
      "2 11\n");
}

TEST(ProgramInstances, EachInstanceTakesItsOwnParameterValue) {
  SimFixture f;
  EXPECT_EQ(RunCaptureThroughFinals(ElaborateSrc,
                                    "program p #(parameter int K = 0);\n"
                                    "  int v;\n"
                                    "  initial begin\n"
                                    "    v = K;\n"
                                    "    #(K) $display(\"%m %0d\", v);\n"
                                    "  end\n"
                                    "endprogram\n"
                                    "module top;\n"
                                    "  p #(1) u0();\n"
                                    "  p #(2) u1();\n"
                                    "endmodule\n",
                                    f),
            "top.u0 1\ntop.u1 2\n");
}

TEST(ProgramInstances, EachInstanceKeepsItsOwnState) {
  SimFixture f;
  EXPECT_EQ(RunCaptureThroughFinals(ElaborateSrc,
                                    "program p(input var int v);\n"
                                    "  int s;\n"
                                    "  initial begin\n"
                                    "    #1 s = v;\n"
                                    "    #(s) $display(\"%m %0d\", s);\n"
                                    "  end\n"
                                    "endprogram\n"
                                    "module top;\n"
                                    "  p u0(1);\n"
                                    "  p u1(2);\n"
                                    "endmodule\n",
                                    f),
            "top.u0 1\ntop.u1 2\n");
}

TEST(ProgramInstances, EachLoopGenerateInstanceReadsItsOwnElement) {
  SimFixture f;
  EXPECT_EQ(
      RunCaptureThroughFinals(ElaborateSrc,
                              "program p(input var int v);\n"
                              "  initial begin\n"
                              "    #1;\n"
                              "    #(v) $display(\"%m %0d\", v);\n"
                              "  end\n"
                              "endprogram\n"
                              "module top;\n"
                              "  int arr[2] = '{3, 4};\n"
                              "  for (genvar i = 0; i < 2; i++) begin : g\n"
                              "    p pi(arr[i]);\n"
                              "  end\n"
                              "endmodule\n",
                              f),
      "top.g[0].pi 3\ntop.g[1].pi 4\n");
}

TEST(ProgramInstances, AGenericInterfacePortReachesTheConnectedInstance) {
  SimFixture f;
  EXPECT_EQ(RunCaptureThroughFinals(ElaborateSrc,
                                    "interface bus;\n"
                                    "  int v = 7;\n"
                                    "endinterface\n"
                                    "program prg(interface d);\n"
                                    "  initial #1 $display(\"%0d\", d.v);\n"
                                    "endprogram\n"
                                    "module top;\n"
                                    "  bus b();\n"
                                    "  prg p(b);\n"
                                    "endmodule\n",
                                    f),
            "7\n");
}

TEST(ProgramContents, EachOfSeveralFinalsInATopLevelProgramRunsOnce) {
  SimFixture f;
  std::string out =
      RunCaptureThroughFinals(ElaborateSrcAllTops,
                              "program p;\n"
                              "  initial #1;\n"
                              "  final $display(\"f1 %0t\", $time);\n"
                              "  final $display(\"f2 %0t\", $time);\n"
                              "endprogram\n",
                              f);
  EXPECT_TRUE(out == "f1 1\nf2 1\n" || out == "f2 1\nf1 1\n") << out;
}

TEST(ProgramContents, ANestedProgramsFinalRunsOnceAtTheEnd) {
  SimFixture f;
  EXPECT_EQ(RunCaptureThroughFinals(ElaborateSrc,
                                    "module top;\n"
                                    "  program p;\n"
                                    "    initial #1;\n"
                                    "    final $display(\"done %0t\", $time);\n"
                                    "  endprogram\n"
                                    "  initial #9 $display(\"late\");\n"
                                    "endmodule\n",
                                    f),
            "done 1\n");
}

TEST(ProgramContents, AProgramsOwnFunctionIsCalledFromItsInitial) {
  SimFixture f;
  EXPECT_EQ(RunCaptureThroughFinals(ElaborateSrcAllTops,
                                    "program p;\n"
                                    "  int r;\n"
                                    "  function int sq(int x); return x * x; "
                                    "endfunction\n"
                                    "  initial begin\n"
                                    "    r = sq(7);\n"
                                    "    $display(\"%0d\", r);\n"
                                    "  end\n"
                                    "endprogram\n",
                                    f),
            "49\n");
}

constexpr const char* kSourceProgram =
    "module top;\n"
    "  program src;\n"
    "    int sig = 0;\n"
    "    initial sig = 11;\n"
    "  endprogram\n";

TEST(ProgramToProgramReference, AReadInsideATaskOfTheReferringProgram) {
  SimFixture f;
  EXPECT_EQ(
      RunCaptureThroughFinals(ElaborateSrc,
                              std::string(kSourceProgram) +
                                  "  program dst;\n"
                                  "    int got;\n"
                                  "    task tk(); #1 got = src.sig; endtask\n"
                                  "    initial begin\n"
                                  "      tk();\n"
                                  "      $display(\"%0d\", got);\n"
                                  "    end\n"
                                  "  endprogram\n"
                                  "endmodule\n",
                              f),
      "11\n");
}

TEST(ProgramToProgramReference, AReadInsideAFunctionOfTheReferringProgram) {
  SimFixture f;
  EXPECT_EQ(
      RunCaptureThroughFinals(ElaborateSrc,
                              std::string(kSourceProgram) +
                                  "  program dst;\n"
                                  "    function int peek(); return src.sig; "
                                  "endfunction\n"
                                  "    initial #1 $display(\"%0d\", peek());\n"
                                  "  endprogram\n"
                                  "endmodule\n",
                              f),
      "11\n");
}

TEST(ProgramToProgramReference, AReadInsideAClassMethodOfTheReferringProgram) {
  SimFixture f;
  EXPECT_EQ(
      RunCaptureThroughFinals(ElaborateSrc,
                              std::string(kSourceProgram) +
                                  "  program dst;\n"
                                  "    class C;\n"
                                  "      function int get(); return src.sig; "
                                  "endfunction\n"
                                  "    endclass\n"
                                  "    initial begin\n"
                                  "      C c;\n"
                                  "      c = new;\n"
                                  "      #1 $display(\"%0d\", c.get());\n"
                                  "    end\n"
                                  "  endprogram\n"
                                  "endmodule\n",
                              f),
      "11\n");
}

TEST(ProgramToProgramReference, ALaterWriteInTheOtherProgramIsSeen) {
  SimFixture f;
  EXPECT_EQ(
      RunCaptureThroughFinals(ElaborateSrc,
                              "module top;\n"
                              "  program src;\n"
                              "    int sig = 5;\n"
                              "    initial #1 sig = 9;\n"
                              "  endprogram\n"
                              "  program dst;\n"
                              "    initial #2 $display(\"%0d\", src.sig);\n"
                              "  endprogram\n"
                              "endmodule\n",
                              f),
      "9\n");
}

TEST(ProgramDesignSignals, PackageAndCompilationUnitVariablesAreShared) {
  SimFixture f;
  EXPECT_EQ(RunCaptureThroughFinals(
                ElaborateSrc,
                "package pk;\n"
                "  int pv = 1;\n"
                "endpackage\n"
                "int uv = 2;\n"
                "module top;\n"
                "  initial begin\n"
                "    pk::pv = 10;\n"
                "    uv = 20;\n"
                "  end\n"
                "  program p;\n"
                "    import pk::*;\n"
                "    initial begin\n"
                "      $display(\"%0d %0d %0d %0d\", pk::pv, pv, uv, "
                "$unit::uv);\n"
                "      pk::pv = 30;\n"
                "      uv = 40;\n"
                "    end\n"
                "  endprogram\n"
                "  final $display(\"%0d %0d\", pk::pv, uv);\n"
                "endmodule\n",
                f),
            "10 10 20 20\n30 40\n");
}

}  // namespace
