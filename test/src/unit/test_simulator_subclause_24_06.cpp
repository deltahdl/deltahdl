#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(AnonymousProgramSim, ClassDeclaredInAnAnonymousProgramIsConstructed) {
  auto v = RunAndGet(
      "program;\n"
      "  class Box; int v; function new(int x); v = x; endfunction endclass\n"
      "endprogram\n"
      "module top;\n"
      "  int result;\n"
      "  program p;\n"
      "    Box b;\n"
      "    initial begin b = new(19); result = b.v + 1; end\n"
      "  endprogram\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 20u);
}

TEST(AnonymousProgramSim,
     ATopLevelProgramUsesAnAnonymousProgramFunctionsValue) {
  SimFixture f;
  EXPECT_EQ(
      RunCaptureAllTops("program;\n"
                        "  function int f(int x); return x * 3; endfunction\n"
                        "endprogram\n"
                        "program p;\n"
                        "  initial $display(\"%0d\", f(7));\n"
                        "endprogram\n",
                        f),
      "21\n");
}

TEST(AnonymousProgramSim,
     AProgramReachesAPackageAnonymousFunctionByImportAndByScope) {
  SimFixture f;
  EXPECT_EQ(RunCaptureAllTops(
                "package pkg;\n"
                "  program;\n"
                "    function int f(int x); return x + 100; endfunction\n"
                "  endprogram\n"
                "endpackage\n"
                "program p;\n"
                "  import pkg::*;\n"
                "  initial $display(\"%0d %0d\", f(1), pkg::f(2));\n"
                "endprogram\n",
                f),
            "101 102\n");
}

TEST(AnonymousProgramSim,
     DISABLED_ATopLevelProgramsClassExtendsAnAnonymousProgramClass) {
  SimFixture f;
  EXPECT_EQ(RunCaptureAllTops(
                "program;\n"
                "  class B;\n"
                "    virtual function int v(); return 4; endfunction\n"
                "  endclass\n"
                "endprogram\n"
                "program p;\n"
                "  class D extends B;\n"
                "    function int v(); return 5 + super.v(); endfunction\n"
                "  endclass\n"
                "  D d;\n"
                "  initial begin d = new; $display(\"%0d\", d.v()); end\n"
                "endprogram\n",
                f),
            "9\n");
}

TEST(AnonymousProgramSim, ANestedProgramsClassExtendsAnAnonymousProgramClass) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("program;\n"
                 "  class B;\n"
                 "    virtual function int v(); return 4; endfunction\n"
                 "  endclass\n"
                 "endprogram\n"
                 "module top;\n"
                 "  program p;\n"
                 "    class D extends B;\n"
                 "      function int v(); return 5 + super.v(); endfunction\n"
                 "    endclass\n"
                 "    D d;\n"
                 "    initial begin d = new; $display(\"%0d\", d.v()); end\n"
                 "  endprogram\n"
                 "endmodule\n",
                 f),
      "9\n");
}

TEST(AnonymousProgramSim,
     AProgramsClassImplementsAnAnonymousProgramInterfaceClass) {
  SimFixture f;
  EXPECT_EQ(RunCaptureAllTops(
                "program;\n"
                "  interface class IS;\n"
                "    pure virtual function int g();\n"
                "  endclass\n"
                "endprogram\n"
                "program p;\n"
                "  class C implements IS;\n"
                "    virtual function int g(); return 6; endfunction\n"
                "  endclass\n"
                "  C c;\n"
                "  initial begin c = new; $display(\"%0d\", c.g()); end\n"
                "endprogram\n",
                f),
            "6\n");
}

}  // namespace
