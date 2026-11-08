#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/sim_context_types.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(PackageImportSim, PackageHandleArrayElementsAreSixtyFourBitsWide) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package p1;\n"
      "  class C;\n"
      "    int v;\n"
      "  endclass\n"
      "  C q[$];\n"
      "  C d[];\n"
      "  C arr[2];\n"
      "endpackage\n"
      "module top;\n"
      "  import p1::*;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* q = f.ctx.FindQueue("p1.q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->elem_width, 64u);
  auto* d = f.ctx.FindArrayInfo("p1.d");
  ASSERT_NE(d, nullptr);
  EXPECT_EQ(d->elem_width, 64u);
  auto* elem = f.ctx.FindVariable("p1.arr[1]");
  ASSERT_NE(elem, nullptr);
  EXPECT_EQ(elem->value.width, 64u);
}

TEST(PackageImportSim, PackageQueueOfHandlesReadThroughElementProperties) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  class C;\n"
                      "    int v;\n"
                      "    function new(int a); v = a; endfunction\n"
                      "  endclass\n"
                      "  C q[$];\n"
                      "endpackage\n"
                      "module top;\n"
                      "  import p1::*;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    static C c1 = new(6);\n"
                      "    static C c2 = new(8);\n"
                      "    p1::q.push_back(c1);\n"
                      "    p1::q.push_back(c2);\n"
                      "    y = p1::q[1].v * 100 + p1::q[0].v;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            806u);
}

TEST(PackageScopeReferenceSim,
     PackageClassVariableInitializerConstructsItsSpecialization) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  class G #(int N = 1);\n"
                      "    function int get_n();\n"
                      "      return N;\n"
                      "    endfunction\n"
                      "  endclass\n"
                      "  G #(5) b = new;\n"
                      "  G #(7) c = new;\n"
                      "endpackage\n"
                      "module t;\n"
                      "  int y;\n"
                      "  initial y = p1::b.get_n() * 10 + p1::c.get_n();\n"
                      "endmodule\n",
                      "y"),
            57u);
}

TEST(PackageImportSim, PackageVoidFunctionCalledAsAStatementWritesItsPackage) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int x;\n"
                      "  function void set(int v);\n"
                      "    x = v;\n"
                      "  endfunction\n"
                      "  function int bump(int v);\n"
                      "    x = x + v;\n"
                      "    return x;\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int a, y;\n"
                      "  initial begin\n"
                      "    p1::set(5);\n"
                      "    a = p1::x;\n"
                      "    void'(p1::bump(1));\n"
                      "    y = a * 10 + p1::x;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            56u);
}

TEST(PackageImportSim, PackageFunctionWritesItsOwnQueueBare) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int q[$];\n"
                      "  function void add(int v);\n"
                      "    q.push_back(v);\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p1::add(5);\n"
                      "    p1::add(6);\n"
                      "    y = p1::q.size() * 10 + p1::q[1];\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            26u);
}

TEST(PackageImportSim, PackageFunctionWritesItsOwnAssociativeArrayReadBare) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int m[string];\n"
                      "  function void put(int v);\n"
                      "    m[\"k\"] = v;\n"
                      "  endfunction\n"
                      "  function int get();\n"
                      "    return m[\"k\"];\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p1::put(5);\n"
                      "    y = p1::get();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            5u);
}

TEST(PackageImportSim,
     PackageFunctionWritesItsOwnAssociativeArrayReadThroughTheQualifier) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int m[string];\n"
                      "  function void put(int v);\n"
                      "    m[\"k\"] = v;\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p1::put(5);\n"
                      "    y = p1::m[\"k\"];\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            5u);
}

TEST(PackageImportSim,
     PackageAssociativeArrayWrittenThroughTheQualifierReadBare) {
  EXPECT_EQ(RunAndGet("package p1;\n"
                      "  int m[string];\n"
                      "  function int get();\n"
                      "    return m[\"k\"];\n"
                      "  endfunction\n"
                      "endpackage\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    p1::m[\"k\"] = 7;\n"
                      "    y = p1::get();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            7u);
}

TEST(PackageImportSim, PackageQualifiedClassHandleWithoutImportRunsItsTask) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  class C;\n"
                      "    task t(); #3; endtask\n"
                      "  endclass\n"
                      "endpackage\n"
                      "module top;\n"
                      "  p::C c = new;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    c.t();\n"
                      "    y = $time;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            3u);
}

TEST(PackageImportSim,
     PackageQualifiedClassHandleWithoutImportRunsItsFunction) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  class C;\n"
                      "    int x = 4;\n"
                      "    function void f(); x = 7; endfunction\n"
                      "  endclass\n"
                      "endpackage\n"
                      "module top;\n"
                      "  p::C c;\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    c = new;\n"
                      "    y = c.x * 10;\n"
                      "    c.f();\n"
                      "    y = y + c.x;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            47u);
}

TEST(PackageImportSim, AModuleClassExtendsAnImportedClass) {
  for (const char* import : {"import p::B;", "import p::*;"}) {
    EXPECT_EQ(RunAndGet(std::string("package p;\n"
                                    "  localparam int K = 4;\n"
                                    "  class B;\n"
                                    "    int b = 3;\n"
                                    "    function int get(); return b + K; "
                                    "endfunction\n"
                                    "  endclass\n"
                                    "endpackage\n"
                                    "module t; ") +
                            import +
                            "\n"
                            "  class D extends B;\n"
                            "  endclass\n"
                            "  D d = new;\n"
                            "  int r;\n"
                            "  initial r = d.b * 10 + d.get();\n"
                            "endmodule\n",
                        "r"),
              37u)
        << import;
  }
}

TEST(PackageImportSim, AUnitClassExtendsAClassNamedThroughAPackage) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  localparam int K = 4;\n"
                      "  class B;\n"
                      "    int b = 3;\n"
                      "    function int get(); return b + K; endfunction\n"
                      "  endclass\n"
                      "endpackage\n"
                      "class B;\n"
                      "  int b = 9;\n"
                      "endclass\n"
                      "class D extends p::B;\n"
                      "endclass\n"
                      "module t;\n"
                      "  D d = new;\n"
                      "  B u = new;\n"
                      "  int r;\n"
                      "  initial r = d.b * 100 + d.get() * 10 + u.b;\n"
                      "endmodule\n",
                      "r"),
            379u);
}

TEST(PackageImportSim, APackagesClassTypedefDeclaresAHandleOfItsClass) {
  for (const char* unit : {"", "class D extends p::B;\nendclass\n"}) {
    EXPECT_EQ(RunAndGet(std::string("package q;\n"
                                    "  class C;\n"
                                    "    int c = 5;\n"
                                    "  endclass\n"
                                    "endpackage\n"
                                    "package p;\n"
                                    "  class B;\n"
                                    "    int b = 3;\n"
                                    "  endclass\n"
                                    "  typedef B bt;\n"
                                    "  typedef q::C ct;\n"
                                    "  typedef bt bt2;\n"
                                    "endpackage\n") +
                            unit +
                            "module t;\n"
                            "  p::bt h = new;\n"
                            "  p::ct g = new;\n"
                            "  p::bt2 k = new;\n"
                            "  int r;\n"
                            "  initial r = h.b * 100 + g.c * 10 + k.b;\n"
                            "endmodule\n",
                        "r"),
              353u)
        << unit;
  }
}

}  // namespace
