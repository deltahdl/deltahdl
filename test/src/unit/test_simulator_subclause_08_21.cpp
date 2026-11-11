#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_scheduler.h"
#include "simulator/class_object.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(AbstractClassSimulation, AbstractExtendsAbstractVtable) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "virtual class Shape;\n"
      "  pure virtual function int area();\n"
      "endclass\n"
      "virtual class Shape2D extends Shape;\n"
      "  pure virtual function int perimeter();\n"
      "endclass\n"
      "module t; endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  auto* info = f.ctx.FindClassType("Shape2D");
  ASSERT_NE(info, nullptr);
  ASSERT_EQ(info->vtable.size(), 2u);
  EXPECT_EQ(info->vtable[0].method, nullptr);
  EXPECT_EQ(info->vtable[1].method, nullptr);
}

TEST(AbstractClassSimulation, LoweredAbstractClassIsAbstract) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "virtual class Base;\n"
      "  pure virtual function void work();\n"
      "endclass\n"
      "module t; endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  auto* info = f.ctx.FindClassType("Base");
  ASSERT_NE(info, nullptr);
  EXPECT_TRUE(info->is_abstract);
}

TEST(AbstractClassSimulation, LoweredPureVirtualNullInVtable) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "virtual class Base;\n"
      "  pure virtual function int compute();\n"
      "endclass\n"
      "module t; endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  auto* info = f.ctx.FindClassType("Base");
  ASSERT_NE(info, nullptr);
  ASSERT_FALSE(info->vtable.empty());
  EXPECT_EQ(info->vtable[0].method, nullptr);
}

TEST(AbstractClassSimulation, ConcreteSubclassOfAbstractBaseConstructed) {
  EXPECT_EQ(RunAndGet("virtual class Base;\n"
                      "  pure virtual function int compute();\n"
                      "endclass\n"
                      "class Derived extends Base;\n"
                      "  virtual function int compute();\n"
                      "    compute = 42;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Derived d;\n"
                      "    d = new;\n"
                      "    result = d.compute();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            42u);
}

TEST(AbstractClassSimulation, AbstractBaseConstructorRunsViaChaining) {
  EXPECT_EQ(RunAndGet("virtual class Base;\n"
                      "  int tag;\n"
                      "  pure virtual function int get();\n"
                      "  function new(int t);\n"
                      "    tag = t;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class Derived extends Base;\n"
                      "  function new();\n"
                      "    super.new(7);\n"
                      "  endfunction\n"
                      "  virtual function int get();\n"
                      "    get = tag;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Derived d;\n"
                      "    d = new;\n"
                      "    result = d.get();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            7u);
}

TEST(AbstractClassSimulation, ConstructAbstractClassDirectlyError) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "virtual class Base;\n"
      "  pure virtual function int compute();\n"
      "endclass\n"
      "module t;\n"
      "  Base b;\n"
      "  initial b = new;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot construct object of abstract class 'Base'",
                            6, "8.21"));
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot construct object of abstract class 'Base'",
                            6, "8.21"));
}

TEST(AbstractClassSimulation, EmptyBodyVirtualMethodIsCallable) {
  EXPECT_EQ(RunAndGet("class Base;\n"
                      "  virtual function int send(bit[31:0] data);\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Base b;\n"
                      "    b = new;\n"
                      "    b.send(0);\n"
                      "    result = 1;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(AbstractClassSimulation, ConstructAbstractClassNames8_21) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "virtual class Shape;\n"
      "  pure virtual function int area();\n"
      "endclass\n"
      "module t;\n"
      "  Shape s;\n"
      "  initial s = new;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot construct object of abstract class", 6,
                            "8.21"));
}

const char* const kEmptyBodySrc =
    "class K; endclass\n"
    "class B;\n"
    "  virtual function integer send(bit [31:0] data); endfunction\n"
    "  virtual function logic [7:0] l(); endfunction\n"
    "  virtual function int i(); endfunction\n"
    "  virtual function bit [3:0] b4(); endfunction\n"
    "  virtual function string s(); endfunction\n"
    "  virtual function K k(); endfunction\n"
    "  function integer nv(); endfunction\n"
    "  static function integer st(); endfunction\n"
    "  function integer dl(); int q; endfunction\n"
    "  function integer g(bit a); if (a) g = 5; endfunction\n"
    "endclass\n"
    "function integer mf(); endfunction\n"
    "module m;\n"
    "  B b = new;\n"
    "  integer z;\n"
    "  int r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14;\n"
    "  initial begin\n"
    "    r1 = (b.send(0) === 'x);\n"
    "    r2 = (b.l() === 8'bx);\n"
    "    r3 = b.i() + 7;\n"
    "    r4 = b.b4() + 7;\n"
    "    r5 = (b.s() == \"\");\n"
    "    r6 = (b.k() == null);\n"
    "    r7 = (b.nv() === 'x);\n"
    "    r8 = (B::st() === 'x);\n"
    "    r9 = (mf() === 'x);\n"
    "    r10 = (b.dl() === 'x);\n"
    "    r11 = b.g(1);\n"
    "    r12 = (b.g(0) === 'x);\n"
    "    r13 = (b.send(1) === 'x);\n"
    "    r14 = (z === 'x);\n"
    "  end\n"
    "endmodule\n";

TEST(AbstractClassSimulation,
     EmptyBodyOfATwoStateStringOrClassFunctionGivesItsDefault) {
  SimFixture f;
  auto* design = ElaborateSrc(kEmptyBodySrc, f);
  LowerRunAndCheck(f, design,
                   {{"r3", 7u},
                    {"r4", 7u},
                    {"r5", 1u},
                    {"r6", 1u},
                    {"r11", 5u},
                    {"r14", 1u}});
}

TEST(AbstractClassSimulation, DISABLED_EmptyBodyOfAFourStateFunctionGivesX) {
  SimFixture f;
  auto* design = ElaborateSrc(kEmptyBodySrc, f);
  LowerRunAndCheck(f, design,
                   {{"r1", 1u},
                    {"r2", 1u},
                    {"r7", 1u},
                    {"r8", 1u},
                    {"r9", 1u},
                    {"r10", 1u},
                    {"r12", 1u},
                    {"r13", 1u}});
}

}  // namespace
