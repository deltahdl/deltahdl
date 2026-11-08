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

}  // namespace
