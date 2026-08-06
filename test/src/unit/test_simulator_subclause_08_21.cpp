#include "builders_ast.h"
#include "builders_systask.h"
#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "helpers_scheduler.h"
#include "simulator/class_object.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

// 8.21: an abstract class may be extended into a further abstract class; its
// pure virtual methods -- both the one inherited from the abstract base and the
// one newly added -- remain unimplemented prototypes, which the lowerer records
// as null vtable slots. Driven end-to-end so the lowerer, not the test, builds
// the vtable.
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

// 8.21: an abstract class's constructor is never invoked on its own -- it runs
// only indirectly, reached by the constructor chain of an extended non-abstract
// object. The abstract base here defines a real constructor that stores a
// field; the concrete subclass reaches it with super.new (real 8.7/8.17
// constructor and chaining syntax). The stored value surviving into the
// constructed object shows the base constructor executed during the subclass's
// indirect construction.
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

// 8.21: an object of an abstract class shall not be constructed directly.
// Constructing the abstract base with 'new' is a runtime error even though
// the declaration of the handle elaborates cleanly.
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
  EXPECT_FALSE(f.has_errors);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_TRUE(f.diag.HasErrors());
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

}  // namespace
