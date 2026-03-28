#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(TypedConstructorCallSim, ConstructsSpecifiedType) {
  EXPECT_EQ(RunAndGet(
      "class C;\n"
      "  int x;\n"
      "  function new(); x = 1; endfunction\n"
      "endclass\n"
      "class D extends C;\n"
      "  function new(); super.new(); x = 42; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C c;\n"
      "    c = D::new;\n"
      "    result = c.x;\n"
      "  end\n"
      "endmodule\n", "result"), 42u);
}

TEST(TypedConstructorCallSim, TypedConstructorWithPositionalArgs) {
  EXPECT_EQ(RunAndGet(
      "class C;\n"
      "  int val;\n"
      "  function new(int v); val = v; endfunction\n"
      "endclass\n"
      "class D extends C;\n"
      "  function new(int v); super.new(v); endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C c;\n"
      "    c = D::new(99);\n"
      "    result = c.val;\n"
      "  end\n"
      "endmodule\n", "result"), 99u);
}

TEST(TypedConstructorCallSim, TypedConstructorWithNamedArgs) {
  EXPECT_EQ(RunAndGet(
      "class C;\n"
      "  int val;\n"
      "  function new(int v); val = v; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C c;\n"
      "    c = C::new(.v(55));\n"
      "    result = c.val;\n"
      "  end\n"
      "endmodule\n", "result"), 55u);
}

TEST(TypedConstructorCallSim, TypedConstructorSameType) {
  EXPECT_EQ(RunAndGet(
      "class C;\n"
      "  int val;\n"
      "  function new(); val = 33; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C c;\n"
      "    c = C::new;\n"
      "    result = c.val;\n"
      "  end\n"
      "endmodule\n", "result"), 33u);
}

TEST(TypedConstructorCallSim, TypedConstructorInitializesProperties) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C;\n"
      "  int a;\n"
      "  int b;\n"
      "  function new(int x, int y);\n"
      "    a = x;\n"
      "    b = y;\n"
      "  endfunction\n"
      "endclass\n"
      "class D extends C;\n"
      "  function new(int x, int y); super.new(x, y); endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int ra, rb;\n"
      "  initial begin\n"
      "    C c;\n"
      "    c = D::new(10, 20);\n"
      "    ra = c.a;\n"
      "    rb = c.b;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"ra", 10u}, {"rb", 20u}});
}

TEST(TypedConstructorCallSim, TypedConstructorPropertyDefaults) {
  EXPECT_EQ(RunAndGet(
      "class C;\n"
      "  int x = 5;\n"
      "endclass\n"
      "class D extends C;\n"
      "  int y = 10;\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C c;\n"
      "    c = D::new;\n"
      "    result = c.x;\n"
      "  end\n"
      "endmodule\n", "result"), 5u);
}

TEST(TypedConstructorCallSim, ParameterizedTypedConstructor) {
  EXPECT_EQ(RunAndGet(
      "class C;\n"
      "  int val;\n"
      "  function new(); val = 0; endfunction\n"
      "endclass\n"
      "class E #(int N = 1) extends C;\n"
      "  function new(); super.new(); val = N; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C c;\n"
      "    c = E#(.N(77))::new;\n"
      "    result = c.val;\n"
      "  end\n"
      "endmodule\n", "result"), 77u);
}

TEST(TypedConstructorCallSim, ParameterizedTypedConstructorWithArgs) {
  EXPECT_EQ(RunAndGet(
      "class C;\n"
      "  int val;\n"
      "  function new(); val = 0; endfunction\n"
      "endclass\n"
      "class E #(int N = 1) extends C;\n"
      "  int extra;\n"
      "  function new(int e); super.new(); val = N; extra = e; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C c;\n"
      "    c = E#(.N(10))::new(.e(20));\n"
      "    result = c.val;\n"
      "  end\n"
      "endmodule\n", "result"), 10u);
}

}  // namespace
