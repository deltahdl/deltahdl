#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(TypedConstructorCallSim, ConstructsSpecifiedType) {
  EXPECT_EQ(RunAndGet("class C;\n"
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
                      "endmodule\n",
                      "result"),
            42u);
}

TEST(TypedConstructorCallSim, TypedConstructorWithPositionalArgs) {
  EXPECT_EQ(RunAndGet("class C;\n"
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
                      "endmodule\n",
                      "result"),
            99u);
}

TEST(TypedConstructorCallSim, TypedConstructorWithNamedArgs) {
  EXPECT_EQ(RunAndGet("class C;\n"
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
                      "endmodule\n",
                      "result"),
            55u);
}

TEST(TypedConstructorCallSim, TypedConstructorSameType) {
  EXPECT_EQ(RunAndGet("class C;\n"
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
                      "endmodule\n",
                      "result"),
            33u);
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
  EXPECT_EQ(RunAndGet("class C;\n"
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
                      "endmodule\n",
                      "result"),
            5u);
}

TEST(TypedConstructorCallSim, ParameterizedTypedConstructor) {
  EXPECT_EQ(RunAndGet("class C;\n"
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
                      "endmodule\n",
                      "result"),
            77u);
}

TEST(TypedConstructorCallSim, MultiLevelInheritanceConstructsSpecifiedType) {
  // §8.8: the constructed object is the named (specified) type even when that
  // type sits several levels below the target's type, and §8.7-style chained
  // construction runs every level's constructor in order. The most-derived
  // constructor runs last, so its assignment to the shared property wins.
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int x;\n"
                      "  function new(); x = 1; endfunction\n"
                      "endclass\n"
                      "class D extends C;\n"
                      "  function new(); super.new(); x = 2; endfunction\n"
                      "endclass\n"
                      "class E extends D;\n"
                      "  function new(); super.new(); x = 3; endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    c = E::new;\n"
                      "    result = c.x;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            3u);
}

// §8.8: the canonical example `C c = D::new;` uses a typed constructor call as
// a declaration initializer (not a procedural assignment). The object created
// must still be of the specified type D, so a property only assigned by D's
// constructor is observable through the base-typed handle. This exercises the
// block-local declaration-initializer construction path.
TEST(TypedConstructorCallSim, TypedConstructorAsBlockLocalDeclInit) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int x;\n"
                      "  function new(); x = 1; endfunction\n"
                      "endclass\n"
                      "class D extends C;\n"
                      "  function new(); super.new(); x = 42; endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c = D::new;\n"
                      "    result = c.x;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            42u);
}

// §8.8: the same declaration-initializer form must also construct the specified
// type when the declaration is a static (module-level) variable, whose
// initializer runs during static initialization rather than in a procedural
// block.
TEST(TypedConstructorCallSim, TypedConstructorAsStaticDeclInit) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int x;\n"
                      "  function new(); x = 1; endfunction\n"
                      "endclass\n"
                      "class D extends C;\n"
                      "  function new(); super.new(); x = 42; endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  C c = D::new;\n"
                      "  int result;\n"
                      "  initial result = c.x;\n"
                      "endmodule\n",
                      "result"),
            42u);
}

// §8.8: arguments may be passed to a typed constructor call just as for an
// ordinary constructor, so the argument conventions of §8.7 -- including the
// use of default argument values -- apply. A typed call that supplies only the
// leading actual leaves the trailing formal at its declared default, observed
// here through the constructed object.
TEST(TypedConstructorCallSim, TypedConstructorAppliesDefaultArgument) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int a;\n"
                      "  int b;\n"
                      "  function new(int x, int y = 20);\n"
                      "    a = x;\n"
                      "    b = y;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    c = C::new(5);\n"
                      "    result = c.b;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            20u);
}

// §8.8/§8.25: the specified type of a typed constructor call may be a
// parameterized class carrying a type-parameter specialization (as in the LRM's
// `E#(.T(byte))::new` example), not only a value-parameter override. The
// specialization is bound during construction and the constructor runs against
// it, storing the passed value into an inherited property observed through the
// base-typed handle.
TEST(TypedConstructorCallSim, TypedConstructorWithTypeParameterSpecialization) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int val;\n"
                      "  function new(); val = 0; endfunction\n"
                      "endclass\n"
                      "class E #(type T = int) extends C;\n"
                      "  function new(T v); super.new(); val = v; endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    c = E#(.T(byte))::new(.v(5));\n"
                      "    result = c.val;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            5u);
}

TEST(TypedConstructorCallSim, ParameterizedTypedConstructorWithArgs) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int val;\n"
                      "  function new(); val = 0; endfunction\n"
                      "endclass\n"
                      "class E #(int N = 1) extends C;\n"
                      "  int extra;\n"
                      "  function new(int e); super.new(); val = N; extra = e; "
                      "endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c;\n"
                      "    c = E#(.N(10))::new(.e(20));\n"
                      "    result = c.val;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            10u);
}

}  // namespace
