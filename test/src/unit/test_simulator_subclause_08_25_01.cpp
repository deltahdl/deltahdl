#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(ParameterizedScopeResolutionSim, BothClassAndLocalParamsReadable) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C #(parameter int p = 10);\n"
      "  parameter int q = 20;\n"
      "endclass\n"
      "module t;\n"
      "  int a, b;\n"
      "  initial begin\n"
      "    a = C#()::p;\n"
      "    b = C#()::q;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 10u}, {"b", 20u}});
}

TEST(ParameterizedScopeResolutionSim, TwoSpecializationsReturnDifferentValues) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "virtual class C #(parameter int W = 8);\n"
      "  static function int get_w;\n"
      "    get_w = W;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int a, b;\n"
      "  initial begin\n"
      "    a = C#(3)::get_w();\n"
      "    b = C#(7)::get_w();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 3u}, {"b", 7u}});
}

TEST(ParameterizedScopeResolutionSim,
     SpecificSpecializationValueAccessUsesOverride) {
  // §8.25.1: the explicit specialization form may denote a specific parameter,
  // so reading `C#(3)::p` yields the value of p in the C#(3) specialization --
  // 3 -- not the class's default of 1. Two different specializations of the
  // same value parameter therefore read back as their two override values.
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C #(parameter int p = 1);\n"
      "endclass\n"
      "module t;\n"
      "  int a, b;\n"
      "  initial begin\n"
      "    a = C#(3)::p;\n"
      "    b = C#(7)::p;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 3u}, {"b", 7u}});
}

TEST(ParameterizedScopeResolutionSim,
     OutOfBlockMethodTakesValueFromCallSiteSpecialization) {
  // §8.25.1: an out-of-block method definition of a parameterized class implies
  // no specialization of its own; the class parameter it reads is supplied by
  // the specialization named at the call site. The same out-of-block method
  // called through two specializations therefore returns the two parameter
  // values -- the default 1 for C#() and the override 5 for C#(5).
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C #(parameter int p = 1);\n"
      "  extern static function int f();\n"
      "endclass\n"
      "function int C::f();\n"
      "  return p;\n"
      "endfunction\n"
      "module t;\n"
      "  int a, b;\n"
      "  initial begin\n"
      "    a = C#()::f();\n"
      "    b = C#(5)::f();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 1u}, {"b", 5u}});
}

TEST(ParameterizedScopeResolutionSim,
     ScopeResolvedParamInMethodTracksActiveSpecialization) {
  // §8.25.1: inside the class the unadorned `C::p` names the class parameter,
  // and when the method runs under a specialization it reads that
  // specialization's value -- exactly as the bare name p does. With p read
  // twice (once bare, once as C::p) the result is 2*p: 2 for the default
  // specialization and 10 for C#(5).
  SimFixture f;
  auto* design = ElaborateSrc(
      "virtual class C #(parameter int p = 1);\n"
      "  static function int f();\n"
      "    return p + C::p;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int a, b;\n"
      "  initial begin\n"
      "    a = C#()::f();\n"
      "    b = C#(5)::f();\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 2u}, {"b", 10u}});
}

TEST(ParameterizedScopeResolutionSim, SpecializationArgumentFromLocalparam) {
  // §8.25.1: the explicit specialization's argument is a constant expression,
  // which may be a localparam and not only a literal. `C#(K)::p` reads p in the
  // specialization selected by the localparam K, so the result is K's value.
  EXPECT_EQ(RunAndGet("class C #(parameter int p = 1);\n"
                      "endclass\n"
                      "module t;\n"
                      "  localparam int K = 6;\n"
                      "  int result;\n"
                      "  initial result = C#(K)::p;\n"
                      "endmodule\n",
                      "result"),
            6u);
}

TEST(ParameterizedScopeResolutionSim,
     SpecializationArgumentFromModuleParameter) {
  // §8.25.1: the specialization argument may also be a module parameter, built
  // and resolved through a different declaration path than a literal or a
  // localparam. `C#(W)::p` selects the specialization named by W and reads p.
  EXPECT_EQ(RunAndGet("class C #(parameter int p = 1);\n"
                      "endclass\n"
                      "module t #(parameter int W = 9);\n"
                      "  int result;\n"
                      "  initial result = C#(W)::p;\n"
                      "endmodule\n",
                      "result"),
            9u);
}

TEST(ParameterizedScopeResolutionSim,
     SpecializationLeavesLocalParameterUnchanged) {
  // §8.25.1: a specialization overrides the class's value parameters (the
  // parameter port p), but a parameter declared in the class body (q) is not a
  // specialization argument and keeps its declared value. Reading both under
  // C#(3) gives the override 3 for p and the unchanged 5 for q.
  SimFixture f;
  auto* design = ElaborateSrc(
      "class C #(parameter int p = 1);\n"
      "  parameter int q = 5;\n"
      "endclass\n"
      "module t;\n"
      "  int a, b;\n"
      "  initial begin\n"
      "    a = C#(3)::p;\n"
      "    b = C#(3)::q;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"a", 3u}, {"b", 5u}});
}

TEST(ParameterizedScopeResolutionSim, NamedSpecializationOverrideResolves) {
  // §8.25.1: the specialization prefix may name its argument (.p(3)) instead of
  // supplying it positionally; `C#(.p(3))::p` still denotes p in that
  // specialization, so the result is 3.
  EXPECT_EQ(RunAndGet("class C #(parameter int p = 1);\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial result = C#(.p(3))::p;\n"
                      "endmodule\n",
                      "result"),
            3u);
}

TEST(ParameterizedScopeResolutionSim,
     DefaultScopeAccessFoldsAsConstantExpression) {
  // §8.25.1: the scope resolution operator accesses a parameter, which is a
  // constant expression, so `C#()::p` may appear where a constant is required.
  // Using it to initialize a localparam forces the access to fold at
  // elaboration; the folded localparam then reads back as the parameter's
  // default (3) at run time -- a different code path than a procedural read.
  EXPECT_EQ(RunAndGet("class C #(parameter int p = 3);\n"
                      "endclass\n"
                      "module t;\n"
                      "  localparam int W = C#()::p;\n"
                      "  int result;\n"
                      "  initial result = W;\n"
                      "endmodule\n",
                      "result"),
            3u);
}

TEST(ParameterizedScopeResolutionSim,
     SpecificSpecializationFoldsInConstantExpression) {
  // §8.25.1: the explicit specialization form denotes a specific parameter even
  // in a constant-expression position. Using C#(4)::p to initialize a
  // localparam forces the elaborator to fold the access; it must yield the
  // C#(4) specialization's value (4), not the class default (1), and the folded
  // localparam reads back as 4 at run time.
  EXPECT_EQ(RunAndGet("class C #(parameter int p = 1);\n"
                      "endclass\n"
                      "module t;\n"
                      "  localparam int W = C#(4)::p;\n"
                      "  int result;\n"
                      "  initial result = W;\n"
                      "endmodule\n",
                      "result"),
            4u);
}

TEST(ParameterizedScopeResolutionSim,
     UnadornedScopeInsideClassSelectsParameterOverLocal) {
  // §8.25.1: within the parameterized class the unadorned name as a scope
  // resolution prefix names a member -- here the parameter p -- and does not
  // denote the default specialization. It disambiguates the parameter from a
  // local variable of the same name, so `C::p` reads the parameter value 1,
  // not the shadowing local's 99.
  EXPECT_EQ(RunAndGet("class C #(parameter int p = 1);\n"
                      "  static function int g();\n"
                      "    int p = 99;\n"
                      "    return C::p;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial result = C#()::g();\n"
                      "endmodule\n",
                      "result"),
            1u);
}

// §8.25.1 (printed pages 205-206 of IEEE 1800-2023): the unadorned name
// of a parameterized class denotes its default specialization other than as the
// prefix of the class scope resolution operator, so `typedef C T;` makes T
// that specialization and `T::p` is `C#()::p`. The simulator knew a class by
// its declared name alone, so the typedef name resolved to no class and the
// read answered 0 while `C#()::p` beside it read 1. A class-body parameter is
// reached the same way.
TEST(ParameterizedScopeResolutionSim,
     ScopeResolutionThroughATypedefOfTheDefaultSpecialization) {
  EXPECT_EQ(RunAndGet("class C #(int p = 1);\n"
                      "  parameter int q = 5;\n"
                      "endclass\n"
                      "module t;\n"
                      "  typedef C T;\n"
                      "  int result;\n"
                      "  initial result = T::p * 100 + T::q * 10 + C#()::p;\n"
                      "endmodule\n",
                      "result"),
            151u);
}

// §6.18 with §8.9: a typedef of a class with no parameters names the class as
// well, so a static property is reached through it.
TEST(ParameterizedScopeResolutionSim,
     StaticPropertyThroughATypedefOfAPlainClass) {
  EXPECT_EQ(RunAndGet("class K;\n"
                      "  static int n = 6;\n"
                      "endclass\n"
                      "module t;\n"
                      "  typedef K KT;\n"
                      "  int result;\n"
                      "  initial result = KT::n + 30;\n"
                      "endmodule\n",
                      "result"),
            36u);
}

// §8.25 binds a class's type parameter throughout the class body per
// specialization (printed page 204 of IEEE 1800-2023), and §8.25.1 has
// the explicit specialization form as the prefix of the class scope resolution
// operator outside the class (printed 205), so §20.6.2's `$bits(T)` (printed
// 629) in a static method called as `Box#(byte)::bits()` is 8 whether the
// package class is reached through an import or through `p::`, and 16 for
// `p::Box#(shortint)::bits()`. No object runs a static method, so the actual
// was read off none: the value-parameter bind made a 1-bit local of the type
// name and every specialization answered 1.
TEST(ParameterizedScopeResolutionSim,
     BitsOfATypeParameterInAStaticMethodOfASpecialization) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  class Box #(type T = int);\n"
                      "    static function int bits(); return $bits(T);\n"
                      "    endfunction\n"
                      "  endclass\n"
                      "endpackage\n"
                      "module t;\n"
                      "  import p::*;\n"
                      "  int out;\n"
                      "  initial out = Box#(byte)::bits() * 10000 +\n"
                      "                p::Box#(byte)::bits() * 100 +\n"
                      "                p::Box#(shortint)::bits();\n"
                      "endmodule\n",
                      "out"),
            8u * 10000u + 8u * 100u + 16u);
}

// §8.25.1: `Box#()` is the default specialization, whose type parameter is
// the default the class declares -- byte here rather than int, so that the
// 8 the default gives is told from the 32 a class parameter's slot answered
// for the name -- and `Box#(shortint)` beside it reads its own 16.
TEST(ParameterizedScopeResolutionSim,
     BitsOfATypeParameterInAStaticMethodOfTheDefaultSpecialization) {
  EXPECT_EQ(RunAndGet("class Box #(type T = byte);\n"
                      "  static function int bits(); return $bits(T);\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int out;\n"
                      "  initial out = Box#()::bits() * 100 +\n"
                      "                Box#(shortint)::bits();\n"
                      "endmodule\n",
                      "out"),
            8u * 100u + 16u);
}

// §8.25 lets any type be the actual, so `Box#(logic [11:0])` -- a keyword
// type under a packed dimension, which the parse spells as a select on the
// name -- binds T to a 12-bit type, `Box#(int unsigned)` -- a type the parse
// reads as a type, since an expression cannot spell the signing -- to a
// 32-bit one, and `Box#(.T(word_t))` to the 20-bit typedef it names.
TEST(ParameterizedScopeResolutionSim,
     BitsOfARangedTypedefOrNamedTypeActualInAStaticMethod) {
  EXPECT_EQ(RunAndGet("class Box #(type T = int);\n"
                      "  static function int bits(); return $bits(T);\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  typedef bit [19:0] word_t;\n"
                      "  int out;\n"
                      "  initial out = Box#(logic [11:0])::bits() * 10000 +\n"
                      "                Box#(int unsigned)::bits() * 100 +\n"
                      "                Box#(.T(word_t))::bits();\n"
                      "endmodule\n",
                      "out"),
            12u * 10000u + 32u * 100u + 20u);
}

// §8.25 with §13.3: a static task named through a specialization runs as a
// coroutine, so its `#1` suspends the process, and the type the call bound
// is still in force when the body resumes: `Box#(shortint)::show(out)` writes
// 16 through its output formal where the default's `Box#()::show(out)`
// writes 32, and the sum tells the two calls apart from a 1 or a 32 twice.
TEST(ParameterizedScopeResolutionSim,
     BitsOfATypeParameterInAStaticTaskOfASpecialization) {
  EXPECT_EQ(RunAndGet("class Box #(type T = int);\n"
                      "  static task show(output int o);\n"
                      "    #1 o = $bits(T);\n"
                      "  endtask\n"
                      "endclass\n"
                      "module t;\n"
                      "  int a, b, out;\n"
                      "  initial begin\n"
                      "    Box#(shortint)::show(a);\n"
                      "    Box#()::show(b);\n"
                      "    out = a * 100 + b;\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            16u * 100u + 32u);
}

// §8.25.1 (printed page 205) with §26.3 (printed 808): the explicit
// specialization of a package's class reached through `p::` prefixes the
// class scope resolution operator as the bare name does, so a static task
// enabled as the statement `p::Box#(byte)::show(a)` runs with T bound to
// byte, 8 through its output formal after the `#1`, `p::Box#(shortint)` 16
// and `p::Box#()` the default's 32. The task statement bound the actuals of
// a bare `Box#(...)` alone, so the package-qualified forms answered 32 each.
TEST(ParameterizedScopeResolutionSim,
     BitsOfATypeParameterInAStaticTaskOfAPackageClassSpecialization) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  class Box #(type T = int);\n"
                      "    static task show(output int o);\n"
                      "      #1 o = $bits(T);\n"
                      "    endtask\n"
                      "  endclass\n"
                      "endpackage\n"
                      "module t;\n"
                      "  int a, b, c, out;\n"
                      "  initial begin\n"
                      "    p::Box#(byte)::show(a);\n"
                      "    p::Box#(shortint)::show(b);\n"
                      "    p::Box#()::show(c);\n"
                      "    out = a * 10000 + b * 100 + c;\n"
                      "  end\n"
                      "endmodule\n",
                      "out"),
            8u * 10000u + 16u * 100u + 32u);
}

// §8.25.1 with §8.10 (printed pages 186-187): a static method called
// through a specialization's scope, `C#(5)::outer()`, runs in the class's
// scope, so a bare `helper()` inside it is the class's own static method,
// as it is under `C::outer()`. outer reads helper() + N, twice N plus N, 15
// under #(5). The specialization call bound N and pushed no class, so the
// bare call was looked up in the caller's class, ran nothing and read 0,
// and outer answered 5.
TEST(ParameterizedScopeResolutionSim,
     BareStaticCallInsideAStaticMethodOfASpecialization) {
  EXPECT_EQ(RunAndGet("class C #(int N = 1);\n"
                      "  static function int helper();\n"
                      "    return N * 2;\n"
                      "  endfunction\n"
                      "  static function int outer();\n"
                      "    return helper() + N;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    result = C#(5)::outer();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            15u);
}

// §8.25.1 with §8.13: and the bare call may name a static method the base
// declares, uvm_typed_callbacks#(T)'s m_get_q called from
// uvm_callbacks#(T,CB)::get_first, which uvm_callback_iter#(T,CB)::first
// reaches as `uvm_callbacks#(T,CB)::get_first(m_i, m_obj)`: the ref formal
// writes get_first's q, whose size reads 3. Under the caller's class the
// call ran nothing, q stayed null and its size call was reported.
TEST(ParameterizedScopeResolutionSim,
     BareInheritedStaticCallInsideAStaticMethodOfASpecialization) {
  EXPECT_EQ(RunAndGet("class Q;\n"
                      "  int n = 3;\n"
                      "  function int size(); return n; endfunction\n"
                      "endclass\n"
                      "class C #(type T = int);\n"
                      "  static function void m_get_q(ref Q q, input T obj);\n"
                      "    q = new;\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class D #(type T = int) extends C#(T);\n"
                      "  static function int get_first(input T obj);\n"
                      "    Q q;\n"
                      "    m_get_q(q, obj);\n"
                      "    return q == null ? 7 : q.size();\n"
                      "  endfunction\n"
                      "endclass\n"
                      "class Iter #(type T = int);\n"
                      "  function int first();\n"
                      "    return D#(T)::get_first(0);\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    Iter#(int) it = new;\n"
                      "    result = it.first();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            3u);
}

}  // namespace
