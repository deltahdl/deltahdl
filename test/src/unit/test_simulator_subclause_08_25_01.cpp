#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"

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

}  // namespace
