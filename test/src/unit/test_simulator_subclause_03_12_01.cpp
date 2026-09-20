#include <gtest/gtest.h>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(CompilationUnitSim, CuScopeFunctionCallableFromModule) {
  auto val = RunAndGet(
      "function int helper(int x); return x + 1; endfunction\n"
      "module top;\n"
      "  int observed;\n"
      "  initial observed = helper(5);\n"
      "endmodule\n",
      "observed");
  EXPECT_EQ(val, 6u);
}

TEST(CompilationUnitSim, MultipleCuScopeFunctionsResolvedAtRuntime) {
  auto val = RunAndGet(
      "function int twice(int x); return x * 2; endfunction\n"
      "function int add_one(int x); return x + 1; endfunction\n"
      "module top;\n"
      "  int observed;\n"
      "  initial observed = twice(add_one(3));\n"
      "endmodule\n",
      "observed");
  EXPECT_EQ(val, 8u);
}

// §3.12.1 and §6.19: an enumeration a typedef declares at compilation-unit
// scope declares its literals for the modules of the unit, so a module reads
// MID as 1 and a class method of the unit compares against JUMBO.
TEST(CompilationUnitSim, CuScopeEnumLiteralsResolveInModulesAndClasses) {
  auto val = RunAndGet(
      "typedef enum {LOW, MID, HIGH} level_t;\n"
      "class Reader;\n"
      "  function int is_high(level_t l);\n"
      "    return l == HIGH;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int r;\n"
      "  initial begin\n"
      "    Reader o = new;\n"
      "    r = MID + 10 * o.is_high(HIGH);\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(val, 11u);
}

// §3.12.1 (printed page 56) with §6.21 (printed 132-133): the
// compilation-unit scope holds the declarations outside any other scope,
// and a name a module's own scope does not declare is searched for there
// next, so `int g;` written outside every module is one variable both
// modules share: a's process writes 5 at time 0 through a unit-scope
// function and top's reads it at time 1: 5. No lowerer path created the
// unit's storage (CreateUnitDataVariables in lowerer_package_data.cpp), so
// the write landed nowhere and the read answered nothing. The write goes
// through a function of the unit because the elaborator's §23.9 check of a
// procedural assignment's target (ValidateScopeRules in
// elaborator_scope_rules.cpp) knows the module's own names and its imports'
// and not the unit's, so `initial g = 5` in a module is reported as
// undeclared, which a subroutine body escapes; the read side admits the
// unit's names.
TEST(CompilationUnitSim, CuScopeVariableSharedByTwoModules) {
  auto val = RunAndGet(
      "int g;\n"
      "function void set_g(int v);\n"
      "  g = v;\n"
      "endfunction\n"
      "module a;\n"
      "  initial set_g(5);\n"
      "endmodule\n"
      "module top;\n"
      "  a u();\n"
      "  int y;\n"
      "  initial #1 y = g;\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(val, 5u);
}

// §3.12.1 (printed page 56) with §26.2 (printed 808): a declaration
// assignment of the compilation-unit scope is made before any initial or
// always procedure starts, as a package's is, so `int g = 4;` outside every
// module reads 4 in a process at time 0 and `$unit::g` names the same
// variable: 4 * 10 + 4. With no storage for the unit's items neither read
// answered.
TEST(CompilationUnitSim, CuScopeVariableInitializedBeforeAnyProcess) {
  auto val = RunAndGet(
      "int g = 4;\n"
      "module top;\n"
      "  int y;\n"
      "  initial y = g * 10 + $unit::g;\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(val, 44u);
}

// §3.12.1 (printed page 56) with §8.3 (printed 180): `C h;` outside every
// module, after a unit-scope `class C`, is one handle variable of C the
// unit's modules share, so `h = new` through a unit function constructs an
// object of C into it and a module's `h.v` reads the property's initializer
// 3. The unit's storage was sized 32 bits, half a handle, with no class
// recorded under `h` (RegisterUnitClassVariables in lowerer_register.cpp
// records the packages' alone before), so the `new` found no class to
// construct and `h.v` read no object. The write goes through a unit
// function for the reason CuScopeVariableSharedByTwoModules gives.
TEST(CompilationUnitSim, CuScopeClassHandleConstructedThroughUnitFunction) {
  auto val = RunAndGet(
      "class C;\n"
      "  int v = 3;\n"
      "endclass\n"
      "C h;\n"
      "function void mk();\n"
      "  h = new;\n"
      "endfunction\n"
      "module top;\n"
      "  int y;\n"
      "  initial begin\n"
      "    mk();\n"
      "    y = h.v;\n"
      "  end\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(val, 3u);
}

// §3.12.1 (printed page 56) with §8.7 (printed 184) and §26.2 (printed
// 808): the unit's declaration assignment `C h2 = new;` constructs the
// object before any procedure starts, as a package's would, so a module
// reads 3 through `h2.v` at time 0 with no write of its own. The
// initializer was evaluated as an ordinary expression, which a bare `new`
// is not, so nothing was constructed (ConstructDataClassInitializers in
// lowerer_package_data.cpp makes the construction once the unit's classes
// are lowered).
TEST(CompilationUnitSim, CuScopeClassHandleConstructedByItsInitializer) {
  auto val = RunAndGet(
      "class C;\n"
      "  int v = 3;\n"
      "endclass\n"
      "C h2 = new;\n"
      "module top;\n"
      "  int y;\n"
      "  initial y = h2.v;\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(val, 3u);
}

// §3.12.1 (printed page 56) with §26.3 (printed 810): a wildcard import
// written at compilation-unit scope makes a package's class visible to the
// unit's own declarations, so `C h3 = new;` after `import p::*` is a handle
// of p's C, constructed before any procedure starts, and a module reads 4
// through it. The record of the class a unit variable holds is found
// through the unit's imports when the unit declares no class of the name
// (UnitScopeClassKey in lowerer_register.cpp); with none, the storage was
// 32 bits and nothing was constructed.
TEST(CompilationUnitSim, CuScopeHandleOfAWildcardImportedPackageClass) {
  auto val = RunAndGet(
      "package p;\n"
      "  class C;\n"
      "    int v = 4;\n"
      "  endclass\n"
      "endpackage\n"
      "import p::*;\n"
      "C h3 = new;\n"
      "module top;\n"
      "  int y;\n"
      "  initial y = h3.v;\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(val, 4u);
}

}  // namespace
