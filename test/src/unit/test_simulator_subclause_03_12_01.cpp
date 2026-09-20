#include <gtest/gtest.h>

#include <cstdint>
#include <string>

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
// through a function of the unit because, when this case was written, the
// elaborator's §23.9 check of a procedural assignment's target
// (ValidateScopeRules in elaborator_scope_rules.cpp) knew the module's own
// names and its imports' and not the unit's, so `initial g = 5` in a module
// was reported as undeclared, which a subroutine body escapes; the case is
// kept beside CuScopeVariableWrittenDirectlyByAModuleProcess below, which
// writes without the function, so the unit function's write to the unit's
// variable stays covered.
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

// §3.12.1 (printed page 56) with §6.21 (printed 132-133): a module's own
// procedural assignment writes the unit's variable, `initial g = 5;` in a
// with no function between, and top reads 5 through it at time 1. The
// elaborator reported the write as "undeclared identifier 'g'"
// (ValidateScopeRules in elaborator_scope_rules.cpp admitted the module's
// names and its imports' alone), so no such design reached the simulator;
// the case above wrote through a unit function to get past it. The value
// read is the write's and not the declaration's, which has none, so a run
// whose write landed elsewhere reads 0.
TEST(CompilationUnitSim, CuScopeVariableWrittenDirectlyByAModuleProcess) {
  auto val = RunAndGet(
      "int g;\n"
      "module a;\n"
      "  initial g = 5;\n"
      "endmodule\n"
      "module top;\n"
      "  a u();\n"
      "  int y;\n"
      "  initial #1 y = g;\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(val, 5u);
}

// §3.12.1 (printed page 56) with §6.10 (printed 108) and §10.3.2 (printed
// 249): a module's continuous assignment drives the unit's variable, `assign
// g = 5;` in a with no declaration of g in the module, and top reads 5
// through it at time 1. The elaborator assumed an implicit net `g` of the
// module for the target (MaybeCreateImplicitNet in elaborator_items.cpp knew
// the module's own names alone), so the assignment drove that net and the
// unit's variable, keyed under its bare name and registered as an imported
// name, stayed 0 -- which a run whose driver lands elsewhere still reads.
TEST(CompilationUnitSim, CuScopeVariableDrivenByAModuleContinuousAssignment) {
  auto val = RunAndGet(
      "int g;\n"
      "module a;\n"
      "  assign g = 5;\n"
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
// function for the reason CuScopeVariableSharedByTwoModules gives, and is
// kept so a unit function's `new` into the unit's handle stays covered.
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

// A design whose package p declares `int K = 4` and a function f reading it,
// followed by the unit-scope declarations `unit_decls` outside every module,
// the last of which declares g, and a module top whose process reads g into
// y at time 0; answers y.
static uint64_t UnitInitializerRead(const std::string& unit_decls) {
  return RunAndGet(
      "package p;\n"
      "  int K = 4;\n"
      "  function int f();\n"
      "    return K * 2;\n"
      "  endfunction\n"
      "endpackage\n" +
          unit_decls +
          "module top;\n"
          "  int y;\n"
          "  initial y = g;\n"
          "endmodule\n",
      "y");
}

// §3.12.1 (printed page 56) with §26.3 (printed 810) and §26.2 (printed
// 808): a wildcard import written at compilation-unit scope makes p's K
// visible in the unit's scope, whose declaration assignment `int g = K;` is
// made before any procedure starts, after p's own `int K = 4;`, so a module
// reads 4 through g at time 0. The unit's imports were bound after the
// unit's initializers had run (LowerCompilationUnitImports after
// InitUnitDataVariables), so the initializer found no K and g read 0.
TEST(CompilationUnitSim, CuScopeInitializerReadsAWildcardImportedVariable) {
  EXPECT_EQ(UnitInitializerRead("import p::*;\n"
                                "int g = K;\n"),
            4u);
}

// The same through an explicit `import p::K;`, which §26.3 binds ahead of a
// wildcard one (§26.5): `int g = K * 10 + 1;` reads 41; an unbound K read 0
// and g 1.
TEST(CompilationUnitSim, CuScopeInitializerReadsAnExplicitlyImportedVariable) {
  EXPECT_EQ(UnitInitializerRead("import p::K;\n"
                                "int g = K * 10 + 1;\n"),
            41u);
}

// §3.12.1 with §26.2 (printed page 808): the unit's `int g = p::f();` calls
// the package's function through the scope resolution operator (§26.3),
// which reads the package's own K, initialized before the unit's items are,
// so g holds 8 and a module reads 8. A K read before its initializer would
// give 0, and a call resolved to nothing 0.
TEST(CompilationUnitSim, CuScopeInitializerCallsAPackageFunction) {
  EXPECT_EQ(UnitInitializerRead("int g = p::f();\n"), 8u);
}

// A design whose compilation-unit scope declares `int g = 5;` ahead of the
// modules `modules`, the last of which is the top; answers the variable
// `var_name` once the run has ended, a hierarchical name for an instance's.
static uint64_t UnitGRead(const std::string& modules, const char* var_name) {
  return RunAndGet("int g = 5;\n" + modules, var_name);
}

// §3.12.1 (printed page 56) with §23.9 (printed 761): a reference is
// resolved in the nearer scope first, the module's own declaration ahead of
// the compilation unit's, so top's `int g = 7;` is the g its process reads:
// 7. A resolution that reached the unit's storage under the shared name
// read 5.
TEST(CompilationUnitSim, CuScopeVariableShadowedByTheModulesOwnDeclaration) {
  EXPECT_EQ(UnitGRead("module top;\n"
                      "  int g = 7;\n"
                      "  int y;\n"
                      "  initial y = g;\n"
                      "endmodule\n",
                      "y"),
            7u);
}

// §3.12.1 (printed page 56) with §6.21 (printed 132-133): the unit's `int g
// = 5;` outlives an instance's like-named declaration, a's `int g = 7;`
// stored under the instance's own key, so top, which declares no g, reads
// the unit's 5. An instance's declaration displacing the unit's storage
// read 7.
TEST(CompilationUnitSim, CuScopeVariableKeptByAnInstanceDeclaringTheName) {
  EXPECT_EQ(UnitGRead("module a;\n"
                      "  int g = 7;\n"
                      "endmodule\n"
                      "module top;\n"
                      "  a u();\n"
                      "  int y;\n"
                      "  initial y = g;\n"
                      "endmodule\n",
                      "y"),
            5u);
}

// §3.12.1 (printed page 56) with §23.9 (printed 761): the top's `int g =
// 7;` is the top's own, and an instance whose module declares no g reads
// the unit's g, the enclosing scope's, so u.y is 5. The unit's storage
// stood under the bare name the top's declaration is keyed by, so the top's
// LowerVar (lowerer_var.cpp) replaced it, and the instance's bare reference,
// which SimContext::FindVariable answers from the bare key, read the top's
// 7. The unit's storage now stands under "$unit.g" and each instance is
// bound to it under its own prefix (AliasUnitDataItems in
// lowerer_package_data.cpp), the top's own declaration left to the top.
TEST(CompilationUnitSim, CuScopeVariableReadByAnInstanceWhileTheTopDeclaresIt) {
  EXPECT_EQ(UnitGRead("module a;\n"
                      "  int y;\n"
                      "  initial y = g;\n"
                      "endmodule\n"
                      "module top;\n"
                      "  int g = 7;\n"
                      "  a u();\n"
                      "endmodule\n",
                      "u.y"),
            5u);
}

// §3.12.1 (printed page 56) with §23.9 (printed 761) and §23.3.3.2: a port
// of the top named as the unit's variable is the top's own g, an
// unconnected `input var int` reading its type's default 0 (Table 6-7), and
// the instance below reads the unit's 5, so `g * 10 + u.y` at time 1 is 5.
// The port's storage is created only where nothing answers the name
// (CreatePortVariable in lowerer_register.cpp), and the unit's storage
// under the bare name answered it, so the port was the unit's variable and
// both read 5: 55.
TEST(CompilationUnitSim, CuScopeVariableNamedAsAPortOfTheTopIsNotThePort) {
  EXPECT_EQ(UnitGRead("module a;\n"
                      "  int y;\n"
                      "  initial y = g;\n"
                      "endmodule\n"
                      "module top(input var int g);\n"
                      "  a u();\n"
                      "  int y;\n"
                      "  initial #1 y = g * 10 + u.y;\n"
                      "endmodule\n",
                      "y"),
            5u);
}

// §3.12.1 (printed page 56) with §26.2 (printed 808): the unit's own
// declaration assignment `int h = g + 1;` reads the unit's g whatever a
// module declares, so top's `y = h` reads 6 beside the top's own g. The
// unit's initializers are evaluated in a frame of the unit's own scope,
// which resolves the bare name to "$unit.g"; a frame resolving it by the
// bare key alone finds no g once the key is left to the top's declaration.
TEST(CompilationUnitSim, CuScopeInitializerReadsTheUnitsOwnShadowedVariable) {
  EXPECT_EQ(UnitGRead("int h = g + 1;\n"
                      "module top;\n"
                      "  int g = 7;\n"
                      "  int y;\n"
                      "  initial y = h;\n"
                      "endmodule\n",
                      "y"),
            6u);
}

// §3.12.1 (printed page 56) with §23.9 (printed 761): `$unit::g` names the
// compilation-unit scope's g explicitly, past the top's own `int g = 7;`,
// which the bare g resolves to, so `g * 10 + $unit::g` is 75. The prefix
// was dropped by EvalIdentifier (evaluation.cpp), which read the
// identifier's text alone, so both read the top's 7: 77.
TEST(CompilationUnitSim, CuScopeVariableNamedThroughUnitPrefixPastTheTopsOwn) {
  EXPECT_EQ(UnitGRead("module top;\n"
                      "  int g = 7;\n"
                      "  int y;\n"
                      "  initial y = g * 10 + $unit::g;\n"
                      "endmodule\n",
                      "y"),
            75u);
}

// §3.12.1 (printed page 56) with §23.9 (printed 761): `$unit::g = 3` in the
// top writes the unit's g, so the top's own g stays 7 and the instance a,
// declaring no g, reads the unit's 3 at time 1: `g * 10 + u.y` at time 2
// is 73. Resolved by the identifier's text (ResolveLhsVariable in
// statement_assign.cpp), the write landed in the top's g and the instance
// read the unit's untouched 5: 35.
TEST(CompilationUnitSim,
     CuScopeVariableWrittenThroughUnitPrefixPastTheTopsOwn) {
  EXPECT_EQ(UnitGRead("module a;\n"
                      "  int y;\n"
                      "  initial #1 y = g;\n"
                      "endmodule\n"
                      "module top;\n"
                      "  int g = 7;\n"
                      "  a u();\n"
                      "  int y;\n"
                      "  initial begin\n"
                      "    $unit::g = 3;\n"
                      "    #2 y = g * 10 + u.y;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            73u);
}

// §3.12.1 (printed page 56) with §13.5.1: a `$unit::g` actual is the
// unit's g passed by value, so `twice($unit::g) * 10 + twice(g)` beside the
// top's own g is 114; the actual read by its text was the top's 7: 154.
// `$unit::g` where the module declares no g reads as the bare g does
// (CuScopeVariableInitializedBeforeAnyProcess above).
TEST(CompilationUnitSim, CuScopeVariableAsAnActualThroughUnitPrefix) {
  EXPECT_EQ(UnitGRead("function int twice(int v);\n"
                      "  return v * 2;\n"
                      "endfunction\n"
                      "module top;\n"
                      "  int g = 7;\n"
                      "  int y;\n"
                      "  initial y = twice($unit::g) * 10 + twice(g);\n"
                      "endmodule\n",
                      "y"),
            114u);
}

// §3.12.1 (printed page 56) with §8.9 (printed 186): a static property of
// the unit's own class C is initialized once, its `static int s = g * 10 +
// 1;` an expression of the unit's scope, which declares g, so a module
// reads 51 through `C::s`. The unit's classes are lowered before any
// module is, and the initializer was evaluated in no frame, resolving g by
// its bare key, which holds nothing once the unit's storage stands under
// "$unit.g": s read 1. LowerClassDecl (lowerer_class.cpp) now evaluates the
// initializer in a frame of the unit's scope.
TEST(CompilationUnitSim, CuScopeClassStaticInitializerReadsTheUnitsVariable) {
  EXPECT_EQ(UnitGRead("class C;\n"
                      "  static int s = g * 10 + 1;\n"
                      "endclass\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial y = C::s;\n"
                      "endmodule\n",
                      "y"),
            51u);
}

// A design whose compilation-unit scope declares `int g = 5;` and then the
// class `unit_class`, and whose top declares its own `int g = 7;`,
// constructs a C and reads `read * 10 + g` into y; answers y, in which the
// tens digit is what the class read and the units the top's own g.
static uint64_t UnitClassReadBesideTheTopsG(const std::string& unit_class,
                                            const std::string& read) {
  return UnitGRead(unit_class +
                       "module top;\n"
                       "  int g = 7;\n"
                       "  int y;\n"
                       "  C c;\n"
                       "  initial begin\n"
                       "    c = new;\n"
                       "    y = " +
                       read +
                       " * 10 + g;\n"
                       "  end\n"
                       "endmodule\n",
                   "y");
}

// §3.12.1 (printed page 56) with §8.7 (printed 184) and §23.9 (printed
// 761): the unit class's `int p = g;` is an expression of the class
// declaration's scope, the unit's, whose g is 5 whatever the constructing
// module declares, so `c.p * 10 + g` in a top with its own `int g = 7;` is
// 57. The defaults were read in a frame of no package
// (ConstructBaseThenDefaults in eval_class_new.cpp, as b0255e0e9 left a unit
// class), which resolved g through the top's instance prefix to the top's
// 7: 77.
TEST(CompilationUnitSim, CuScopeClassPropertyInitializerReadsTheUnitsVariable) {
  EXPECT_EQ(UnitClassReadBesideTheTopsG("class C;\n"
                                        "  int p = g;\n"
                                        "endclass\n",
                                        "c.p"),
            57u);
}

// §3.12.1 (printed page 56) with §23.9 (printed 761): a method of the unit
// class reads a bare g as the unit's 5, its body nested in the unit's scope
// and never in the calling module's, so `c.get() * 10 + g` is 57 beside
// the top's own g. The method's frame carried no scope (RecordClassPackage
// in lowerer_class.cpp recorded a package alone), so the bare g resolved
// through the calling instance's prefix to the top's 7: 77.
TEST(CompilationUnitSim, CuScopeClassMethodReadsTheUnitsVariable) {
  EXPECT_EQ(UnitClassReadBesideTheTopsG("class C;\n"
                                        "  function int get();\n"
                                        "    return g;\n"
                                        "  endfunction\n"
                                        "endclass\n",
                                        "c.get()"),
            57u);
}

// §3.12.1 (printed page 56) with §13.5.2 (printed 349): a ref formal is the
// actual variable itself, and `$unit::q` names the unit's queue past the
// top's own `int q[$]`, so `push($unit::q)` appends to the unit's queue and
// the by-value `qsize($unit::q)` copies that queue: 1 * 10 + the top's own
// empty q, 10. Both binds resolved the actual by its text
// (TryBindRefAggregateArg and TryBindArrayArg in eval_function_args.cpp),
// so the push landed in the top's queue and both counted it: 11. The size
// is read through a formal because `$unit::q.size()` is not parsed
// (Parser::ParseSystemCall returns the prefixed identifier with no postfix
// chain).
TEST(CompilationUnitSim, CuScopeQueueBoundByReferenceThroughUnitPrefix) {
  EXPECT_EQ(RunAndGet("int q[$];\n"
                      "module top;\n"
                      "  int q[$];\n"
                      "  int y;\n"
                      "  function automatic void push(ref int a[$]);\n"
                      "    a.push_back(1);\n"
                      "  endfunction\n"
                      "  function int qsize(int a[$]);\n"
                      "    return a.size();\n"
                      "  endfunction\n"
                      "  initial begin\n"
                      "    push($unit::q);\n"
                      "    y = qsize($unit::q) * 10 + q.size();\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            10u);
}

// §3.12.1 (printed page 56) with §13.5.2 (printed 349): `set3($unit::g)`
// binds the `ref int r` formal to the unit's g, so the write through the
// formal leaves the top's own `int g = 7` alone: `g * 10 + $unit::g` is 73.
// TryBindRefArg (eval_function_args.cpp) resolved the actual by its text,
// which bound the top's g: 35.
TEST(CompilationUnitSim, CuScopeVariableBoundByReferenceThroughUnitPrefix) {
  EXPECT_EQ(UnitGRead("module top;\n"
                      "  int g = 7;\n"
                      "  int y;\n"
                      "  function automatic void set3(ref int r);\n"
                      "    r = 3;\n"
                      "  endfunction\n"
                      "  initial begin\n"
                      "    set3($unit::g);\n"
                      "    y = g * 10 + $unit::g;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            73u);
}

// §3.12.1 (printed page 56) with §6.16 (printed 112): `$unit::s = "abcde"`
// writes the unit's `string s`, whose whole value a string assignment takes,
// so a unit class method's `s.len()` reads 5 and the top's own `int s = 7`
// stays 7: 57. The store asked the kind of the target by its text
// (IsStringTarget in statement_assign_core.cpp), found the top's int, and
// cut the value to the string's width: "e", 1, and 17. The length is read
// through the class because `$unit::s.len()` is not parsed
// (Parser::ParseSystemCall) and a unit function's frame carries no scope of
// the unit's, so its bare s is the calling module's.
TEST(CompilationUnitSim, CuScopeStringWrittenThroughUnitPrefixPastTheTopsInt) {
  EXPECT_EQ(RunAndGet("string s = \"x\";\n"
                      "class C;\n"
                      "  function int len();\n"
                      "    return s.len();\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module top;\n"
                      "  int s = 7;\n"
                      "  int y;\n"
                      "  C c;\n"
                      "  initial begin\n"
                      "    c = new;\n"
                      "    $unit::s = \"abcde\";\n"
                      "    y = c.len() * 10 + s;\n"
                      "  end\n"
                      "endmodule\n",
                      "y"),
            57u);
}

}  // namespace
