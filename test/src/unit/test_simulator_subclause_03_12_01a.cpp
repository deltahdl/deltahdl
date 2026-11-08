#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_scheduler.h"
#include "simulator/variable.h"

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
      "    static Reader o = new;\n"
      "    r = MID + 10 * o.is_high(HIGH);\n"
      "  end\n"
      "endmodule\n",
      "r");
  EXPECT_EQ(val, 11u);
}

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

TEST(CompilationUnitSim, CuScopeInitializerReadsAWildcardImportedVariable) {
  EXPECT_EQ(UnitInitializerRead("import p::*;\n"
                                "int g = K;\n"),
            4u);
}

TEST(CompilationUnitSim, CuScopeInitializerReadsAnExplicitlyImportedVariable) {
  EXPECT_EQ(UnitInitializerRead("import p::K;\n"
                                "int g = K * 10 + 1;\n"),
            41u);
}

TEST(CompilationUnitSim, CuScopeInitializerCallsAPackageFunction) {
  EXPECT_EQ(UnitInitializerRead("int g = p::f();\n"), 8u);
}

static uint64_t UnitGRead(const std::string& modules, const char* var_name) {
  return RunAndGet("int g = 5;\n" + modules, var_name);
}

TEST(CompilationUnitSim, CuScopeVariableShadowedByTheModulesOwnDeclaration) {
  EXPECT_EQ(UnitGRead("module top;\n"
                      "  int g = 7;\n"
                      "  int y;\n"
                      "  initial y = g;\n"
                      "endmodule\n",
                      "y"),
            7u);
}

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

TEST(CompilationUnitSim, CuScopeVariableNamedThroughUnitPrefixPastTheTopsOwn) {
  EXPECT_EQ(UnitGRead("module top;\n"
                      "  int g = 7;\n"
                      "  int y;\n"
                      "  initial y = g * 10 + $unit::g;\n"
                      "endmodule\n",
                      "y"),
            75u);
}

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

TEST(CompilationUnitSim, CuScopeClassPropertyInitializerReadsTheUnitsVariable) {
  EXPECT_EQ(UnitClassReadBesideTheTopsG("class C;\n"
                                        "  int p = g;\n"
                                        "endclass\n",
                                        "c.p"),
            57u);
}

TEST(CompilationUnitSim, CuScopeClassMethodReadsTheUnitsVariable) {
  EXPECT_EQ(UnitClassReadBesideTheTopsG("class C;\n"
                                        "  function int get();\n"
                                        "    return g;\n"
                                        "  endfunction\n"
                                        "endclass\n",
                                        "c.get()"),
            57u);
}

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

TEST(CompilationUnitSim, CuScopeQueueSizeThroughUnitPrefix) {
  EXPECT_EQ(RunAndGet("int q[$] = '{1, 2};\n"
                      "module top;\n"
                      "  int q[$] = '{5};\n"
                      "  int y;\n"
                      "  initial y = $unit::q.size() * 10 + q.size();\n"
                      "endmodule\n",
                      "y"),
            21u);
}

TEST(CompilationUnitSim, CuScopeStringLengthThroughUnitPrefix) {
  EXPECT_EQ(RunAndGet("string s = \"abcde\";\n"
                      "module top;\n"
                      "  string s = \"xy\";\n"
                      "  int y;\n"
                      "  initial y = $unit::s.len() * 10 + s.len();\n"
                      "endmodule\n",
                      "y"),
            52u);
}

TEST(CompilationUnitSim, CuScopeArrayElementThroughUnitPrefix) {
  EXPECT_EQ(RunAndGet("int arr[2] = '{7, 8};\n"
                      "module top;\n"
                      "  int arr[2] = '{1, 2};\n"
                      "  int y;\n"
                      "  initial y = $unit::arr[0] * 10 + arr[0];\n"
                      "endmodule\n",
                      "y"),
            71u);
}

static uint64_t UnitStringRead(const std::string& unit_items,
                               const std::string& body) {
  return RunAndGet("string s = \"unit\";\n" + unit_items +
                       "module top;\n"
                       "  string s = \"modulestring\";\n"
                       "  int y;\n"
                       "  initial " +
                       body +
                       "\n"
                       "endmodule\n",
                   "y");
}

TEST(CompilationUnitSim, CuScopeFunctionReadsTheUnitsVariable) {
  EXPECT_EQ(UnitStringRead("function int len_s();\n"
                           "  return s.len();\n"
                           "endfunction\n",
                           "y = len_s();"),
            4u);
}

TEST(CompilationUnitSim, CuScopeTaskReadsTheUnitsVariable) {
  EXPECT_EQ(UnitStringRead("task len_t(output int o);\n"
                           "  o = s.len();\n"
                           "endtask\n",
                           "len_t(y);"),
            4u);
}

TEST(CompilationUnitSim, CuScopeFunctionWritesTheUnitsVariable) {
  EXPECT_EQ(UnitStringRead("function int len_s();\n"
                           "  return s.len();\n"
                           "endfunction\n"
                           "function void set_s();\n"
                           "  s = \"x\";\n"
                           "endfunction\n",
                           "begin\n"
                           "    set_s();\n"
                           "    y = s.len() * 100 + len_s();\n"
                           "  end"),
            1201u);
}

TEST(CompilationUnitSim, CuScopeStructActualThroughUnitPrefix) {
  EXPECT_EQ(
      RunAndGet("typedef struct packed { logic [7:0] a, b; } st;\n"
                "st u = '{8'h12, 8'h34};\n"
                "module top;\n"
                "  typedef struct packed { logic [3:0] a; logic [11:0] b; }"
                " mt;\n"
                "  mt u = '{4'hA, 12'hBCD};\n"
                "  int y;\n"
                "  function int f(st x);\n"
                "    return x.b;\n"
                "  endfunction\n"
                "  initial y = f($unit::u);\n"
                "endmodule\n",
                "y"),
      0x34u);
}

TEST(CompilationUnitSim, CuScopeTaggedUnionActualThroughUnitPrefix) {
  EXPECT_EQ(RunAndGet("typedef union tagged { void Invalid; int Valid; } u_t;\n"
                      "u_t u = tagged Valid 9;\n"
                      "module top;\n"
                      "  u_t u = tagged Invalid;\n"
                      "  int y;\n"
                      "  function int f(u_t a);\n"
                      "    return a.Valid;\n"
                      "  endfunction\n"
                      "  initial y = f($unit::u);\n"
                      "endmodule\n",
                      "y"),
            9u);
}

TEST(CompilationUnitSim, CuScopeStructVariableMemberReadThroughUnitPrefix) {
  EXPECT_EQ(RunAndGet("typedef struct packed { logic [3:0] a; logic [11:0] b; }"
                      " st2;\n"
                      "st2 u = '{b: 12'hBCD, a: 4'hA};\n"
                      "module top;\n"
                      "  typedef struct packed { logic [7:0] a, b; } mt;\n"
                      "  mt u = '{8'h12, 8'h34};\n"
                      "  int y;\n"
                      "  initial y = $unit::u.b;\n"
                      "endmodule\n",
                      "y"),
            0xBCDu);
}

static Variable* RunUnitTaggedUnion(const std::string& top_items,
                                    SimFixture& f) {
  auto* design = ElaborateSrc(
      "typedef union tagged { void Invalid; int Valid; int Other; } u_t;\n"
      "u_t u = tagged Valid 9;\n"
      "module top;\n" +
          top_items + "endmodule\n",
      f);
  EXPECT_NE(design, nullptr);
  if (design == nullptr) return nullptr;
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  return f.ctx.FindVariable("y");
}

static std::string TopWithItsOwnUnion(const std::string& stmt) {
  return "  u_t u = tagged Other 3;\n"
         "  int y;\n"
         "  function int f(u_t a);\n"
         "    return a.Other;\n"
         "  endfunction\n"
         "  initial " +
         stmt + "\n";
}

TEST(CompilationUnitSim, CuScopeTaggedUnionActualCarriesTheUnitsTag) {
  SimFixture f;
  Variable* y = RunUnitTaggedUnion(TopWithItsOwnUnion("y = f($unit::u);"), f);
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0u);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "run-time error: accessing member 'Other' of "
                            "tagged union 'a' which currently has tag 'Valid'",
                            7, "11.9"));
}

TEST(CompilationUnitSim,
     CuScopeTaggedUnionMemberReadThroughUnitPrefixIsChecked) {
  SimFixture f;
  Variable* y =
      RunUnitTaggedUnion(TopWithItsOwnUnion("y = $unit::u.Other;"), f);
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0u);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "run-time error: accessing member 'Other' of tagged union '$unit.u' "
      "which currently has tag 'Valid'",
      9, "11.9"));
}

TEST(CompilationUnitSim, CuScopeStructVariableMemberReadByItsBareName) {
  EXPECT_EQ(RunAndGet("typedef struct packed { logic [3:0] a; logic [11:0] b; }"
                      " st2;\n"
                      "st2 u = '{b: 12'hBCD, a: 4'hA};\n"
                      "module top;\n"
                      "  int y;\n"
                      "  initial y = u.b;\n"
                      "endmodule\n",
                      "y"),
            0xBCDu);
}

TEST(CompilationUnitSim, CuScopeTaggedUnionRetaggedByItsBareNameIsOneTag) {
  SimFixture f;
  Variable* y = RunUnitTaggedUnion(
      "  int y;\n"
      "  initial begin\n"
      "    u = tagged Other 3;\n"
      "    y = $unit::u.Valid;\n"
      "  end\n",
      f);
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 0u);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "run-time error: accessing member 'Valid' of tagged union '$unit.u' "
      "which currently has tag 'Other'",
      7, "11.9"));
}

}  // namespace
