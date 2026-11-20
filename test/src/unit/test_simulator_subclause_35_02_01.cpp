#include <gtest/gtest.h>

#include <cstdint>
#include <map>
#include <string>

#include "fixture_simulator.h"
#include "helpers_dpi_c_binding.h"

using namespace delta;

namespace {

int AddOne(int a) { return a + 1; }
int Twice(int x) { return 2 * x; }
int TensAndUnits(int a, int b) { return (a * 10) + b; }
void BumpByFive(int* io) { *io += 5; }
int WriteOutAndInout(int a, int* o, int* io) {
  *o = a * 2;
  *io += a;
  return 0;
}
int TaskTensAndUnits(int a, int b, int* o) {
  *o = (a * 10) + b;
  return 0;
}
int calls_of_no_args = 0;
int CountACall() {
  ++calls_of_no_args;
  return 0;
}

struct BoundRun {
  SimFixture f;

  BoundRun(const std::string& src,
           const std::map<std::string, void*>& functions,
           const std::string& dir) {
    RunWithImportsBound(src, f, functions, "subclause_35_02_01_" + dir);
  }

  bool Clean() const { return f.diag.Diagnostics().empty(); }

  uint64_t Value(const char* name) {
    auto* v = f.ctx.FindVariable(name);
    return v == nullptr ? ~uint64_t{0} : v->value.ToUint64();
  }
};

std::map<std::string, void*> AddOneBound() {
  return {{"add_one", reinterpret_cast<void*>(&AddOne)}};
}

constexpr const char* kAddOneImport =
    "  import \"DPI-C\" function int add_one(input int a);\n";

std::string WithAddOne(const char* head, const char* tail) {
  return std::string(head) + kAddOneImport + tail;
}

TEST(DpiImportedSubroutineCall, AnImportCalledFromAClassMethodRuns) {
  BoundRun run(
      WithAddOne("module t;\n",
                 "  class C;\n"
                 "    function int m(); return add_one(6); endfunction\n"
                 "  endclass\n"
                 "  int r;\n"
                 "  C c;\n"
                 "  initial begin c = new; r = c.m(); end\n"
                 "endmodule\n"),
      AddOneBound(), "class_method");
  EXPECT_TRUE(run.Clean());
  EXPECT_EQ(run.Value("r"), 7U);
}

TEST(DpiImportedSubroutineCall, AnImportCalledInAContinuousAssignmentRuns) {
  BoundRun run(WithAddOne("module t;\n",
                          "  int a = 9;\n"
                          "  int w;\n"
                          "  assign w = add_one(a);\n"
                          "endmodule\n"),
               AddOneBound(), "continuous");
  EXPECT_TRUE(run.Clean());
  EXPECT_EQ(run.Value("w"), 10U);
}

TEST(DpiImportedSubroutineCall, AnImportCalledFromAPackageFunctionRuns) {
  BoundRun run(WithAddOne("package pk;\n",
                          "  function int via(input int a);\n"
                          "    return add_one(a);\n"
                          "  endfunction\n"
                          "endpackage\n"
                          "module t;\n"
                          "  int r;\n"
                          "  initial r = pk::via(10);\n"
                          "endmodule\n"),
               AddOneBound(), "package_function");
  EXPECT_TRUE(run.Clean());
  EXPECT_EQ(run.Value("r"), 11U);
}

TEST(DpiImportedSubroutineCall, AnImportCalledFromATaskRuns) {
  BoundRun run(WithAddOne("module t;\n",
                          "  task tk(output int o); o = add_one(20); endtask\n"
                          "  int r;\n"
                          "  initial tk(r);\n"
                          "endmodule\n"),
               AddOneBound(), "task");
  EXPECT_TRUE(run.Clean());
  EXPECT_EQ(run.Value("r"), 21U);
}

TEST(DpiImportedSubroutineCall, AnImportDeclaredInAProgramIsCalledFromIt) {
  BoundRun run(WithAddOne("program pr;\n",
                          "  int r;\n"
                          "  initial r = add_one(4);\n"
                          "endprogram\n"
                          "module t;\n"
                          "  pr p();\n"
                          "endmodule\n"),
               AddOneBound(), "program");
  EXPECT_TRUE(run.Clean());
  EXPECT_EQ(run.Value("p.r"), 5U);
}

TEST(DpiImportedSubroutineCall,
     AnImportDeclaredInAGenerateBlockIsCalledFromIt) {
  BoundRun run(WithAddOne("module t;\n"
                          "  int r;\n"
                          "  if (1) begin : g\n",
                          "    initial r = add_one(30);\n"
                          "  end\n"
                          "endmodule\n"),
               AddOneBound(), "generate");
  EXPECT_TRUE(run.Clean());
  EXPECT_EQ(run.Value("r"), 31U);
}

std::string InterfaceCall(const char* call) {
  return WithAddOne("interface ifc;\n",
                    "  function int through(input int a);\n"
                    "    return add_one(a) + 1;\n"
                    "  endfunction\n"
                    "endinterface\n"
                    "module t;\n"
                    "  ifc i();\n"
                    "  int r;\n") +
         "  initial r = " + call + ";\nendmodule\n";
}

TEST(DpiImportedSubroutineCall, AnInterfaceFunctionCallsTheInterfacesImport) {
  BoundRun run(InterfaceCall("i.through(100)"), AddOneBound(),
               "interface_function");
  EXPECT_TRUE(run.Clean());
  EXPECT_EQ(run.Value("r"), 102U);
}

TEST(DpiImportedSubroutineCall,
     DISABLED_AnInterfaceImportIsReachedThroughTheInstance) {
  BoundRun run(InterfaceCall("i.add_one(42)"), AddOneBound(),
               "interface_import");
  EXPECT_TRUE(run.Clean());
  EXPECT_EQ(run.Value("r"), 43U);
}

TEST(DpiImportedSubroutineCall,
     DISABLED_AnotherInstancesImportIsReachedByItsPath) {
  BoundRun run(WithAddOne("module inner;\n",
                          "endmodule\n"
                          "module t;\n"
                          "  inner u();\n"
                          "  int r;\n"
                          "  initial r = u.add_one(1);\n"
                          "endmodule\n"),
               AddOneBound(), "hierarchical");
  EXPECT_TRUE(run.Clean());
  EXPECT_EQ(run.Value("r"), 2U);
}

std::map<std::string, void*> TensAndUnitsBound() {
  return {{"tens_and_units", reinterpret_cast<void*>(&TensAndUnits)}};
}

constexpr const char* kTensAndUnitsImport =
    "module t;\n"
    "  import \"DPI-C\" function int tens_and_units(input int a,\n"
    "                                               input int b = 4);\n"
    "  int r;\n";

TEST(DpiImportedSubroutineCall, AnOmittedActualTakesTheDeclaredDefault) {
  BoundRun run(std::string(kTensAndUnitsImport) +
                   "  initial r = tens_and_units(1);\n"
                   "endmodule\n",
               TensAndUnitsBound(), "default");
  EXPECT_TRUE(run.Clean());
  EXPECT_EQ(run.Value("r"), 14U);
}

TEST(DpiImportedSubroutineCall, ActualsBoundByNameReachTheirFormals) {
  BoundRun run(std::string(kTensAndUnitsImport) +
                   "  initial r = tens_and_units(.b(2), .a(5));\n"
                   "endmodule\n",
               TensAndUnitsBound(), "named");
  EXPECT_TRUE(run.Clean());
  EXPECT_EQ(run.Value("r"), 52U);
}

TEST(DpiSharedForeignSubroutine, EachNameReachesOneFunctionWithItsOwnDefault) {
  BoundRun run(
      "module t;\n"
      "  import \"DPI-C\" twice = function int a(input int x = 1);\n"
      "  import \"DPI-C\" twice = function int b(input int x = 2);\n"
      "  int r;\n"
      "  int s;\n"
      "  initial begin r = a(); s = b(); end\n"
      "endmodule\n",
      {{"twice", reinterpret_cast<void*>(&Twice)}}, "shared");
  EXPECT_TRUE(run.Clean());
  EXPECT_EQ(run.Value("r"), 2U);
  EXPECT_EQ(run.Value("s"), 4U);
}

TEST(DpiImportedFormals, AnInoutOfAnImportedFunctionIsWrittenBack) {
  BoundRun run(
      "module t;\n"
      "  import \"DPI-C\" function void bump_by_five(inout int io);\n"
      "  int v = 10;\n"
      "  initial bump_by_five(v);\n"
      "endmodule\n",
      {{"bump_by_five", reinterpret_cast<void*>(&BumpByFive)}}, "inout");
  EXPECT_TRUE(run.Clean());
  EXPECT_EQ(run.Value("v"), 15U);
}

TEST(DpiImportedFormals, AnImportedTasksOutputAndInoutAreWrittenBack) {
  BoundRun run(
      "module t;\n"
      "  import \"DPI-C\" task write_out_and_inout(input int a,\n"
      "                                           output int o,\n"
      "                                           inout int io);\n"
      "  int o;\n"
      "  int io = 100;\n"
      "  initial write_out_and_inout(3, o, io);\n"
      "endmodule\n",
      {{"write_out_and_inout", reinterpret_cast<void*>(&WriteOutAndInout)}},
      "task_outputs");
  EXPECT_TRUE(run.Clean());
  EXPECT_EQ(run.Value("o"), 6U);
  EXPECT_EQ(run.Value("io"), 103U);
}

TEST(DpiImportedTaskEnable, AnImportedTaskEnableBindsByNameAndDefault) {
  BoundRun run(
      "module t;\n"
      "  import \"DPI-C\" task task_tens_and_units(input int a,\n"
      "                                           input int b = 7,\n"
      "                                           output int o);\n"
      "  int r;\n"
      "  initial task_tens_and_units(.o(r), .a(3));\n"
      "endmodule\n",
      {{"task_tens_and_units", reinterpret_cast<void*>(&TaskTensAndUnits)}},
      "task_named");
  EXPECT_TRUE(run.Clean());
  EXPECT_EQ(run.Value("r"), 37U);
}

void ExpectOneCallOfTheTaskWithNoFormalList(const char* enable,
                                            const char* dir) {
  calls_of_no_args = 0;
  BoundRun run(std::string("module t;\n"
                           "  import \"DPI-C\" task count_a_call;\n"
                           "  initial ") +
                   enable + ";\nendmodule\n",
               {{"count_a_call", reinterpret_cast<void*>(&CountACall)}}, dir);
  EXPECT_TRUE(run.Clean());
  EXPECT_EQ(calls_of_no_args, 1);
}

TEST(DpiImportedTaskEnable, ATaskImportWithNoFormalListIsDeclaredAndEnabled) {
  ExpectOneCallOfTheTaskWithNoFormalList("count_a_call()", "no_formals");
}

TEST(DpiImportedTaskEnable, DISABLED_ATaskImportIsEnabledWithoutParentheses) {
  ExpectOneCallOfTheTaskWithNoFormalList("count_a_call", "bare_enable");
}

TEST(DpiExportedTaskEnable, AnExportedTaskEnabledFromSvConsumesTime) {
  BoundRun run(
      "module t;\n"
      "  export \"DPI-C\" task sv_t;\n"
      "  task sv_t(output int o); #3 o = 9; endtask\n"
      "  int r;\n"
      "  longint s;\n"
      "  initial begin sv_t(r); s = $time; end\n"
      "endmodule\n",
      {}, "export_time");
  EXPECT_TRUE(run.Clean());
  EXPECT_EQ(run.Value("r"), 9U);
  EXPECT_EQ(run.Value("s"), 3U);
}

TEST(DpiExportedTaskEnable, ADisableEndsAnExportedTaskAsANativeOne) {
  BoundRun run(
      "module t;\n"
      "  export \"DPI-C\" task sv_t;\n"
      "  int done;\n"
      "  int after;\n"
      "  task sv_t(); #5 done = 1; endtask\n"
      "  initial begin\n"
      "    fork begin : run sv_t(); end join_none\n"
      "    #1 disable run;\n"
      "    #10 after = 1;\n"
      "  end\n"
      "endmodule\n",
      {}, "export_disable");
  EXPECT_TRUE(run.Clean());
  EXPECT_EQ(run.Value("done"), 0U);
  EXPECT_EQ(run.Value("after"), 1U);
}

}  // namespace
