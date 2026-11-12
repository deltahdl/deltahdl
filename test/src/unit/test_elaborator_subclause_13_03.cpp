#include <gtest/gtest.h>

#include <cstddef>
#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

TEST(TaskElaboration, TaskDeclInModuleElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  task my_task(input int a);\n"
      "    $display(\"a=%0d\", a);\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(TaskElaboration, TaskWithOutputArgsElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  task compute(input int a, output int b);\n"
      "    b = a * 2;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TaskElaboration, TaskWithInoutArgElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  task inc(inout int v);\n"
      "    v = v + 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TaskElaboration, TaskEmptyBodyElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  task nop;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TaskElaboration, TaskEnablesTaskElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  task inner;\n"
      "  endtask\n"
      "  task outer;\n"
      "    inner();\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TaskElaboration, TaskWithRefArgElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  task automatic inc(ref int v);\n"
      "    v = v + 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TaskElaboration, RefStaticQualifierStickyInheritedAtElaboration) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  task t(ref static int a, b);\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->function_decls.size(), 1u);
  auto* tk = mod->function_decls[0];
  ASSERT_EQ(tk->func_args.size(), 2u);
  EXPECT_EQ(tk->func_args[0].direction, Direction::kRef);
  EXPECT_TRUE(tk->func_args[0].is_ref_static);
  EXPECT_EQ(tk->func_args[1].direction, Direction::kRef);
  EXPECT_TRUE(tk->func_args[1].is_ref_static);
}

TEST(TaskElaboration, ReturnValueDeclaredNames13_3) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task t();\n"
      "    return 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "task returns a value", 3, "13.3"));
}

TEST(TaskElaboration, ReturnValueInAnAssertionPassStmtIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task t();\n"
      "    assert (1) return 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "task returns a value", 3, "13.3"));
}

TEST(TaskElaboration, ReturnValueInAnAssertionFailStmtIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task t();\n"
      "    assert (1) else return 1;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "task returns a value", 3, "13.3"));
}

TEST(TaskElaboration, ReturnValueInARandcaseItemIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task t();\n"
      "    randcase 1 : return 1; endcase\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "task returns a value", 3, "13.3"));
}

TEST(TaskElaboration, ValueReturningProductionInATaskOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task t();\n"
      "    randsequence(main)\n"
      "      void main : a { return; };\n"
      "      int a : { return 7; };\n"
      "    endsequence\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TaskElaboration, ImportedTaskAsAnExpressionOperandIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  import \"DPI-C\" task t(input int a);\n"
      "  int x;\n"
      "  initial x = t(1);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "task 't' is enabled from a statement and cannot "
                            "be an operand of an expression",
                            4, "13.3"));
}

TEST(TaskElaboration, NativeTaskAsAnExpressionOperandIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task t(input int a);\n"
      "  endtask\n"
      "  int x;\n"
      "  initial x = t(1) + 2;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "task 't' is enabled from a statement and cannot "
                            "be an operand of an expression",
                            5, "13.3"));
}

TEST(TaskElaboration, TaskEnabledAsAStatementBesideAFunctionOperandOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task t(input int a);\n"
      "  endtask\n"
      "  function int g(input int a);\n"
      "    return a;\n"
      "  endfunction\n"
      "  int x;\n"
      "  initial begin\n"
      "    t(1);\n"
      "    x = g(1);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TaskElaboration, TaskOperandInContinuousAssignError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic y;\n"
      "  task t; endtask\n"
      "  assign y = t();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "task 't' is enabled from a statement and "
                            "cannot be an operand of an expression",
                            4, "13.3"));
}

TEST(TaskElaboration, TaskOperandInDeclarationInitializerError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task t; endtask\n"
      "  int v = t();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "task 't' is enabled from a statement and "
                            "cannot be an operand of an expression",
                            3, "13.3"));
}

TEST(TaskElaboration, TaskOperandInGenerateBlockError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int x;\n"
      "  task t; endtask\n"
      "  if (1) begin : g\n"
      "    initial x = t();\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "task 't' is enabled from a statement and "
                            "cannot be an operand of an expression",
                            5, "13.3"));
}

TEST(TaskElaboration, PackageAndUnitTaskOperandsError) {
  ElabFixture f;
  ElaborateSrc(
      "package pk; task t; endtask endpackage\n"
      "task u; endtask\n"
      "module m;\n"
      "  int x;\n"
      "  initial begin\n"
      "    x = pk::t();\n"
      "    x = u();\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "task 'pk::t' is enabled from a statement and "
                            "cannot be an operand of an expression",
                            6, "13.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "task 'u' is enabled from a statement and cannot "
                            "be an operand of an expression",
                            7, "13.3"));
}

TEST(TaskElaboration, ModuleFunctionHidesUnitTask) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "task u; endtask\n"
      "module m;\n"
      "  int x;\n"
      "  function int u(); return 1; endfunction\n"
      "  initial x = u();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TaskElaboration, TaskOperandInGenerateElseAndCaseArmsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  int x;\n"
      "  task t; endtask\n"
      "  if (0) begin : a\n"
      "  end else begin : b\n"
      "    initial x = t();\n"
      "  end\n"
      "  case (1)\n"
      "    1: begin : c\n"
      "      initial x = t();\n"
      "    end\n"
      "  endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "task 't' is enabled from a statement and "
                            "cannot be an operand of an expression",
                            6, "13.3"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "task 't' is enabled from a statement and "
                            "cannot be an operand of an expression",
                            10, "13.3"));
}

TEST(TaskElaboration, BodyDeclarationTypingADirectionOnlyFormalElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  task mytask2;\n"
      "    output x;\n"
      "    input y;\n"
      "    int x;\n"
      "    logic y;\n"
      "    x = y;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TaskElaboration, BodyDeclarationThatTypesNoFormalIsARedeclaration) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  task t;\n"
      "    input int a;\n"
      "    input b;\n"
      "    input c;\n"
      "    int a;\n"
      "    int b = 1;\n"
      "    localparam int c = 2;\n"
      "  endtask\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'a'", 6, "23.9"));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'b'", 7, "23.9"));
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "redeclaration of 'c'", 8, "23.9"));
}

struct TaskPlace {
  const char* head;
  const char* tail;
  int line;
};

constexpr TaskPlace kTaskPlaces[] = {
    {"module m;\n", "endmodule\n", 2},
    {"interface i;\n", "endinterface\nmodule m; i u(); endmodule\n", 2},
    {"program p;\n", "endprogram\n", 2},
    {"module m;\n  if (1) begin : g\n", "  end\nendmodule\n", 3},
    {"module m;\n  for (genvar k = 0; k < 1; k++) begin : g\n",
     "  end\nendmodule\n", 3}};

constexpr TaskPlace kClassTaskPlaces[] = {
    {"class C;\n", "endclass\nmodule m; endmodule\n", 2}};

constexpr TaskPlace kPackageClassTaskPlaces[] = {
    {"package q;\nclass C;\n", "endclass\nendpackage\nmodule m; endmodule\n",
     3}};

constexpr TaskPlace kPackageAndUnitTaskPlaces[] = {
    {"package pk;\n", "endpackage\nmodule m; endmodule\n", 2},
    {"", "module m; endmodule\n", 1}};

constexpr const char* kTaskReturnsAValue = "task returns a value";
constexpr const char* kTaskOverrideMisplaced =
    "a task's dynamic_override_specifiers belong on a class method "
    "declaration";
constexpr const char* kTaskOperand =
    "is enabled from a statement and cannot be an operand of an expression";

std::string TaskIn(const TaskPlace& place, const std::string& task) {
  return std::string(place.head) + "  " + task + "\n" + place.tail;
}

bool TaskElaboratesClean(const std::string& src) {
  ElabFixture f;
  ElaborateSrc(src, f);
  return !f.diag.HasErrors();
}

bool TaskElaborationReports(const std::string& src, const char* message,
                            int line) {
  ElabFixture f;
  ElaborateSrc(src, f);
  return ReportedError(f.diag.Diagnostics(), message, line, "13.3");
}

template <std::size_t N>
void ExpectTaskReported(const TaskPlace (&places)[N], const char* task,
                        const char* message) {
  for (const auto& place : places) {
    EXPECT_TRUE(
        TaskElaborationReports(TaskIn(place, task), message, place.line))
        << TaskIn(place, task);
  }
}

template <std::size_t N>
void ExpectTaskAccepted(const TaskPlace (&places)[N], const char* task) {
  for (const auto& place : places) {
    EXPECT_TRUE(TaskElaboratesClean(TaskIn(place, task)))
        << TaskIn(place, task);
  }
}

constexpr const char* kValueReturn = "task t(); return 1; endtask";
constexpr const char* kBareReturn =
    "task t(output int r); r = 1; if (r == 1) return; r = 2; endtask";

TEST(TaskReturnElaboration, AValueReturnedFromATaskIsReportedInEveryPlace) {
  ExpectTaskReported(kTaskPlaces, kValueReturn, kTaskReturnsAValue);
  ExpectTaskReported(kClassTaskPlaces, kValueReturn, kTaskReturnsAValue);
}

TEST(TaskReturnElaboration,
     DISABLED_AValueReturnedFromATaskInAPackageOrTheUnitIsReported) {
  ExpectTaskReported(kPackageAndUnitTaskPlaces, kValueReturn,
                     kTaskReturnsAValue);
  ExpectTaskReported(kPackageClassTaskPlaces, kValueReturn, kTaskReturnsAValue);
}

TEST(TaskReturnElaboration, ABareReturnFromATaskIsAcceptedInEveryPlace) {
  ExpectTaskAccepted(kTaskPlaces, kBareReturn);
  ExpectTaskAccepted(kClassTaskPlaces, kBareReturn);
  ExpectTaskAccepted(kPackageAndUnitTaskPlaces, kBareReturn);
  ExpectTaskAccepted(kPackageClassTaskPlaces, kBareReturn);
}

constexpr const char* kOverriddenTasks[] = {
    "task :initial t(); endtask", "task :extends t(); endtask",
    "task :final t(); endtask", "task :initial :final t(); endtask"};

TEST(TaskOverrideElaboration,
     ADynamicOverrideOnATaskOutsideAClassIsReportedInEveryPlace) {
  for (const char* task : kOverriddenTasks) {
    ExpectTaskReported(kTaskPlaces, task, kTaskOverrideMisplaced);
    ExpectTaskReported(kPackageAndUnitTaskPlaces, task, kTaskOverrideMisplaced);
  }
}

TEST(TaskOverrideElaboration,
     ADynamicOverrideOnATaskDefinedOutsideItsScopeIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "  extern task :initial t();\n"
      "endclass\n"
      "task :initial C::t(); endtask\n"
      "interface bus;\n"
      "  extern task put(int d);\n"
      "endinterface\n"
      "module m (bus b);\n"
      "  task :final b.put(int d); endtask\n"
      "endmodule\n"
      "module top;\n"
      "  bus i ();\n"
      "  m u (i);\n"
      "endmodule\n",
      f);
  for (int line : {4, 9}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kTaskOverrideMisplaced,
                              line, "13.3"))
        << line;
  }
}

TEST(TaskOverrideElaboration, ADynamicOverrideOnAClassTaskIsAccepted) {
  ExpectTaskAccepted(kClassTaskPlaces, "virtual task :initial t(); endtask");
  ExpectTaskAccepted(kPackageClassTaskPlaces,
                     "virtual task :initial t(); endtask");
  EXPECT_TRUE(
      TaskElaboratesClean("class C;\n"
                          "  virtual task :initial t(); endtask\n"
                          "endclass\n"
                          "class D extends C;\n"
                          "  virtual task :extends t(); endtask\n"
                          "endclass\n"
                          "class E extends D;\n"
                          "  task :final t(); endtask\n"
                          "endclass\n"
                          "class G;\n"
                          "  extern task :initial u();\n"
                          "endclass\n"
                          "task G::u(); endtask\n"
                          "module m; endmodule\n"));
}

struct TaskOperandForm {
  const char* operand;
  const char* statement;
  int line;
};

constexpr TaskOperandForm kOwnTaskOperands[] = {
    {"module m;\n  int x;\n  task t(); endtask\n  task outer;\n"
     "    x = t();\n  endtask\nendmodule\n",
     "module m;\n  int x;\n  task t(); endtask\n  task outer;\n"
     "    t();\n  endtask\nendmodule\n",
     5},
    {"program p;\n  int x;\n  task t; endtask\n  initial x = t();\n"
     "endprogram\n",
     "program p;\n  int x;\n  task t; endtask\n  initial t();\n"
     "endprogram\n",
     4},
    {"interface i;\n  int x;\n  task t; endtask\n  initial x = t();\n"
     "endinterface\nmodule m; i u(); endmodule\n",
     "interface i;\n  int x;\n  task t; endtask\n  initial t();\n"
     "endinterface\nmodule m; i u(); endmodule\n",
     4},
    {"module m;\n  int x;\n  task t; endtask\n"
     "  for (genvar k = 0; k < 1; k++) begin : g\n"
     "    initial x = t();\n  end\nendmodule\n",
     "module m;\n  int x;\n  task t; endtask\n"
     "  for (genvar k = 0; k < 1; k++) begin : g\n"
     "    initial t();\n  end\nendmodule\n",
     5}};

constexpr TaskOperandForm kNamedTaskOperands[] = {
    {"class C;\n  task t(); endtask\nendclass\nmodule m;\n  C h = new;\n"
     "  int x;\n  initial x = h.t();\nendmodule\n",
     "class C;\n  task t(); endtask\nendclass\nmodule m;\n  C h = new;\n"
     "  int x;\n  initial h.t();\nendmodule\n",
     7},
    {"class C;\n  int x;\n  task t(); endtask\n  task u();\n"
     "    x = t();\n  endtask\nendclass\nmodule m; endmodule\n",
     "class C;\n  int x;\n  task t(); endtask\n  task u();\n"
     "    t();\n  endtask\nendclass\nmodule m; endmodule\n",
     5},
    {"class C;\n  int x;\n  task t(); endtask\n  task u();\n"
     "    x = this.t();\n  endtask\nendclass\nmodule m; endmodule\n",
     "class C;\n  int x;\n  task t(); endtask\n  task u();\n"
     "    this.t();\n  endtask\nendclass\nmodule m; endmodule\n",
     5},
    {"class B;\n  task t(); endtask\nendclass\nclass D extends B;\n"
     "  int x;\n  task u();\n    x = super.t();\n  endtask\nendclass\n"
     "module m; endmodule\n",
     "class B;\n  task t(); endtask\nendclass\nclass D extends B;\n"
     "  int x;\n  task u();\n    super.t();\n  endtask\nendclass\n"
     "module m; endmodule\n",
     7},
    {"module c;\n  task t(); endtask\nendmodule\nmodule m;\n  int x;\n"
     "  c u1();\n  initial x = u1.t();\nendmodule\n",
     "module c;\n  task t(); endtask\nendmodule\nmodule m;\n  int x;\n"
     "  c u1();\n  initial u1.t();\nendmodule\n",
     7},
    {"interface i;\n  task t(); endtask\nendinterface\nmodule n(i b);\n"
     "  int x;\n  initial x = b.t();\nendmodule\n"
     "module m;\n  i u();\n  n k(u);\nendmodule\n",
     "interface i;\n  task t(); endtask\nendinterface\nmodule n(i b);\n"
     "  int x;\n  initial b.t();\nendmodule\n"
     "module m;\n  i u();\n  n k(u);\nendmodule\n",
     6}};

TEST(TaskOperandElaboration,
     ATaskOperandInATaskAProgramAnInterfaceOrALoopGenerateIsReported) {
  for (const auto& form : kOwnTaskOperands) {
    EXPECT_TRUE(TaskElaborationReports(form.operand, kTaskOperand, form.line))
        << form.operand;
  }
}

TEST(
    TaskOperandElaboration,
    DISABLED_ATaskOperandThroughAHandleThisSuperOrAHierarchicalNameIsReported) {
  for (const auto& form : kNamedTaskOperands) {
    EXPECT_TRUE(TaskElaborationReports(form.operand, kTaskOperand, form.line))
        << form.operand;
  }
}

TEST(TaskOperandElaboration, TheSameTaskEnabledAsAStatementIsAccepted) {
  for (const auto& form : kOwnTaskOperands) {
    EXPECT_TRUE(TaskElaboratesClean(form.statement)) << form.statement;
  }
  for (const auto& form : kNamedTaskOperands) {
    EXPECT_TRUE(TaskElaboratesClean(form.statement)) << form.statement;
  }
}

}  // namespace
