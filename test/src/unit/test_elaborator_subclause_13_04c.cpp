#include <gtest/gtest.h>

#include <algorithm>
#include <cstddef>
#include <string>
#include <vector>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

struct FunctionScope {
  const char* opening;
  const char* closing;
};

struct BodyLine {
  const char* statement;
  const char* report;
};

std::string FunctionWithin(const FunctionScope& scope,
                           const std::vector<std::string>& body) {
  std::string src = scope.opening;
  src += "  function void f();\n";
  for (const auto& statement : body) src += "    " + statement + "\n";
  return src + "  endfunction\n" + scope.closing;
}

int FirstBodyLineOf(const FunctionScope& scope) {
  std::string opening = scope.opening;
  return static_cast<int>(std::count(opening.begin(), opening.end(), '\n')) + 2;
}

template <std::size_t S, std::size_t L>
void ExpectEachLineReported(const FunctionScope (&scopes)[S],
                            const BodyLine (&lines)[L]) {
  std::vector<std::string> body;
  for (const auto& line : lines) body.emplace_back(line.statement);
  for (const auto& scope : scopes) {
    std::string src = FunctionWithin(scope, body);
    ElabFixture f;
    ElaborateSrc(src, f);
    for (std::size_t k = 0; k < L; ++k) {
      EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), lines[k].report,
                                FirstBodyLineOf(scope) + static_cast<int>(k),
                                "13.4"))
          << lines[k].statement << "\n"
          << src;
    }
  }
}

template <std::size_t S>
void ExpectBodyAccepted(const FunctionScope (&scopes)[S],
                        const std::vector<std::string>& body) {
  for (const auto& scope : scopes) {
    std::string src = FunctionWithin(scope, body);
    ElabFixture f;
    ElaborateSrc(src, f);
    EXPECT_FALSE(f.diag.HasErrors()) << src;
  }
}

constexpr const char* kTimeControlInFunction =
    "time-controlling statement is not allowed inside a function";
constexpr const char* kBlockingForkInFunction =
    "only fork/join_none is permitted inside a function";
constexpr const char* kTaskEnableInFunction = "function cannot enable a task";

constexpr FunctionScope kCheckedTimeScopes[] = {
    {"module m;\n  event e, e2;\n  bit b, c;\n", "endmodule\n"},
    {"interface i;\n  event e, e2;\n  bit b, c;\n",
     "endinterface\nmodule m;\n  i u();\nendmodule\n"},
    {"program p;\n  event e, e2;\n  bit b, c;\n", "endprogram\n"},
    {"module m;\n  event e, e2;\n  bit b, c;\n  if (1) begin : g\n",
     "  end\nendmodule\n"},
    {"module m;\n  event e, e2;\n  bit b, c;\n"
     "  for (genvar k = 0; k < 2; k++) begin : g\n",
     "  end\nendmodule\n"},
    {"class C;\n  event e, e2;\n  bit b, c;\n",
     "endclass\nmodule m;\nendmodule\n"},
    {"module m;\n  class C;\n  event e, e2;\n  bit b, c;\n",
     "  endclass\nendmodule\n"}};

constexpr FunctionScope kUncheckedTimeScopes[] = {
    {"package q;\n  event e, e2;\n  bit b, c;\n",
     "endpackage\nmodule m;\nendmodule\n"},
    {"event e, e2;\nbit b, c;\n", "module m;\nendmodule\n"},
    {"package q;\n  class C;\n  event e, e2;\n  bit b, c;\n",
     "  endclass\nendpackage\nmodule m;\nendmodule\n"}};

constexpr FunctionScope kClockedScopes[] = {
    {"module m;\n  bit c;\n  default clocking cb @(posedge c); endclocking\n",
     "endmodule\n"},
    {"interface i;\n  bit c;\n"
     "  default clocking cb @(posedge c); endclocking\n",
     "endinterface\nmodule m;\n  i u();\nendmodule\n"},
    {"program p;\n  bit c;\n  default clocking cb @(posedge c); endclocking\n",
     "endprogram\n"},
    {"module m;\n  bit c;\n  default clocking cb @(posedge c); endclocking\n"
     "  if (1) begin : g\n",
     "  end\nendmodule\n"}};

constexpr BodyLine kTimeControls[] = {
    {"#1;", kTimeControlInFunction},
    {"@(e);", kTimeControlInFunction},
    {"wait (b);", kTimeControlInFunction},
    {"wait fork;", kTimeControlInFunction},
    {"wait_order (e, e2);", kTimeControlInFunction},
    {"expect (@(posedge c) b);", kTimeControlInFunction},
    {"b = #1 b;", kTimeControlInFunction},
    {"b = @(e) b;", kTimeControlInFunction},
    {"b <= #1 b;", kTimeControlInFunction},
    {"fork join", kBlockingForkInFunction},
    {"fork join_any", kBlockingForkInFunction}};

constexpr BodyLine kCycleDelays[] = {{"##1;", kTimeControlInFunction}};

TEST(FunctionTimeControlElaboration,
     EveryTimeControlInAFunctionIsReportedInEveryPlace) {
  ExpectEachLineReported(kCheckedTimeScopes, kTimeControls);
}

TEST(FunctionTimeControlElaboration,
     DISABLED_EveryTimeControlInAPackageUnitOrPackageClassFunctionIsReported) {
  ExpectEachLineReported(kUncheckedTimeScopes, kTimeControls);
}

TEST(FunctionTimeControlElaboration,
     ACycleDelayInAFunctionIsReportedInEveryClockedPlace) {
  ExpectEachLineReported(kClockedScopes, kCycleDelays);
}

TEST(FunctionTimeControlElaboration,
     StatementsThatDoNotBlockAreAcceptedInAFunctionInEveryPlace) {
  std::vector<std::string> body = {"b <= 1;", "-> e;",
                                   "fork #1 b = 0; join_none"};
  ExpectBodyAccepted(kCheckedTimeScopes, body);
  ExpectBodyAccepted(kUncheckedTimeScopes, body);
}

constexpr FunctionScope kCheckedTaskScopes[] = {
    {"module m;\n  task t; endtask\n", "endmodule\n"},
    {"interface i;\n  task t; endtask\n",
     "endinterface\nmodule m;\n  i u();\nendmodule\n"},
    {"program p;\n  task t; endtask\n", "endprogram\n"}};

constexpr FunctionScope kUncheckedTaskScopes[] = {
    {"module m;\n  task t; endtask\n  if (1) begin : g\n",
     "  end\nendmodule\n"},
    {"module m;\n  for (genvar k = 0; k < 2; k++) begin : g\n"
     "  task t; endtask\n",
     "  end\nendmodule\n"},
    {"package pk;\n  task t; endtask\n", "endpackage\nmodule m;\nendmodule\n"},
    {"task t; endtask\n", "module m;\nendmodule\n"},
    {"class C;\n  task t; endtask\n", "endclass\nmodule m;\nendmodule\n"},
    {"module m;\n  class C;\n  task t; endtask\n", "  endclass\nendmodule\n"},
    {"package q;\n  class C;\n  task t; endtask\n",
     "  endclass\nendpackage\nmodule m;\nendmodule\n"}};

constexpr FunctionScope kClassTaskScopes[] = {
    {"class C;\n  task t; endtask\n", "endclass\nmodule m;\nendmodule\n"},
    {"module m;\n  class C;\n  task t; endtask\n", "  endclass\nendmodule\n"},
    {"class B;\n  task t; endtask\nendclass\nclass C extends B;\n",
     "endclass\nmodule m;\nendmodule\n"}};

constexpr BodyLine kOwnTaskEnable[] = {{"t();", kTaskEnableInFunction}};

TEST(FunctionTaskEnableElaboration,
     ATaskEnabledFromAModuleInterfaceOrProgramFunctionIsReported) {
  ExpectEachLineReported(kCheckedTaskScopes, kOwnTaskEnable);
}

TEST(FunctionTaskEnableElaboration,
     DISABLED_ATaskEnabledFromAGeneratePackageUnitOrClassFunctionIsReported) {
  ExpectEachLineReported(kUncheckedTaskScopes, kOwnTaskEnable);
}

TEST(FunctionTaskEnableElaboration,
     DISABLED_AClassTaskEnabledThroughThisSuperOrInheritanceIsReported) {
  constexpr BodyLine kThisEnable[] = {{"this.t();", kTaskEnableInFunction}};
  constexpr BodyLine kSuperEnable[] = {{"super.t();", kTaskEnableInFunction}};
  constexpr FunctionScope kDerivedScope[] = {kClassTaskScopes[2]};
  ExpectEachLineReported(kClassTaskScopes, kThisEnable);
  ExpectEachLineReported(kDerivedScope, kSuperEnable);
  ExpectEachLineReported(kDerivedScope, kOwnTaskEnable);
}

TEST(FunctionTaskEnableElaboration,
     ATaskEnabledInsideForkJoinNoneOfAFunctionIsAcceptedInEveryPlace) {
  std::vector<std::string> body = {"fork t(); join_none"};
  ExpectBodyAccepted(kCheckedTaskScopes, body);
  ExpectBodyAccepted(kUncheckedTaskScopes, body);
  ExpectBodyAccepted(kClassTaskScopes,
                     {"fork this.t(); join_none", "fork t(); join_none"});
  constexpr FunctionScope kDerivedScope[] = {kClassTaskScopes[2]};
  ExpectBodyAccepted(kDerivedScope, {"fork super.t(); join_none"});
}

constexpr FunctionScope kNamedTaskScopes[] = {
    {"class K;\n  task t; endtask\nendclass\nmodule m;\n  K h;\n",
     "endmodule\n"},
    {"module c;\n  task t; endtask\nendmodule\nmodule m;\n  c u1();\n",
     "endmodule\n"},
    {"interface i;\n  task t; endtask\nendinterface\nmodule n(i b);\n",
     "endmodule\nmodule m;\n  i u();\n  n k(u);\nendmodule\n"},
    {"module m;\n  process p;\n", "endmodule\n"}};

constexpr const char* kNamedTaskEnables[] = {"h.t();", "u1.t();", "b.t();",
                                             "p.await();"};

TEST(FunctionTaskEnableElaboration,
     DISABLED_ATaskEnabledThroughAHandleAHierarchicalNameOrAPortIsReported) {
  for (std::size_t k = 0; k < 4; ++k) {
    BodyLine lines[] = {{kNamedTaskEnables[k], kTaskEnableInFunction}};
    FunctionScope scope[] = {kNamedTaskScopes[k]};
    ExpectEachLineReported(scope, lines);
  }
}

TEST(FunctionTaskEnableElaboration,
     ATaskEnabledThroughAHandleAHierarchicalNameOrAPortInForkJoinNoneIsOk) {
  for (std::size_t k = 0; k < 3; ++k) {
    FunctionScope scope[] = {kNamedTaskScopes[k]};
    ExpectBodyAccepted(
        scope, {std::string("fork ") + kNamedTaskEnables[k] + " join_none"});
  }
}

TEST(FunctionTaskEnableElaboration,
     DISABLED_AClassFunctionHidingAModuleTaskOfItsNameIsCalledFreely) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  task t; endtask\n"
      "  class B;\n"
      "    function void t(); endfunction\n"
      "  endclass\n"
      "  class K extends B;\n"
      "    function void f(); t(); this.t(); endfunction\n"
      "  endclass\n"
      "  class L;\n"
      "    function void t(); endfunction\n"
      "    function void f(); t(); this.t(); endfunction\n"
      "  endclass\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(FunctionTaskEnableElaboration,
     APackageFunctionHidingAUnitTaskOfItsNameIsCalledFreely) {
  ElabFixture f;
  ElaborateSrc(
      "task t; endtask\n"
      "package pk;\n"
      "  function void t(); endfunction\n"
      "  function void f(); t(); endfunction\n"
      "endpackage\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(FunctionProcessControlElaboration,
     AFunctionMaySuspendResumeAndKillAProcessInEveryPlace) {
  constexpr FunctionScope kProcessScopes[] = {
      {"module m;\n", "endmodule\n"},
      {"interface i;\n", "endinterface\nmodule m;\n  i u();\nendmodule\n"},
      {"program p0;\n", "endprogram\n"},
      {"module m;\n  if (1) begin : g\n", "  end\nendmodule\n"},
      {"package q;\n", "endpackage\nmodule m;\nendmodule\n"},
      {"", "module m;\nendmodule\n"},
      {"class C;\n", "endclass\nmodule m;\nendmodule\n"}};
  ExpectBodyAccepted(kProcessScopes,
                     {"process p;", "p = process::self();", "p.suspend();",
                      "p.resume();", "p.kill();"});
}

struct RestrictedCall {
  const char* src;
  int line;
  const char* report;
};

constexpr const char* kOutputInContinuousAssignment =
    "has output argument; cannot be called in a continuous assignment";
constexpr const char* kOutputInInitializer =
    "has output argument; cannot be called in a declaration's initializer";
constexpr const char* kOutputInEventExpression =
    "has output argument; cannot be called in an event expression";

void ExpectRestrictedCallReported(const RestrictedCall& call) {
  ElabFixture f;
  ElaborateSrc(call.src, f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), call.report, call.line, "13.4"))
      << call.src;
}

void ExpectCallAccepted(const char* src) {
  ElabFixture f;
  ElaborateSrc(src, f);
  EXPECT_FALSE(f.diag.HasErrors()) << src;
}

constexpr RestrictedCall kReportedOutputCalls[] = {
    {"interface i;\n  int y, z;\n"
     "  function int f(output int o); o = 1; return 1; endfunction\n"
     "  assign z = f(y);\nendinterface\nmodule m;\n  i u();\nendmodule\n",
     4, kOutputInContinuousAssignment},
    {"program p;\n  int y, z;\n"
     "  function int f(output int o); o = 1; return 1; endfunction\n"
     "  assign z = f(y);\nendprogram\n",
     4, kOutputInContinuousAssignment},
    {"module m;\n  int y, z;\n"
     "  function int f(output int o); o = 1; return 1; endfunction\n"
     "  if (1) begin : g\n    assign z = f(y);\n  end\nendmodule\n",
     5, kOutputInContinuousAssignment},
    {"module m;\n  int y;\n"
     "  function int f(output int o); o = 1; return 1; endfunction\n"
     "  wire [31:0] z = f(y);\nendmodule\n",
     4, kOutputInInitializer},
    {"interface i;\n  int y;\n"
     "  function int f(output int o); o = 1; return 1; endfunction\n"
     "  int z = f(y);\nendinterface\nmodule m;\n  i u();\nendmodule\n",
     4, kOutputInInitializer},
    {"program p;\n  int y;\n"
     "  function int f(output int o); o = 1; return 1; endfunction\n"
     "  int z = f(y);\nendprogram\n",
     4, kOutputInInitializer},
    {"module m;\n  int y;\n"
     "  function int f(output int o); o = 1; return 1; endfunction\n"
     "  if (1) begin : g\n    int z = f(y);\n  end\nendmodule\n",
     5, kOutputInInitializer},
    {"interface i;\n  int y, z;\n"
     "  function int f(output int o); o = 1; return 1; endfunction\n"
     "  initial @(f(y)) z = 1;\nendinterface\nmodule m;\n  i u();\n"
     "endmodule\n",
     4, kOutputInEventExpression},
    {"program p;\n  int y, z;\n"
     "  function int f(output int o); o = 1; return 1; endfunction\n"
     "  initial @(f(y)) z = 1;\nendprogram\n",
     4, kOutputInEventExpression},
    {"module m;\n  int y, z;\n"
     "  function int f(output int o); o = 1; return 1; endfunction\n"
     "  if (1) begin : g\n    initial @(f(y)) z = 1;\n  end\nendmodule\n",
     5, kOutputInEventExpression},
    {"module m;\n  int y, z;\n  bit c;\n"
     "  function int f(output int o); o = 1; return 1; endfunction\n"
     "  initial @(posedge c iff f(y)) z = 1;\nendmodule\n",
     5, kOutputInEventExpression},
    {"module m;\n  int y, z;\n"
     "  function int f(inout int o); return o; endfunction\n"
     "  initial @(f(y)) z = 1;\nendmodule\n",
     4, "has inout argument; cannot be called in an event expression"},
    {"module m;\n  int y, z;\n"
     "  function automatic int f(ref int o); return o; endfunction\n"
     "  initial @(f(y)) z = 1;\nendmodule\n",
     4, "has ref argument; cannot be called in an event expression"},
    {"module m;\n  int y, z;\n"
     "  function int f(inout int o); return o; endfunction\n"
     "  initial assign z = f(y);\nendmodule\n",
     4,
     "has inout argument; cannot be called in a procedural continuous "
     "assignment"},
    {"module m;\n  int y, z;\n"
     "  function automatic int f(ref int o); return o; endfunction\n"
     "  initial force z = f(y);\nendmodule\n",
     4,
     "has ref argument; cannot be called in a procedural continuous "
     "assignment"},
    {"module m;\n  int y, z;\n"
     "  function int f(output int o); o = 1; return 1; endfunction\n"
     "  initial force z = f(y);\nendmodule\n",
     4,
     "has output argument; cannot be called in a procedural continuous "
     "assignment"}};

TEST(FunctionRestrictedCallElaboration,
     AnOutputInoutOrRefFunctionOutsideAProceduralStatementIsReported) {
  for (const auto& call : kReportedOutputCalls) {
    ExpectRestrictedCallReported(call);
  }
}

constexpr RestrictedCall kUnreportedOutputCalls[] = {
    {"package q;\n  int y;\n"
     "  function int f(output int o); o = 1; return 1; endfunction\n"
     "  int z = f(y);\nendpackage\nmodule m;\nendmodule\n",
     4, kOutputInInitializer},
    {"int y;\n"
     "function int f(output int o); o = 1; return 1; endfunction\n"
     "int z = f(y);\nmodule m;\nendmodule\n",
     3, kOutputInInitializer},
    {"package q;\n  int y, z;\n"
     "  function int f(output int o); o = 1; return 1; endfunction\n"
     "  task automatic t(); @(f(y)) z = 1; endtask\nendpackage\n"
     "module m;\nendmodule\n",
     4, kOutputInEventExpression},
    {"int y, z;\n"
     "function int f(output int o); o = 1; return 1; endfunction\n"
     "task automatic t(); @(f(y)) z = 1; endtask\nmodule m;\nendmodule\n",
     3, kOutputInEventExpression},
    {"class C;\n  int y, z;\n"
     "  function int f(output int o); o = 1; return 1; endfunction\n"
     "  task t(); @(f(y)) z = 1; endtask\nendclass\nmodule m;\nendmodule\n",
     4, kOutputInEventExpression},
    {"module m;\n  class C;\n  int y, z;\n"
     "  function int f(output int o); o = 1; return 1; endfunction\n"
     "  task t(); @(f(y)) z = 1; endtask\n  endclass\nendmodule\n",
     5, kOutputInEventExpression},
    {"package q;\n"
     "  function int f(output int o); o = 1; return 1; endfunction\n"
     "endpackage\nmodule m;\n  int y, z;\n  assign z = q::f(y);\n"
     "endmodule\n",
     6, kOutputInContinuousAssignment},
    {"function int f(output int o); o = 1; return 1; endfunction\n"
     "module m;\n  int y, z;\n  assign z = f(y);\nendmodule\n",
     4, kOutputInContinuousAssignment},
    {"class C;\n"
     "  static function int f(output int o); o = 1; return 1; endfunction\n"
     "endclass\nmodule m;\n  int y, z;\n  assign z = C::f(y);\nendmodule\n",
     6, kOutputInContinuousAssignment},
    {"interface i;\n"
     "  function int f(output int o); o = 1; return 1; endfunction\n"
     "endinterface\nmodule m;\n  i u();\n  int y, z;\n"
     "  assign z = u.f(y);\nendmodule\n",
     7, kOutputInContinuousAssignment},
    {"module c(input logic [31:0] a);\nendmodule\nmodule m;\n  int y;\n"
     "  function int f(output int o); o = 1; return 1; endfunction\n"
     "  c u(.a(f(y)));\nendmodule\n",
     6, "has output argument; cannot be called in"}};

TEST(FunctionRestrictedCallElaboration,
     DISABLED_AnOutputFunctionOutsideAProceduralStatementIsReportedAnywhere) {
  for (const auto& call : kUnreportedOutputCalls) {
    ExpectRestrictedCallReported(call);
  }
}

TEST(FunctionRestrictedCallElaboration,
     AConstRefOrInputFunctionAndAnyCallInAProceduralStatementAreAccepted) {
  ExpectCallAccepted(
      "module m;\n  int y, z, v;\n  wire [31:0] w;\n"
      "  function automatic int g(const ref int o); return o; endfunction\n"
      "  function int h(int o); return o; endfunction\n"
      "  int q = g(y) + h(y);\n"
      "  initial @(g(y) or h(y)) z = 2;\n"
      "  initial force w = g(y) + h(y);\nendmodule\n");
  ExpectCallAccepted(
      "package q;\n  int y;\n"
      "  function int h(int o); return o; endfunction\n"
      "  int z = h(y);\nendpackage\nmodule m;\nendmodule\n");
  ExpectCallAccepted(
      "module m;\n  int y, z, v;\n"
      "  function int f(output int o); o = 1; return 1; endfunction\n"
      "  initial z = f(y);\n"
      "  always @(z) v = f(y);\n"
      "  initial if (f(y) == 1) z = 3;\nendmodule\n");
}

}  // namespace
