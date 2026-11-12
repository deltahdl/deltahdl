#include <gtest/gtest.h>

#include <initializer_list>
#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(FunctionBackgroundProcessElaboration, ForkJoinNoneOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function void my_func();\n"
      "    fork\n"
      "      a = 1;\n"
      "    join_none\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionBackgroundProcessElaboration, NonblockingAssignOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  function void set_x();\n"
      "    x <= 1;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionBackgroundProcessElaboration, EventTriggerOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  event e;\n"
      "  function void fire_event();\n"
      "    -> e;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionBackgroundProcessElaboration, ClockingDriveOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk;\n"
      "  logic sig;\n"
      "  clocking cb @(posedge clk);\n"
      "    output sig;\n"
      "  endclocking\n"
      "  function void drive_it();\n"
      "    cb.sig <= 1'b1;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionBackgroundProcessElaboration, DelayInsideForkJoinNoneOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function void spawn_delayed();\n"
      "    fork\n"
      "      #10 $display(\"done\");\n"
      "    join_none\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionBackgroundProcessElaboration, ForkJoinError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void my_func();\n"
      "    fork\n"
      "      a = 1;\n"
      "    join\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "only fork/join_none is permitted inside a function", 3, "13.4"));
}

TEST(FunctionBackgroundProcessElaboration, ForkJoinAnyError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  function void my_func();\n"
      "    fork\n"
      "      a = 1;\n"
      "    join_any\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "only fork/join_none is permitted inside a function", 3, "13.4"));
}

TEST(FunctionBackgroundProcessElaboration, TaskEnableInsideForkJoinNoneOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task t(); endtask\n"
      "  function void f();\n"
      "    fork\n"
      "      t();\n"
      "    join_none\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionBackgroundProcessElaboration, ContAssignToFuncWithNbaError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic q;\n"
      "  logic r;\n"
      "  function automatic logic spawn_nba();\n"
      "    q <= 1'b1;\n"
      "    return 1'b0;\n"
      "  endfunction\n"
      "  assign r = spawn_nba();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "function 'spawn_nba' schedules a background event and cannot be called "
      "outside an initial/always procedure or fork block",
      8, "13.4.4"));
}

TEST(FunctionBackgroundProcessElaboration,
     ContAssignToFuncWithForkJoinNoneError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic r;\n"
      "  function automatic logic spawn_bg();\n"
      "    fork\n"
      "      $display(\"bg\");\n"
      "    join_none\n"
      "    return 1'b1;\n"
      "  endfunction\n"
      "  assign r = spawn_bg();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "function 'spawn_bg' schedules a background event and cannot be called "
      "outside an initial/always procedure or fork block",
      9, "13.4.4"));
}

TEST(FunctionBackgroundProcessElaboration,
     ContAssignToFuncWithEventTriggerError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  event e;\n"
      "  logic r;\n"
      "  function automatic logic spawn_trigger();\n"
      "    -> e;\n"
      "    return 1'b1;\n"
      "  endfunction\n"
      "  assign r = spawn_trigger();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "function 'spawn_trigger' schedules a background "
                            "event and cannot be called outside an "
                            "initial/always procedure or fork block",
                            8, "13.4.4"));
}

TEST(FunctionBackgroundProcessElaboration, NbEventTriggerOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  event e;\n"
      "  function void fire_nb();\n"
      "    ->> e;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionBackgroundProcessElaboration,
     ContAssignToFuncWithNbEventTriggerError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  event e;\n"
      "  logic r;\n"
      "  function automatic logic spawn_nb_trigger();\n"
      "    ->> e;\n"
      "    return 1'b1;\n"
      "  endfunction\n"
      "  assign r = spawn_nb_trigger();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "function 'spawn_nb_trigger' schedules a background "
                    "event and cannot be called outside an "
                    "initial/always procedure or fork block",
                    8, "13.4.4"));
}

TEST(FunctionBackgroundProcessElaboration, ContAssignToPureFuncOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic r;\n"
      "  function automatic logic pure_func(input logic a);\n"
      "    return ~a;\n"
      "  endfunction\n"
      "  logic in;\n"
      "  assign r = pure_func(in);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionBackgroundProcessElaboration, VarInitToBackgroundFuncNbaError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic q;\n"
      "  function automatic logic spawn_nba();\n"
      "    q <= 1'b1;\n"
      "    return 1'b0;\n"
      "  endfunction\n"
      "  logic y = spawn_nba();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "function 'spawn_nba' schedules a background event and cannot be called "
      "outside an initial/always procedure or fork block",
      7, "13.4.4"));
}

TEST(FunctionBackgroundProcessElaboration, NetDeclInitToBackgroundFuncError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic q;\n"
      "  function automatic logic spawn_nba();\n"
      "    q <= 1'b1;\n"
      "    return 1'b0;\n"
      "  endfunction\n"
      "  wire y = spawn_nba();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "function 'spawn_nba' schedules a background event and cannot be called "
      "outside an initial/always procedure or fork block",
      7, "13.4.4"));
}

TEST(FunctionBackgroundProcessElaboration, VarInitToPureFuncOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  function automatic logic pure_func(input logic a);\n"
      "    return ~a;\n"
      "  endfunction\n"
      "  logic in;\n"
      "  logic y = pure_func(in);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionBackgroundProcessElaboration, InitialCallToBackgroundFuncOk) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic q;\n"
      "  function automatic logic spawn_nba();\n"
      "    q <= 1'b1;\n"
      "    return 1'b0;\n"
      "  endfunction\n"
      "  logic r;\n"
      "  initial r = spawn_nba();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionBackgroundProcessElaboration,
     ContAssignToFuncWithNbaInRandsequenceCodeBlockError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic q;\n"
      "  logic r;\n"
      "  function automatic logic spawn_rs();\n"
      "    randsequence(main)\n"
      "      main : { q <= 1'b1; };\n"
      "    endsequence\n"
      "    return 1'b0;\n"
      "  endfunction\n"
      "  assign r = spawn_rs();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "function 'spawn_rs' schedules a background event and cannot be called "
      "outside an initial/always procedure or fork block",
      10, "13.4.4"));
}

TEST(FunctionBackgroundProcessElaboration,
     ContAssignToFuncWithNbaInRandsequenceWeightCodeBlockError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic q;\n"
      "  logic r;\n"
      "  int i;\n"
      "  function automatic logic spawn_rs_weight();\n"
      "    randsequence(main)\n"
      "      main : alt := 1 { q <= 1'b1; };\n"
      "      alt : { i = 1; };\n"
      "    endsequence\n"
      "    return 1'b0;\n"
      "  endfunction\n"
      "  assign r = spawn_rs_weight();\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "function 'spawn_rs_weight' schedules a background "
                            "event and cannot be called outside an "
                            "initial/always procedure or fork block",
                            12, "13.4.4"));
}

TEST(FunctionBackgroundProcessElaboration,
     BackgroundEventThroughAnotherFunction) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  logic q, y, z;\n"
      "  function int g(); q <= 1; return 1; endfunction\n"
      "  function int f(); return g(); endfunction\n"
      "  function automatic int r(int n); return n > 0 ? r(n - 1) : 0;\n"
      "  endfunction\n"
      "  assign y = f();\n"
      "  assign z = r(2);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "function 'f' schedules a background event and "
                            "cannot be called",
                            7, "13.4.4"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "function 'r' schedules a background event", 8,
                             "13.4.4"));
}

constexpr const char* kSchedulesBackground =
    "schedules a background event and cannot be called outside an "
    "initial/always procedure or fork block";

std::string BackgroundReport(const std::string& func) {
  return "function '" + func + "' " + kSchedulesBackground;
}

TEST(FunctionBackgroundProcessElaboration,
     TheClauseExampleReportsTheInitializerAndAcceptsBothInitialCalls) {
  ElabFixture f;
  const std::string kSrc =
      "class IntClass;\n"
      "  int a;\n"
      "endclass\n"
      "module m;\n"
      "  IntClass address = new(), stack = new();\n"
      "  function automatic bit watch_for_zero(IntClass p);\n"
      "    fork\n"
      "      forever @p.a begin\n"
      "        if (p.a == 0) $display(\"Unexpected zero\");\n"
      "      end\n"
      "    join_none\n"
      "    return (p.a == 0);\n"
      "  endfunction\n"
      "  function bit start_check();\n"
      "    return (watch_for_zero(address) | watch_for_zero(stack));\n"
      "  endfunction\n"
      "  bit y = watch_for_zero(stack);\n"
      "  initial if (start_check()) $display(\"OK\");\n"
      "  initial fork\n"
      "    if (start_check()) $display(\"OK too\");\n"
      "  join_none\n"
      "endmodule\n";
  ElaborateSrc(kSrc, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            BackgroundReport("watch_for_zero"),
                            LineHolding(kSrc, "bit y ="), "13.4.4"));
  EXPECT_FALSE(ErrorOnLine(f.diag.Diagnostics(), LineHolding(kSrc, "\"OK\"")));
  EXPECT_FALSE(
      ErrorOnLine(f.diag.Diagnostics(), LineHolding(kSrc, "\"OK too\"")));
}

TEST(FunctionBackgroundProcessElaboration,
     AContinuousAssignmentOfAFunctionWithAClockingDriveIsReported) {
  ElabFixture f;
  const std::string kSrc =
      "module m(input logic clk);\n"
      "  logic sig, r, s;\n"
      "  clocking cb @(posedge clk);\n"
      "    output sig;\n"
      "  endclocking\n"
      "  function automatic logic drive_it();\n"
      "    cb.sig <= 1'b1;\n"
      "    return 1'b0;\n"
      "  endfunction\n"
      "  assign r = drive_it();\n"
      "  initial s = drive_it();\n"
      "endmodule\n";
  ElaborateSrc(kSrc, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), BackgroundReport("drive_it"),
                            LineHolding(kSrc, "assign r"), "13.4.4"));
  EXPECT_FALSE(
      ErrorOnLine(f.diag.Diagnostics(), LineHolding(kSrc, "initial s")));
}

TEST(FunctionBackgroundProcessElaboration,
     ACallFromAnAlwaysProcedureOrAForkOfOneIsAccepted) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input logic clk);\n"
      "  logic q, qf, r1, r2, r3, r4, r5;\n"
      "  function automatic logic spawn_nba();\n"
      "    q <= 1'b1;\n"
      "    return 1'b0;\n"
      "  endfunction\n"
      "  function automatic logic spawn_ff();\n"
      "    qf <= 1'b1;\n"
      "    return 1'b0;\n"
      "  endfunction\n"
      "  function automatic logic spawn_bg();\n"
      "    fork\n"
      "      #1 q = 1'b0;\n"
      "    join_none\n"
      "    return 1'b1;\n"
      "  endfunction\n"
      "  always @(posedge clk) r1 = spawn_nba();\n"
      "  always_ff @(posedge clk) r2 <= spawn_ff();\n"
      "  initial fork\n"
      "    r3 = spawn_bg();\n"
      "  join\n"
      "  always @(negedge clk) fork\n"
      "    r4 = spawn_nba();\n"
      "    r5 = spawn_bg();\n"
      "  join_any\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(FunctionBackgroundProcessElaboration,
     DISABLED_ACallFromAFinalProcedureIsReported) {
  ElabFixture f;
  const std::string kSrc =
      "module m;\n"
      "  logic q, r, s;\n"
      "  function automatic logic spawn_nba();\n"
      "    q <= 1'b1;\n"
      "    return 1'b0;\n"
      "  endfunction\n"
      "  final r = spawn_nba();\n"
      "  initial s = spawn_nba();\n"
      "endmodule\n";
  ElaborateSrc(kSrc, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), BackgroundReport("spawn_nba"),
                            LineHolding(kSrc, "final r"), "13.4.4"));
  EXPECT_FALSE(
      ErrorOnLine(f.diag.Diagnostics(), LineHolding(kSrc, "initial s")));
}

void ExpectContinuousCallsReported(const std::string& src,
                                   std::initializer_list<const char*> funcs) {
  ElabFixture f;
  ElaborateSrc(src, f);
  for (const char* func : funcs) {
    EXPECT_TRUE(ReportedError(
        f.diag.Diagnostics(), BackgroundReport(func),
        LineHolding(src, std::string("assign r = ") + func), "13.4.4"));
    EXPECT_FALSE(
        ErrorOnLine(f.diag.Diagnostics(),
                    LineHolding(src, std::string("initial s = ") + func)));
  }
}

TEST(FunctionBackgroundProcessElaboration,
     AContinuousCallIsReportedInAnInterfaceAndAProgram) {
  ExpectContinuousCallsReported(
      "interface i;\n"
      "  logic q, r, s;\n"
      "  function automatic logic ispawn();\n"
      "    q <= 1'b1;\n"
      "    return 1'b0;\n"
      "  endfunction\n"
      "  assign r = ispawn();\n"
      "  initial s = ispawn();\n"
      "endinterface\n"
      "program p;\n"
      "  logic q, r, s;\n"
      "  function automatic logic pspawn();\n"
      "    q <= 1'b1;\n"
      "    return 1'b0;\n"
      "  endfunction\n"
      "  assign r = pspawn();\n"
      "  initial s = pspawn();\n"
      "endprogram\n"
      "module m;\n"
      "  i u();\n"
      "  p v();\n"
      "endmodule\n",
      {"ispawn", "pspawn"});
}

TEST(FunctionBackgroundProcessElaboration,
     DISABLED_AContinuousCallIsReportedInAGenerateBlock) {
  ExpectContinuousCallsReported(
      "module m;\n"
      "  if (1) begin : g\n"
      "    logic q, r, s;\n"
      "    function automatic logic gspawn();\n"
      "      q <= 1'b1;\n"
      "      return 1'b0;\n"
      "    endfunction\n"
      "    assign r = gspawn();\n"
      "    initial s = gspawn();\n"
      "  end\n"
      "  for (genvar k = 0; k < 1; k++) begin : fg\n"
      "    logic q, r, s;\n"
      "    function automatic logic fspawn();\n"
      "      q <= 1'b1;\n"
      "      return 1'b0;\n"
      "    endfunction\n"
      "    assign r = fspawn();\n"
      "    initial s = fspawn();\n"
      "  end\n"
      "endmodule\n",
      {"gspawn", "fspawn"});
}

TEST(FunctionBackgroundProcessElaboration,
     DISABLED_APackageOrUnitVariableInitializerCallIsReported) {
  ElabFixture f;
  const std::string kSrc =
      "package pk;\n"
      "  logic q;\n"
      "  function automatic logic pkspawn();\n"
      "    q <= 1'b1;\n"
      "    return 1'b0;\n"
      "  endfunction\n"
      "  logic y = pkspawn();\n"
      "endpackage\n"
      "logic uq;\n"
      "function automatic logic uspawn();\n"
      "  uq <= 1'b1;\n"
      "  return 1'b0;\n"
      "endfunction\n"
      "logic uy = uspawn();\n"
      "module m;\n"
      "  logic s, t;\n"
      "  initial s = pk::pkspawn();\n"
      "  initial t = uspawn();\n"
      "endmodule\n";
  ElaborateSrc(kSrc, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), BackgroundReport("pkspawn"),
                            LineHolding(kSrc, "logic y ="), "13.4.4"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), BackgroundReport("uspawn"),
                            LineHolding(kSrc, "logic uy ="), "13.4.4"));
  EXPECT_FALSE(
      ErrorOnLine(f.diag.Diagnostics(), LineHolding(kSrc, "initial s")));
  EXPECT_FALSE(
      ErrorOnLine(f.diag.Diagnostics(), LineHolding(kSrc, "initial t")));
}

TEST(FunctionBackgroundProcessElaboration,
     AForkJoinNoneInAFunctionHoldsAnyTaskStatement) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  event e;\n"
      "  logic c, x;\n"
      "  task t(); #1 x = 0; endtask\n"
      "  function void spawn_all();\n"
      "    fork\n"
      "      @(e) x = 1;\n"
      "      wait (c) x = 0;\n"
      "      forever #5 x = ~x;\n"
      "      begin\n"
      "        fork #1 x = 1; #2 x = 0; join\n"
      "        fork #3 x = 1; join_any\n"
      "        wait fork;\n"
      "        x = @(e) c;\n"
      "        t();\n"
      "      end\n"
      "    join_none\n"
      "  endfunction\n"
      "  class C;\n"
      "    event ce;\n"
      "    int v;\n"
      "    task ct(); #1 v = 2; endtask\n"
      "    function void spawn();\n"
      "      fork\n"
      "        begin @ce; wait (v > 0); fork ct(); join wait fork; end\n"
      "      join_none\n"
      "    endfunction\n"
      "  endclass\n"
      "  initial spawn_all();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
