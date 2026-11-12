#include <gtest/gtest.h>

#include <initializer_list>
#include <string>

#include "common/diagnostic.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

const char kIllegal[] = "not legally callable in the Postponed region";

std::string InTop(const std::string& item, const std::string& body = "") {
  return "package pk; logic pv; task pmut; pv = 1; endtask endpackage\n"
         "logic uv; task umut; uv = 1; endtask\n"
         "class C; int v; static int s; task m; v = 1; endtask "
         "function void fm; v = 2; endfunction "
         "static task sm; s = 1; endtask endclass\n"
         "module top;\n"
         "  logic [7:0] x; logic [7:0] mem [0:1]; event ev;\n"
         "  task mut; x = 8'd1; endtask\n"
         "  task outer; mut(); endtask\n"
         "  task body_task; " +
         body +
         " endtask\n"
         "  function void fmut; x = 8'd2; endfunction\n"
         "  task tout(output logic [7:0] o); o = 8'd3; endtask\n"
         "  task automatic tref(ref logic [7:0] r); r = 8'd4; endtask\n"
         "  task rep; $display(\"rep x=%0d\", x); endtask\n"
         "  task show(input logic [7:0] v); $display(v); endtask\n"
         "  C c = new;\n"
         "  " +
         item +
         "\n"
         "endmodule\n";
}

void ExpectReported(const std::string& src, int line) {
  ElabFixture f;
  Elaborate(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kIllegal, line, "16.4"))
      << src;
}

void ExpectAccepted(const std::string& src) {
  ElabFixture f;
  ASSERT_NE(Elaborate(src, f), nullptr) << src;
  EXPECT_FALSE(f.has_errors) << src;
  for (const auto& d : f.diag.Diagnostics()) {
    EXPECT_EQ(d.message.find("Postponed region"), std::string::npos)
        << d.message << "\n"
        << src;
  }
}

TEST(FinalDeferredCallee,
     DISABLED_AWritingTaskIsReportedOnEveryFinalDirective) {
  for (const char* item : {"initial assert final (1) mut();",
                           "initial assert final (0) else mut();",
                           "initial assume final (1) mut();",
                           "initial assume final (0) else mut();",
                           "initial cover final (1) mut();"}) {
    ExpectReported(InTop(item), 15);
  }
}

TEST(FinalDeferredCallee, DISABLED_EveryWayOfWritingInTheCalleeIsReported) {
  for (const char* body :
       {"x <= 8'd2;", "x++;", "x += 1;", "assign x = 8'd1; deassign x;",
        "force x = 8'd1; release x;", "-> ev;", "->> ev;", "#0;",
        "logic [7:0] l; l = 8'd1;"}) {
    ExpectReported(InTop("initial assert final (1) body_task();", body), 15);
  }
}

TEST(FinalDeferredCallee, DISABLED_EveryKindOfWritingCalleeIsReported) {
  for (const char* item :
       {"initial assert final (1) fmut();", "initial assert final (1) tout(x);",
        "initial assert final (1) tref(x);",
        "initial assert final (1) $readmemh(\"f\", mem);",
        "initial assert final (1) outer();", "initial assert final (1) c.m();",
        "initial assert final (1) c.fm();", "initial assert final (1) C::sm();",
        "initial assert final (1) pk::pmut();",
        "initial assert final (1) umut();"}) {
    ExpectReported(InTop(item), 15);
  }
}

TEST(FinalDeferredCallee, DISABLED_EveryPlaceInAModuleIsReported) {
  for (const char* item :
       {"sf: assert final (1) mut();",
        "if (1) begin : g initial assert final (1) mut(); end",
        "for (genvar j = 0; j < 1; j++) begin : lg "
        "sf: assert final (1) mut(); end",
        "function void fn; assert final (1) fmut(); endfunction"}) {
    ExpectReported(InTop(item), 15);
  }
}

std::string InUnit(const std::string& open, const std::string& close,
                   const std::string& item) {
  return open +
         "\n"
         "  logic [7:0] x; logic [7:0] mem [0:1];\n"
         "  function void show; $display(x); endfunction\n"
         "  " +
         item + "\n" + close + "\nmodule top; u_unit u(); endmodule\n";
}

TEST(FinalDeferredCallee, DISABLED_AnInterfaceProgramOrCheckerIsReported) {
  for (const char* open : {"interface u_unit;", "program u_unit;"}) {
    std::string close =
        open[0] == 'i' ? "endinterface" : std::string("endprogram");
    ExpectReported(
        InUnit(open, close,
               "task mut; x = 8'd1; endtask initial assert final (1) mut();"),
        4);
    ExpectAccepted(InUnit(open, close, "initial assert final (1) show();"));
  }
  ExpectReported(InUnit("checker u_unit;", "endchecker",
                        "initial assert final (1) $readmemh(\"f\", mem);"),
                 4);
  ExpectAccepted(InUnit("checker u_unit;", "endchecker",
                        "initial assert final (1) show();"));
}

TEST(FinalDeferredCallee,
     DISABLED_AClassMethodCallingAWritingSiblingIsReported) {
  ExpectReported(
      "class D;\n"
      "  int v;\n"
      "  task m2; v = 1; endtask\n"
      "  task m1; assert final (1) m2(); endtask\n"
      "endclass\n"
      "module top; D d = new; endmodule\n",
      4);
}

TEST(FinalDeferredCallee, AClassMethodCallingAReadingSiblingIsAccepted) {
  ExpectAccepted(
      "class D;\n"
      "  int v;\n"
      "  task m2; $display(v); endtask\n"
      "  task m1; assert final (1) m2(); endtask\n"
      "endclass\n"
      "module top; D d = new; endmodule\n");
}

TEST(FinalDeferredCallee, AReadingCalleeIsAccepted) {
  ExpectAccepted(InTop("initial assert final (1) rep();"));
  ExpectAccepted(InTop("initial assert final (1) show(x);"));
  ExpectAccepted(InTop("initial assert #0 (1) mut();"));
  for (const char* body : {"$strobe(x);", "$monitor(x);"}) {
    ExpectAccepted(InTop("initial assert final (1) body_task();", body));
  }
}

TEST(FinalDeferredCallee, DISABLED_ACalleeWaitingIntoALaterSlotIsAccepted) {
  for (const char* body : {"#1 $display(x);", "@(ev) $display(x);"}) {
    ExpectAccepted(InTop("initial assert final (1) body_task();", body));
  }
}

}  // namespace
