#include <gtest/gtest.h>

#include <initializer_list>
#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

const char kPass[] =
    "deferred assertion pass action shall be a single subroutine call";
const char kFail[] =
    "deferred assertion fail action shall be a single subroutine call";

struct Form {
  const char* item;
  const char* message;
};

std::string InTop(const std::string& item) {
  return "package pk; task pt; endtask endpackage\n"
         "class B; virtual function void vm; endfunction endclass\n"
         "class K extends B; task t; endtask function void vf; endfunction "
         "static function void sf; endfunction endclass\n"
         "interface ifc; function void f; endfunction endinterface\n"
         "module top;\n"
         "  logic c; int x; event ev;\n"
         "  task tk; endtask\n"
         "  function void vf; endfunction\n"
         "  function int nv; return 1; endfunction\n"
         "  K k = new;\n"
         "  ifc i();\n"
         "  " +
         item +
         "\n"
         "endmodule\n";
}

void ExpectAccepted(const std::string& src) {
  ElabFixture f;
  auto* design = Elaborate(src, f);
  ASSERT_NE(design, nullptr) << src;
  EXPECT_FALSE(f.has_errors) << src;
}

void ExpectReported(const std::string& src, const char* message, int line) {
  ElabFixture f;
  Elaborate(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, line, "16.4"))
      << src;
}

void ExpectEachAccepted(std::initializer_list<const char*> items) {
  for (const char* item : items) ExpectAccepted(InTop(item));
}

void ExpectEachReported(std::initializer_list<Form> forms) {
  for (const auto& form : forms) {
    ExpectReported(InTop(form.item), form.message, 12);
  }
}

TEST(DeferredActionSingleCall, TaskAndVoidFunctionMethodsAreSingleCalls) {
  ExpectEachAccepted({"initial assert #0 (c) k.t();",
                      "initial assume final (c) k.t(); else k.t();",
                      "initial assert #0 (c) else k.vf();"});
}

TEST(DeferredActionSingleCall, EachAssumeFormTakesASingleCall) {
  ExpectEachAccepted({"initial assume #0 (c) tk(); else vf();",
                      "initial assume final (c) vf(); else $info(\"x\");"});
}

TEST(DeferredActionSingleCall, EveryWayOfNamingTheCalleeIsASingleCall) {
  ExpectEachAccepted({"initial assert #0 (c) top.tk();",
                      "initial assert #0 (c) pk::pt();",
                      "initial assert #0 (c) K::sf();",
                      "initial assert final (c) else i.f();"});
  ExpectAccepted(
      "class B; virtual function void vm; endfunction endclass\n"
      "class D extends B;\n"
      "  function void vm; endfunction\n"
      "  function void chk(int x);\n"
      "    assert #0 (x > 0) this.vm(); else super.vm();\n"
      "  endfunction\n"
      "endclass\n"
      "module top; D d = new; endmodule\n");
}

TEST(DeferredActionSingleCall, ANonvoidOrSystemFunctionCallIsASingleCall) {
  ExpectEachAccepted(
      {"initial assert #0 (c) nv();", "initial assert #0 (c) else $random;"});
}

TEST(DeferredActionSingleCall, DISABLED_ACallWithoutParenthesesIsASingleCall) {
  ExpectEachAccepted(
      {"initial assert #0 (c) tk;", "initial assert #0 (c) else vf;",
       "initial assert #0 (c) k.t;", "initial assert #0 (c) top.tk;",
       "sa: assert #0 (c) else tk;"});
}

TEST(DeferredActionSingleCall, EveryOtherStatementKindIsReported) {
  ExpectEachReported({
      {"initial assert #0 (c) else x = 1;", kFail},
      {"initial assert final (c) begin vf(); end", kPass},
      {"initial assume final (c) begin vf(); end", kPass},
      {"initial cover final (c) begin vf(); end", kPass},
      {"initial assume #0 (c) else begin vf(); end", kFail},
      {"initial assert final (c) else begin vf(); end", kFail},
      {"initial assume final (c) else begin vf(); end", kFail},
      {"initial assume final (c) x++;", kPass},
      {"initial assert #0 (c) else x++;", kFail},
      {"initial assert #0 (c) x <= 1;", kPass},
      {"initial assert #0 (c) ->ev;", kPass},
      {"initial cover final (c) ->>ev;", kPass},
      {"initial assert #0 (c) if (x) vf();", kPass},
      {"initial assert #0 (c) else case (x) 0: vf(); endcase", kFail},
      {"initial assert #0 (c) else #1 vf();", kFail},
      {"initial assert #0 (c) else @(ev) vf();", kFail},
      {"initial assert #0 (c) else wait (c) vf();", kFail},
      {"initial assert #0 (c) else repeat (2) vf();", kFail},
      {"initial begin : blk assert #0 (c) else disable blk; end", kFail},
      {"initial assert #0 (c) fork vf(); join", kPass},
      {"initial assert #0 (c) assert #0 (c) vf();", kPass},
  });
}

TEST(DeferredActionSingleCall, AModulesStaticAndSubroutineFormsAreReported) {
  ExpectEachReported({
      {"sa: assert #0 (c) else x = 2;", kFail},
      {"assert final (c) begin vf(); end", kPass},
      {"cover #0 (c) begin vf(); end", kPass},
      {"function void g; assert #0 (c) else x = 1; endfunction", kFail},
      {"task g; assert #0 (c) else x = 1; endtask", kFail},
      {"initial fork assert #0 (c) else x = 1; join", kFail},
      {"initial begin : nb assert #0 (c) else x = 1; end", kFail},
  });
  ExpectEachAccepted({"sa: assert #0 (c) else vf();",
                      "function void g; assert #0 (c) else vf(); endfunction",
                      "initial fork assert #0 (c) else vf(); join"});
}

TEST(DeferredActionSingleCall, DISABLED_AGenerateBlocksFormsAreReported) {
  ExpectEachReported({
      {"if (1) begin : g ga: assert #0 (c) else x = 6; end", kFail},
      {"if (1) begin : g cover #0 (c) begin vf(); end end", kPass},
      {"if (1) begin : g initial assert #0 (c) else x = 6; end", kFail},
      {"if (1) begin : g initial assert final (c) begin vf(); end end", kPass},
      {"for (genvar j = 0; j < 1; j++) begin : lg "
       "ga: assert #0 (c) else x = 6; end",
       kFail},
      {"for (genvar j = 0; j < 1; j++) begin : lg "
       "initial assert #0 (c) else x = 6; end",
       kFail},
      {"if (1) begin : g function void gf; assert #0 (c) else x = 6; "
       "endfunction end",
       kFail},
  });
}

TEST(DeferredActionSingleCall, AGenerateBlocksSingleCallIsAccepted) {
  ExpectEachAccepted({"if (1) begin : g ga: assert #0 (c) else vf(); end",
                      "if (1) begin : g initial assert final (c) vf(); end",
                      "for (genvar j = 0; j < 1; j++) begin : lg "
                      "initial assert #0 (c) else vf(); end"});
}

std::string InUnit(const std::string& open, const std::string& item,
                   const std::string& close) {
  return open +
         "\n"
         "  logic c; int x;\n"
         "  function void vf; endfunction\n"
         "  " +
         item + "\n" + close +
         "\n"
         "module top; logic c; " +
         (open.rfind("checker", 0) == 0 ? "u_chk u(c);" : "u_unit u();") +
         " endmodule\n";
}

struct Unit {
  const char* open;
  const char* close;
  bool takes_module_items;
};

const Unit kUnits[] = {
    {"interface u_unit;", "endinterface", true},
    {"program u_unit;", "endprogram", false},
    {"checker u_chk(logic e);", "endchecker", true},
};

TEST(DeferredActionSingleCall, AnInterfaceProgramOrCheckerReportsItsForms) {
  for (const auto& u : kUnits) {
    if (u.takes_module_items) {
      ExpectReported(InUnit(u.open, "sa: assert #0 (c) else x = 2;", u.close),
                     kFail, 4);
      ExpectAccepted(InUnit(u.open, "sa: assert #0 (c) else vf();", u.close));
    }
    ExpectReported(InUnit(u.open, "initial assert #0 (c) else x = 2;", u.close),
                   kFail, 4);
    ExpectReported(
        InUnit(u.open, "function void g; assert #0 (c) x = 2; endfunction",
               u.close),
        kPass, 4);
    ExpectAccepted(InUnit(u.open, "initial assert #0 (c) vf();", u.close));
    ExpectAccepted(InUnit(
        u.open, "function void g; assert #0 (c) vf(); endfunction", u.close));
  }
}

std::string PackageFunction(const std::string& action) {
  return "package pk2;\n"
         "  function automatic void vf; endfunction\n"
         "  function automatic void pf(int x); int y;\n"
         "    assert #0 (x > 0) else " +
         action +
         ";\n"
         "  endfunction\n"
         "endpackage\n"
         "module top; initial pk2::pf(1); endmodule\n";
}

std::string UnitFunction(const std::string& action) {
  return "function automatic void vf; endfunction\n"
         "function automatic void pf(int x); int y;\n"
         "  assert #0 (x > 0) else " +
         action +
         ";\n"
         "endfunction\n"
         "module top; initial pf(1); endmodule\n";
}

TEST(DeferredActionSingleCall, DISABLED_APackageOrUnitFunctionsFormIsReported) {
  ExpectReported(PackageFunction("y = 2"), kFail, 4);
  ExpectReported(UnitFunction("y = 2"), kFail, 3);
}

TEST(DeferredActionSingleCall, APackageOrUnitFunctionsSingleCallIsAccepted) {
  ExpectAccepted(PackageFunction("vf()"));
  ExpectAccepted(UnitFunction("vf()"));
}

std::string ClassWith(const std::string& assertion) {
  return "class C;\n"
         "  int n = 0;\n"
         "  function void ff(); endfunction\n"
         "  function void chk(int x);\n"
         "    " +
         assertion +
         "\n"
         "  endfunction\n"
         "endclass\n";
}

struct ClassPlace {
  const char* open;
  const char* close;
  int offset;
};

const ClassPlace kClassPlaces[] = {
    {"", "module top; C h = new; endmodule\n", 0},
    {"package pk3;\n", "endpackage\nmodule top; pk3::C h = new; endmodule\n",
     1},
    {"module top;\n", "  C h = new;\nendmodule\n", 1},
};

std::string InClassPlace(const ClassPlace& p, const std::string& assertion) {
  return p.open + ClassWith(assertion) + p.close;
}

TEST(DeferredActionSingleCall, DISABLED_AClassMethodsFormsAreReported) {
  for (const auto& p : kClassPlaces) {
    for (const Form& form :
         {Form{"b: assert #0 (x > 0) else this.n++;", kFail},
          Form{"assert #0 (x > 0) n = 1;", kPass},
          Form{"d: assert final (x > 0) begin ff(); end", kPass},
          Form{"assume #0 (x > 0) else begin ff(); end", kFail},
          Form{"g: cover #0 (x > 0) begin ff(); end", kPass}}) {
      ExpectReported(InClassPlace(p, form.item), form.message, 5 + p.offset);
    }
  }
}

TEST(DeferredActionSingleCall, AClassMethodsSingleCallIsAccepted) {
  for (const auto& p : kClassPlaces) {
    ExpectAccepted(InClassPlace(p, "assert #0 (x > 0) ff(); else this.ff();"));
  }
}

}  // namespace
