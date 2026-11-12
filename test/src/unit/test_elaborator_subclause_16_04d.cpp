#include <gtest/gtest.h>

#include <initializer_list>
#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

const char kAutomatic[] = "cannot pass automatic variable as actual for ref";
const char kDynamic[] = "cannot pass dynamic variable as actual for ref";

std::string InTop(const std::string& item) {
  return "package pk; task automatic upd(ref int r); endtask endpackage\n"
         "module sub; int hv; endmodule\n"
         "class C;\n"
         "  int v; static int sp;\n"
         "  task automatic r(ref int x); endtask\n"
         "  function void fm(ref int x); endfunction\n"
         "  task automatic cr(const ref int x); endtask\n"
         "endclass\n"
         "module top;\n"
         "  typedef struct { int f; } st_t;\n"
         "  st_t sv; int s; int da[]; int q[$]; int aa[int]; int fa[4];\n"
         "  sub u();\n"
         "  C h = new;\n"
         "  task automatic by_ref(ref int r); endtask\n"
         "  task automatic by_cref(const ref int r); endtask\n"
         "  task automatic by_val(input int r); endtask\n"
         "  function automatic void fref(ref int r); endfunction\n"
         "  " +
         item +
         "\n"
         "endmodule\n";
}

void ExpectReported(const std::string& src, const char* message, int line) {
  ElabFixture f;
  Elaborate(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, line, "16.4"))
      << src;
}

void ExpectAccepted(const std::string& src) {
  ElabFixture f;
  ASSERT_NE(Elaborate(src, f), nullptr) << src;
  EXPECT_FALSE(f.has_errors) << src;
}

void ExpectEachReported(std::initializer_list<const char*> items,
                        const char* message) {
  for (const char* item : items) ExpectReported(InTop(item), message, 18);
}

void ExpectEachAccepted(std::initializer_list<const char*> items) {
  for (const char* item : items) ExpectAccepted(InTop(item));
}

TEST(DeferredRefActual, AnAutomaticLocalOrFormalIsReportedForEveryRefKind) {
  ExpectEachReported(
      {"task automatic t1; int loc; assert #0 (1) by_cref(loc); endtask",
       ("function automatic void f1(int p); assert #0 (1) fref(p); "
        "endfunction"),
       "initial begin automatic int loc; assert #0 (1) by_ref(loc); end"},
      kAutomatic);
}

TEST(DeferredRefActual, AnAutomaticLocalIsReportedOnEveryDirective) {
  ExpectEachReported(
      {"task automatic t1; int loc; assert #0 (0) else by_ref(loc); endtask",
       "task automatic t1; int loc; assume #0 (1) by_ref(loc); endtask",
       "task automatic t1; int loc; cover #0 (1) by_ref(loc); endtask",
       "task automatic t1; int loc; assert final (1) by_ref(loc); endtask",
       ("task automatic t1; int loc; assume final (0) else by_ref(loc); "
        "endtask"),
       "task automatic t1; int loc; cover final (1) by_ref(loc); endtask"},
      kAutomatic);
}

TEST(DeferredRefActual, DISABLED_ALoopVariableIsReportedWhereverTheLoopStands) {
  ExpectEachReported(
      {("task automatic t1; for (int i = 0; i < 1; i++) "
        "assert #0 (1) by_ref(i); endtask"),
       ("task static t2; for (int i = 0; i < 1; i++) "
        "assert #0 (1) by_ref(i); endtask"),
       "initial for (int k = 0; k < 1; k++) assert #0 (1) by_ref(k);"},
      kAutomatic);
}

TEST(DeferredRefActual, ALoopOverAStaticVariableIsAccepted) {
  ExpectEachAccepted(
      {"initial for (s = 0; s < 1; s++) assert #0 (1) by_ref(s);"});
}

TEST(DeferredRefActual,
     DISABLED_PartOfAnAutomaticVariableIsReportedAsAutomatic) {
  ExpectEachReported(
      {"task automatic t1; int la[4]; assert #0 (1) by_ref(la[1]); endtask",
       "task automatic t1; st_t ls; assert #0 (1) by_ref(ls.f); endtask"},
      kAutomatic);
}

TEST(DeferredRefActual, PartOfAStaticVariableIsAccepted) {
  ExpectEachAccepted({"initial assert #0 (1) by_ref(fa[1]);"});
}

TEST(DeferredRefActual, DISABLED_AStaticStructMemberIsAccepted) {
  ExpectEachAccepted({"initial assert #0 (1) by_ref(sv.f);"});
}

TEST(DeferredRefActual,
     DISABLED_AHierarchicalOrStaticPropertyReferenceIsAccepted) {
  ExpectEachAccepted({"initial assert #0 (1) by_ref(u.hv);",
                      "initial assert #0 (1) by_ref(top.s);",
                      "initial assert #0 (1) by_ref(C::sp);"});
}

TEST(DeferredRefActual,
     DISABLED_ADynamicArrayElementIsReportedForEveryRefKind) {
  ExpectEachReported({"initial assert #0 (1) by_ref(da[0]);",
                      "initial assert #0 (1) by_ref(q[0]);",
                      "initial assert #0 (1) by_ref(aa[0]);",
                      "initial assert #0 (1) by_cref(da[0]);",
                      "initial assert #0 (1) by_cref(q[0]);",
                      "initial assert #0 (1) by_cref(aa[0]);"},
                     kDynamic);
}

TEST(DeferredRefActual, DISABLED_EveryCalleeFormHasItsRefFormalChecked) {
  ExpectEachReported(
      {"task automatic t1; int loc; assert #0 (1) h.r(loc); endtask",
       "task automatic t1; int loc; assert #0 (1) h.fm(loc); endtask",
       "task automatic t1; int loc; assert #0 (1) pk::upd(loc); endtask"},
      kAutomatic);
}

TEST(DeferredRefActual, EveryCalleeFormTakesAStaticActual) {
  ExpectEachAccepted({"initial assert #0 (1) h.r(s);",
                      "initial assert #0 (1) h.fm(s);",
                      "initial assert #0 (1) pk::upd(s);"});
}

TEST(DeferredRefActual, DISABLED_AGenerateBlocksTaskLocalIsReported) {
  ExpectEachReported({("for (genvar g = 0; g < 1; g++) begin : gb "
                       "task automatic gt; int loc; assert #0 (1) by_ref(loc); "
                       "endtask end")},
                     kAutomatic);
}

TEST(DeferredRefActual, AGenerateBlocksStaticActualIsAccepted) {
  ExpectEachAccepted(
      {("for (genvar g = 0; g < 1; g++) begin : gb "
        "task automatic gt; assert #0 (1) by_ref(s); endtask "
        "end")});
}

TEST(DeferredRefActual, AByValueFormalTakesAnyVariable) {
  ExpectEachAccepted(
      {"task automatic t1; int loc; assert #0 (1) by_val(loc); endtask",
       "initial assert #0 (1) by_val(h.v);",
       "initial assert #0 (1) by_val(da[0]);", "sa: assert #0 (1) by_ref(s);"});
}

std::string InUnit(const std::string& open, const std::string& close,
                   const std::string& actual) {
  return open +
         "\n"
         "  task automatic upd(ref int r); endtask int ps;\n"
         "  task automatic pc; int loc; assert #0 (1) upd(" +
         actual + "); endtask\n" + close + "\n";
}

struct Unit {
  const char* open;
  const char* close;
};

const Unit kPackageOrUnit[] = {
    {"package pk2;", "endpackage\nmodule top; endmodule"},
    {"", "module top; endmodule"},
};

const Unit kInterfaceOrProgram[] = {
    {"interface u_unit;", "endinterface\nmodule top; u_unit u(); endmodule"},
    {"program u_unit;", "endprogram\nmodule top; u_unit u(); endmodule"},
};

TEST(DeferredRefActual, DISABLED_APackageOrUnitTasksLocalIsReported) {
  for (const auto& u : kPackageOrUnit) {
    ExpectReported(InUnit(u.open, u.close, "loc"), kAutomatic, 3);
  }
}

TEST(DeferredRefActual, AnInterfaceOrProgramTasksLocalIsReported) {
  for (const auto& u : kInterfaceOrProgram) {
    ExpectReported(InUnit(u.open, u.close, "loc"), kAutomatic, 3);
  }
}

TEST(DeferredRefActual, EveryUnitsStaticVariableIsAccepted) {
  for (const auto& u : kPackageOrUnit) {
    ExpectAccepted(InUnit(u.open, u.close, "ps"));
  }
  for (const auto& u : kInterfaceOrProgram) {
    ExpectAccepted(InUnit(u.open, u.close, "ps"));
  }
}

std::string InMethod(const std::string& stmt) {
  return "class D;\n"
         "  int v; static int sp;\n"
         "  task automatic r(ref int x); endtask\n"
         "  task automatic cr(const ref int x); endtask\n"
         "  task meth(); int loc; " +
         stmt +
         " endtask\n"
         "endclass\n"
         "module top; D d = new; endmodule\n";
}

TEST(DeferredRefActual, DISABLED_AClassMethodsLocalIsReported) {
  ExpectReported(InMethod("assert #0 (1) r(loc);"), kAutomatic, 5);
}

TEST(DeferredRefActual, DISABLED_AClassPropertyInsideAMethodIsReported) {
  for (const char* stmt :
       {"assert #0 (1) r(v);", "assert #0 (1) r(this.v);",
        "assert #0 (1) cr(v);", "assert #0 (1) cr(this.v);"}) {
    ExpectReported(InMethod(stmt), kDynamic, 5);
  }
}

TEST(DeferredRefActual, AStaticPropertyInsideAMethodIsAccepted) {
  ExpectAccepted(InMethod("assert #0 (1) r(sp);"));
  ExpectAccepted(InMethod("assert #0 (1) r(D::sp);"));
}

}  // namespace
