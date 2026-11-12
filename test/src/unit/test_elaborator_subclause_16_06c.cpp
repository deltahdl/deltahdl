#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <initializer_list>
#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

const char kStateful[] =
    "keeps state or has a side effect and cannot be called in a concurrent "
    "assertion";

std::string WithForm(std::string src, const std::string& form) {
  for (size_t at = src.find("@@"); at != std::string::npos;
       at = src.find("@@", at + form.size())) {
    src.replace(at, 2, form);
  }
  return src;
}

const char kOutside[] =
    "typedef struct {int f;} t_s;\n"
    "package pk;\n"
    "  int pc;\n"
    "  logic pclk = 0;\n"
    "  function automatic bit pside(bit x); pc = 1; return x; endfunction\n"
    "  function automatic bit ppure(bit x); return x; endfunction\n"
    "endpackage\n"
    "int uc;\n"
    "function automatic bit uside(bit x); uc = 1; return x; endfunction\n"
    "function automatic bit upure(bit x); return x; endfunction\n"
    "class C;\n"
    "  static int sc;\n"
    "  static function bit cside(bit x); sc = 1; return x; endfunction\n"
    "  static function bit cpure(bit x); return x; endfunction\n"
    "endclass\n";

std::string StateBench(const std::string& items,
                       const std::string& outside = "") {
  return std::string(kOutside) + outside +
         "module top;\n"
         "  logic clk = 0, a = 1;\n"
         "  int cnt; int arr[2]; logic [3:0] vec; t_s st; event ev;\n"
         "  integer fd, seed;\n"
         "  function automatic bit fs(bit x); cnt = 1; return x; endfunction\n"
         "  function bit frw(bit x); int n; n = n + 1; return x; endfunction\n"
         "  function bit fwr(bit x); int n; n = 1; return x && n > 0; "
         "endfunction\n"
         "  function bit frd(bit x); return x && cnt >= 0; endfunction\n"
         "  function automatic bit fsi(bit x); static int n = 0; return x; "
         "endfunction\n"
         "  function automatic bit fai(bit x); int n = 0; return x && n == 0; "
         "endfunction\n"
         "  function automatic bit fbit(bit x); vec[0] = 1; return x; "
         "endfunction\n"
         "  function automatic bit farr(bit x); arr[1] = 1; return x; "
         "endfunction\n"
         "  function automatic bit fmem(bit x); st.f = 1; return x; "
         "endfunction\n"
         "  function automatic bit fhier(bit x); top.cnt = 1; return x; "
         "endfunction\n"
         "  function automatic bit fcomp(bit x); cnt += 1; return x; "
         "endfunction\n"
         "  function automatic bit fnb(bit x); cnt <= 1; return x; "
         "endfunction\n"
         "  function automatic bit finc(bit x); cnt++; return x; endfunction\n"
         "  function automatic bit fdec(bit x); --cnt; return x; endfunction\n"
         "  function automatic bit fown(bit x); int n = 0; n++; return x && n "
         "> "
         "0; endfunction\n"
         "  function automatic bit fev(bit x); ->ev; return x; endfunction\n"
         "  function automatic bit fevnb(bit x); ->>ev; return x; endfunction\n"
         "  function automatic bit fdisp(bit x); $display(\"d\"); return x; "
         "endfunction\n"
         "  function automatic bit fwrite(bit x); $write(\"w\"); return x; "
         "endfunction\n"
         "  function automatic bit ffw(bit x); $fwrite(fd, \"f\"); return x; "
         "endfunction\n"
         "  function automatic bit frnd(bit x); return x && $random(seed) > 0; "
         "endfunction\n"
         "  function automatic bit fclog(bit x); return x && $clog2(8) == 3; "
         "endfunction\n"
         "  function automatic bit fcall(bit x); return fs(x); endfunction\n"
         "  function automatic void vs(); cnt = 1; endfunction\n"
         "  function automatic bit fvoid(bit x); vs(); return x; endfunction\n"
         "  function automatic bit fpure(bit x); return x; endfunction\n"
         "  function automatic bit fcallp(bit x); return fpure(x); "
         "endfunction\n"
         "  function automatic bit fpk(bit x); pk::pc = 1; return x; "
         "endfunction\n"
         "  function automatic bit funit(bit x); $unit::uc = 1; return x; "
         "endfunction\n"
         "  function automatic bit fcls(bit x); C::sc = 1; return x; "
         "endfunction\n"
         "  " +
         items + "\nendmodule\n";
}

int ReportsAt(const std::vector<Diagnostic>& diags, uint32_t line) {
  int count = 0;
  for (const auto& diag : diags) {
    if (diag.severity == DiagSeverity::kError &&
        diag.message.find(kStateful) != std::string::npos &&
        diag.loc.line == line && diag.subclause == "16.6") {
      ++count;
    }
  }
  return count;
}

void ExpectStatefulOnce(const std::string& marked, const std::string& form) {
  const std::string kSrc = WithForm(marked, form);
  ElabFixture f;
  Elaborate(kSrc, f);
  EXPECT_EQ(ReportsAt(f.diag.Diagnostics(), LineHolding(marked, "@@")), 1)
      << kSrc;
}

void ExpectAccepted(const std::string& marked, const std::string& form) {
  const std::string kSrc = WithForm(marked, form);
  ElabFixture f;
  auto* design = Elaborate(kSrc, f);
  ASSERT_NE(design, nullptr) << kSrc;
  EXPECT_FALSE(f.has_errors) << kSrc;
}

const char kBoolean[] = "assert property (@(posedge clk) @@);";

void ExpectEachStateful(std::initializer_list<const char*> forms) {
  for (const char* form : forms) {
    ExpectStatefulOnce(StateBench(kBoolean), form);
  }
}

void ExpectEachAccepted(std::initializer_list<const char*> forms) {
  for (const char* form : forms) ExpectAccepted(StateBench(kBoolean), form);
}

TEST(AssertionFunctionState, EveryStatelessPureFunctionIsAccepted) {
  ExpectEachAccepted({"fwr(a)", "frd(a)", "fai(a)", "fown(a)", "fclog(a)",
                      "fcallp(a)", "fpure(a)", "pk::ppure(a)", "upure(a)",
                      "C::cpure(a)"});
}

TEST(AssertionFunctionState, DISABLED_AStaticLocalReadBeforeWrittenIsReported) {
  ExpectEachStateful({"frw(a)"});
}

TEST(AssertionFunctionState,
     DISABLED_AnExplicitlyStaticInitializedLocalIsReported) {
  ExpectEachStateful({"fsi(a)"});
}

TEST(AssertionFunctionState, EveryAssignmentToAModuleVariableIsReported) {
  ExpectEachStateful({"fs(a)", "fbit(a)", "farr(a)", "fmem(a)", "fhier(a)",
                      "fcomp(a)", "fnb(a)"});
}

TEST(AssertionFunctionState,
     DISABLED_AnIncrementOrDecrementStatementIsReported) {
  ExpectEachStateful({"finc(a)", "fdec(a)"});
}

TEST(AssertionFunctionState, DISABLED_AnEventTriggerIsReported) {
  ExpectEachStateful({"fev(a)", "fevnb(a)"});
}

TEST(AssertionFunctionState, DISABLED_AnOutputOrStatefulSystemTaskIsReported) {
  ExpectEachStateful({"fdisp(a)", "fwrite(a)", "ffw(a)", "frnd(a)"});
}

TEST(AssertionFunctionState, DISABLED_ACallToAnImpureFunctionIsReported) {
  ExpectEachStateful({"fcall(a)", "fvoid(a)"});
}

TEST(AssertionFunctionState, AWriteToAPackageUnitOrClassVariableIsReported) {
  ExpectEachStateful({"fpk(a)", "funit(a)", "fcls(a)"});
}

TEST(AssertionFunctionState, DISABLED_APackageUnitOrClassFunctionIsReported) {
  ExpectEachStateful({"pk::pside(a)", "uside(a)", "C::cside(a)"});
  ExpectStatefulOnce(StateBench(std::string("import pk::*;\n  ") + kBoolean),
                     "pside(a)");
}

const char* const kStatePlaces[] = {
    "sequence sq; @(posedge clk) @@; endsequence\n  cover property (sq);",
    "assert property (@(posedge clk) disable iff (@@) a);",
    "assume property (@(posedge clk) @@);",
    "cover property (@(posedge clk) @@);",
    "restrict property (@(posedge clk) @@);",
    "always @(posedge clk) assert property (@@);",
};

const char* const kStateRepeatedPlaces[] = {
    "property pq; @(posedge clk) @@; endproperty\n  assert property (pq);",
    "default disable iff (@@);\n  assert property (@(posedge clk) a);",
};

const char* const kStateGeneratePlaces[] = {
    "if (1) begin : g assert property (@(posedge clk) @@); end",
    ("for (genvar j = 0; j < 1; j++) begin : lg\n"
     "    assert property (@(posedge clk) @@);\n  end"),
};

TEST(AssertionFunctionState, EveryPlaceAcceptsAPureFunction) {
  for (const char* place : kStatePlaces) {
    ExpectAccepted(StateBench(place), "fpure(a)");
  }
  for (const char* place : kStateRepeatedPlaces) {
    ExpectAccepted(StateBench(place), "fpure(a)");
  }
  for (const char* place : kStateGeneratePlaces) {
    ExpectAccepted(StateBench(place), "fpure(a)");
  }
}

TEST(AssertionFunctionState,
     DISABLED_ANamedPropertyOrDefaultDisableReportsItOnce) {
  for (const char* place : kStateRepeatedPlaces) {
    ExpectStatefulOnce(StateBench(place), "fs(a)");
  }
}

TEST(AssertionFunctionState, EveryPlaceReportsAFunctionWritingAVariable) {
  for (const char* place : kStatePlaces) {
    ExpectStatefulOnce(StateBench(place), "fs(a)");
  }
}

TEST(AssertionFunctionState, DISABLED_AGenerateBlockReportsAFunctionWriting) {
  for (const char* place : kStateGeneratePlaces) {
    ExpectStatefulOnce(StateBench(place), "fs(a)");
  }
}

TEST(AssertionFunctionState, AnActionBlockMayCallAFunctionWritingAVariable) {
  ExpectAccepted(StateBench("assert property (@(posedge clk) a) else "
                            "$display(\"%0d\", @@);"),
                 "fs(a)");
}

const char kDeclaredProperties[] =
    "package pq;\n"
    "  logic qclk = 0;\n"
    "  property pp; @(posedge qclk) @@; endproperty\n"
    "endpackage\n";

const char kUnitProperty[] =
    "logic vclk = 0;\n"
    "property up; @(posedge vclk) @@; endproperty\n";

TEST(AssertionFunctionState, APackageOrUnitPropertyCallingAPureOneIsAccepted) {
  ExpectAccepted(
      StateBench("assert property (pq::pp);\n"
                 "  assert property (up);",
                 WithForm(kDeclaredProperties, "pk::ppure(1)") + kUnitProperty),
      "upure(1)");
}

TEST(AssertionFunctionState, DISABLED_APackageOrUnitPropertyIsReported) {
  ExpectStatefulOnce(
      StateBench("assert property (pq::pp);", std::string(kDeclaredProperties)),
      "pk::pside(1)");
  ExpectStatefulOnce(StateBench("assert property (up);", kUnitProperty),
                     "uside(1)");
}

std::string StateUnit(const char* kind, const char* effect) {
  const std::string kPort =
      std::string(kind) == "checker" ? "logic clk" : "input logic clk";
  return std::string(kind) + " u_unit(" + kPort +
         ");\n"
         "  int cnt;\n"
         "  function automatic bit ue(bit x); " +
         effect +
         " return x; endfunction\n"
         "  function automatic bit ul(bit x); int n; n = 1; return x; "
         "endfunction\n"
         "  assert property (@(posedge clk) @@);\n"
         "end" +
         kind + "\n";
}

TEST(AssertionFunctionState, EveryUnitReportsAFunctionWritingAVariable) {
  for (const char* kind : {"interface", "program", "checker"}) {
    const std::string kMarked =
        StateBench("u_unit u(clk);", StateUnit(kind, "cnt = 1;"));
    ExpectStatefulOnce(kMarked, "ue(clk)");
    ExpectAccepted(kMarked, "ul(clk)");
  }
}

TEST(AssertionFunctionState, DISABLED_ACheckerReportsASystemTaskCall) {
  ExpectStatefulOnce(
      StateBench("u_unit u(clk);", StateUnit("checker", "$display(\"c\");")),
      "ue(clk)");
}

}  // namespace
