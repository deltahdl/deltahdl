#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr const char* kPlacement = "only in a property or sequence expression";
constexpr const char* kNoneInEffect =
    "requires a global clocking declaration in an enclosing scope";
constexpr const char* kGlobal =
    "  global clocking @(posedge clk); endclocking\n";

std::vector<Diagnostic> Elaborated(const std::string& src) {
  ElabFixture f;
  ElaborateSrc(src, f);
  return f.diag.Diagnostics();
}

void ExpectReported(const std::string& src, const char* report,
                    const std::string& at) {
  EXPECT_TRUE(
      ReportedError(Elaborated(src), report, LineHolding(src, at), "16.9.4"))
      << src;
}

void ExpectAccepted(const std::string& src) {
  EXPECT_TRUE(Elaborated(src).empty()) << src;
}

std::string Clocked(const std::string& items) {
  return "module m;\n  logic clk, a, b, y;\n" + std::string(kGlobal) + items +
         "endmodule\n";
}

std::string Swapped(std::string src, const std::string& from,
                    const std::string& to) {
  return src.replace(src.find(from), from.size(), to);
}

void ExpectFutureReportedPastAccepted(const std::string& src) {
  ExpectReported(src, kPlacement, "$future_gclk");
  ExpectAccepted(Swapped(src, "$future_gclk", "$past_gclk"));
}

TEST(FutureGclkPlacement, DISABLED_ASubroutineBodyIsProceduralCode) {
  const std::string kFunction =
      "  function bit f();\n    return $future_gclk(a);\n  endfunction\n";
  ExpectFutureReportedPastAccepted(
      Clocked(kFunction + "  always @(posedge clk) b = f();\n"));
  ExpectFutureReportedPastAccepted(Clocked(kFunction));
  ExpectFutureReportedPastAccepted(
      Clocked(kFunction + "  assert property (@(posedge clk) f());\n"));
  ExpectFutureReportedPastAccepted(
      Clocked("  task t();\n    b = $future_gclk(a);\n  endtask\n"));
  ExpectFutureReportedPastAccepted(
      Clocked("  class C;\n    function bit g();\n"
              "      return $future_gclk(a);\n    endfunction\n  endclass\n"));
}

TEST(FutureGclkPlacement, DISABLED_APackageOrCompilationUnitFunction) {
  ExpectReported(
      "package pk;\n  function bit f(logic x);\n    return $future_gclk(x);\n"
      "  endfunction\nendpackage\n",
      kPlacement, "$future_gclk");
  ExpectReported(
      "function bit f(logic x);\n  return $future_gclk(x);\nendfunction\n",
      kPlacement, "$future_gclk");
  ExpectAccepted(
      "package pk;\n  sequence s(x);\n    $future_gclk(x);\n"
      "  endsequence\nendpackage\n" +
      Clocked("  assert property (@(posedge clk) pk::s(a));\n"));
}

TEST(FutureGclkPlacement, DISABLED_ProceduralCodeInAGenerateBlock) {
  ExpectFutureReportedPastAccepted(
      Clocked("  if (1) begin : g\n    initial b = $future_gclk(a);\n  end\n"));
  ExpectFutureReportedPastAccepted(
      Clocked("  for (genvar i = 0; i < 2; i++) begin : g\n"
              "    logic z;\n    assign z = $future_gclk(a);\n  end\n"));
}

TEST(FutureGclkPlacement, AContinuousAssignmentAndAnInitialProcedure) {
  ExpectFutureReportedPastAccepted(Clocked("  assign y = $future_gclk(a);\n"));
  ExpectFutureReportedPastAccepted(Clocked("  initial b = $future_gclk(a);\n"));
  ExpectFutureReportedPastAccepted(
      Clocked("  initial if ($future_gclk(a)) b = 1;\n"));
}

TEST(FutureGclkPlacement, EveryActionBlock) {
  for (const char* items : {
           "  assert property (@(posedge clk) a) else b = $future_gclk(a);\n",
           "  assume property (@(posedge clk) a) b = $future_gclk(a);\n",
           "  assume property (@(posedge clk) a) else b = $future_gclk(a);\n",
           "  cover property (@(posedge clk) a) b = $future_gclk(a);\n",
           "  cover sequence (@(posedge clk) a) b = $future_gclk(a);\n",
           "  initial expect (@(posedge clk) a) b = $future_gclk(a);\n",
           "  initial expect (@(posedge clk) a) else b = $future_gclk(a);\n",
       }) {
    ExpectFutureReportedPastAccepted(Clocked(items));
  }
}

TEST(FutureGclkPlacement, AnImmediateOrDeferredAssertionsExpression) {
  for (const char* kind : {"assert", "assert final", "assert #0"}) {
    ExpectFutureReportedPastAccepted(Clocked("  always @(posedge clk) " +
                                             std::string(kind) +
                                             " ($future_gclk(a));\n"));
  }
}

TEST(FutureGclkPlacement, DISABLED_ALetInstanceInProceduralCode) {
  const std::string kSrc = Clocked(
      "  let l(x) = $future_gclk(x);\n  always @(posedge clk)\n"
      "    b = l(a);\n");
  ExpectReported(kSrc, kPlacement, "b = l(a)");
  EXPECT_FALSE(ReportedError(Elaborated(kSrc), kPlacement,
                             LineHolding(kSrc, "let l"), "16.9.4"));
}

TEST(FutureGclkPlacement, DISABLED_ALetInstanceOnlyInAPropertyIsAccepted) {
  ExpectAccepted(
      Clocked("  let l(x) = $future_gclk(x);\n"
              "  assert property (@(posedge clk) l(a));\n"));
}

TEST(FutureGclkPlacement, ProceduralCodeOfAnInterfaceOrProgram) {
  for (const char* kind : {"interface", "program"}) {
    const std::string kSrc = std::string(kind) + " c;\n  logic clk, a, b;\n" +
                             kGlobal + "  initial b = $future_gclk(a);\nend" +
                             kind + "\nmodule top;\n  c u();\nendmodule\n";
    ExpectFutureReportedPastAccepted(kSrc);
  }
}

TEST(FutureGclkPlacement, DISABLED_AFunctionInACheckerBody) {
  ExpectFutureReportedPastAccepted(
      "checker ck(logic clk, logic a);\n" + std::string(kGlobal) +
      "  function bit f();\n    return $future_gclk(a);\n  endfunction\n"
      "endchecker\nmodule top;\n  logic clk, a;\n  ck k(clk, a);\nendmodule\n");
}

TEST(FutureGclkPlacement, EachFutureFunctionIsReported) {
  for (const char* fn : {"$future_gclk", "$rising_gclk", "$falling_gclk",
                         "$steady_gclk", "$changing_gclk"}) {
    ExpectReported(Clocked("  initial b = " + std::string(fn) + "(a);\n"),
                   kPlacement, fn);
  }
}

TEST(FutureGclkPlacement, EveryPropertyStatementAcceptsAFutureFunction) {
  for (const char* items : {
           "  assume property (@(posedge clk) $rising_gclk(a));\n",
           "  restrict property (@(posedge clk) $rising_gclk(a));\n",
           "  cover sequence (@(posedge clk) $rising_gclk(a));\n",
           "  always @(posedge clk) assert property ($rising_gclk(a));\n",
       }) {
    ExpectAccepted(Clocked(items));
  }
}

TEST(FutureGclkPlacement, ANamedSequenceOrPropertyInEveryDesignElement) {
  const std::string kDecls =
      "  sequence s(x); $steady_gclk(x); endsequence\n"
      "  property p(x); $changing_gclk(x) |-> 1; endproperty\n";
  const std::string kAsserts =
      "  assert property (@(posedge clk) s(a));\n"
      "  assert property (@(posedge clk) p(a));\n";
  ExpectAccepted(Clocked(kDecls + kAsserts));
  ExpectAccepted("package pk;\n" + kDecls + "endpackage\n" +
                 Clocked("  assert property (@(posedge clk) pk::s(a));\n"
                         "  assert property (@(posedge clk) pk::p(a));\n"));
  for (const char* kind : {"interface", "program"}) {
    std::string src = kind;
    src += " c;\n  logic clk, a;\n";
    src += kGlobal;
    src += kDecls;
    src += kAsserts;
    src += "end";
    src += kind;
    src += "\nmodule top;\n  c u();\nendmodule\n";
    ExpectAccepted(src);
  }
  std::string checker = "checker ck(logic clk, logic a);\n";
  checker += kGlobal;
  checker += kDecls;
  checker += kAsserts;
  checker +=
      "endchecker\nmodule top;\n  logic clk, a;\n  ck k(clk, a);\nendmodule\n";
  ExpectAccepted(checker);
}

constexpr const char* kAllTen[] = {
    "$past_gclk",    "$rose_gclk",    "$fell_gclk",   "$stable_gclk",
    "$changed_gclk", "$future_gclk",  "$rising_gclk", "$falling_gclk",
    "$steady_gclk",  "$changing_gclk"};

std::string Unclocked(const std::string& items) {
  return "module m;\n  logic clk, a, b;\n" + items + "endmodule\n";
}

TEST(GclkInEffect, EachFunctionNeedsADeclaration) {
  for (const char* fn : kAllTen) {
    const std::string kItems =
        "  assert property (@(posedge clk) " + std::string(fn) + "(a));\n";
    ExpectReported(Unclocked(kItems), kNoneInEffect, fn);
    ExpectAccepted(Clocked(kItems));
  }
}

std::string InstanceOf(const char* kind, bool declared) {
  std::string body = "  logic clk, a, b;\n";
  if (declared) {
    body += kGlobal;
  }
  body += "  assert property (@(posedge clk) $rose_gclk(a));\n";
  if (std::string(kind) == "checker") {
    return "checker c;\n" + body +
           "endchecker\nmodule top;\n  c u();\n"
           "endmodule\n";
  }
  return std::string(kind) + " c;\n" + body + "end" + kind +
         "\nmodule top;\n  c u();\nendmodule\n";
}

TEST(GclkInEffect, AnInterfaceProgramOrCheckersOwnDeclaration) {
  for (const char* kind : {"interface", "program", "checker"}) {
    ExpectReported(InstanceOf(kind, false), kNoneInEffect, "$rose_gclk");
    ExpectAccepted(InstanceOf(kind, true));
  }
}

TEST(GclkInEffect, TheInstantiatingModulesDeclaration) {
  for (const char* kind : {"interface", "program", "checker"}) {
    std::string src = InstanceOf(kind, false);
    src = Swapped(src, "module top;\n",
                  "module top;\n  logic clk;\n" + std::string(kGlobal));
    ExpectAccepted(src);
  }
}

TEST(GclkInEffect, ASiblingOrChildDeclarationIsNotInEffect) {
  const std::string kUser =
      "module user;\n  logic clk, a;\n"
      "  assert property (@(posedge clk) $fell_gclk(a));\nendmodule\n";
  const std::string kOwner =
      "module owner;\n  logic clk;\n" + std::string(kGlobal) + "endmodule\n";
  ExpectReported(
      kUser + kOwner + "module top;\n  user u();\n  owner o();\nendmodule\n",
      kNoneInEffect, "$fell_gclk");
  ExpectReported(
      kOwner +
          "module top;\n  logic clk, a;\n  owner o();\n"
          "  assert property (@(posedge clk) $fell_gclk(a));\nendmodule\n",
      kNoneInEffect, "$fell_gclk");
}

TEST(GclkInEffect, DISABLED_APackageSequenceIsResolvedWhereItIsAsserted) {
  const std::string kPackage =
      "package pk;\n  sequence s(x);\n    $stable_gclk(x);\n  endsequence\n"
      "endpackage\n";
  const std::string kAssert = "  assert property (@(posedge clk) pk::s(a));\n";
  ExpectAccepted(kPackage + Clocked(kAssert));
  ExpectReported(kPackage + Unclocked(kAssert), kNoneInEffect, "pk::s(a)");
}

}  // namespace
