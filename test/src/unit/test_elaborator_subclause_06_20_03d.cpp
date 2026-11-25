#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr std::string_view kDeclarations =
    "package pk; typedef logic [11:0] t; int v; parameter int N = 3;\n"
    "  typedef enum { E0 } e_t; function int f(); return 1; endfunction\n"
    "  task k(); endtask\n"
    "  class K; typedef byte inner; static int q; parameter int Q = 2;\n"
    "    localparam type U = int; endclass\n"
    "endpackage\n"
    "class X #(type T = int, int W = 1); T v; static int s; endclass\n"
    "interface class IC #(type T = int); endclass\n"
    "module m #(type T = int, int W = 1) (); endmodule\n"
    "module b; parameter type T = int; parameter int W = 1; endmodule\n"
    "interface ifc #(type T = int) (); endinterface\n"
    "program prg #(type T = int) (); endprogram\n";

constexpr unsigned kLineOfForm = 14;

const char* const kNoTypes[] = {"5",        "1 + 2",       "P",
                                "q",        "pk::N",       "pk::v",
                                "pk::f",    "pk::k",       "pk::E0",
                                "pk::nope", "std::nosuch", "std::randomize",
                                "pk::K::q", "pk::K::Q",    "$unit::P",
                                "\"a\"",    "1.5"};

const char* const kTypes[] = {"int",
                              "logic [3:0]",
                              "pk::t",
                              "pk::t [1:0]",
                              "pk::K",
                              "pk::K::inner",
                              "pk::K::U",
                              "u_t",
                              "X #(byte)",
                              "pk::e_t",
                              "$unit::u_t",
                              "process",
                              "std::process",
                              "std::semaphore",
                              "std::mailbox",
                              "mailbox",
                              "mailbox #(int)",
                              "virtual ifc",
                              "event",
                              "string",
                              "chandle",
                              "enum { A, B }",
                              "struct { int a; }"};

std::string Replaced(std::string_view form, std::string_view value) {
  std::string text(form);
  const auto kAt = text.find('@');
  return text.replace(kAt, 1, value);
}

std::string Source(std::string_view form, std::string_view value) {
  return std::string(kDeclarations)
      .append("parameter int P = 4; int q; typedef shortint u_t;\n")
      .append(Replaced(form, value));
}

constexpr std::string_view kSetToNoType =
    "type parameter 'T' can only be set to a data type";

std::string AssignedNoType(std::string_view owner) {
  return std::string("parameter value assignment for type parameter 'T' of '")
      .append(owner)
      .append("' does not name a type");
}

void ExpectReported(std::string_view form, std::string_view value,
                    std::string_view report) {
  const std::string kSource = Source(form, value);
  SCOPED_TRACE(kSource);
  ElabFixture f;
  ElaborateSrc(kSource, f, "top");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), std::string(report),
                            kLineOfForm, "6.20.3"));
}

void ExpectAccepted(std::string_view form, std::string_view value) {
  const std::string kSource = Source(form, value);
  SCOPED_TRACE(kSource);
  ElabFixture f;
  ElaborateSrc(kSource, f, "top");
  EXPECT_FALSE(f.has_errors);
}

bool NamesAnItemOfTheUnit(std::string_view value) {
  return value == "P" || value == "q" || value == "u_t" ||
         value == "X #(byte)" || value.starts_with("$unit");
}

void ExpectOnlyTypesTakenInAPackage(std::string_view form,
                                    std::string_view report) {
  for (const char* value : kNoTypes) {
    if (!NamesAnItemOfTheUnit(value)) ExpectReported(form, value, report);
  }
  for (const char* value : kTypes) {
    if (!NamesAnItemOfTheUnit(value)) ExpectAccepted(form, value);
  }
}

void ExpectOnlyTypesTaken(std::string_view form, std::string_view report) {
  for (const char* value : kNoTypes) ExpectReported(form, value, report);
  for (const char* value : kTypes) ExpectAccepted(form, value);
}

void ExpectOnlyPackageTypesTaken(std::string_view form) {
  for (const char* value : kNoTypes) {
    if (std::string_view(value).starts_with("pk::"))
      ExpectReported(form, value, kSetToNoType);
  }
  for (const char* value : kTypes) ExpectAccepted(form, value);
}

TEST(TypeParameterSetToNoType, BodyDefaultOfAModuleInterfaceOrProgram) {
  ExpectOnlyTypesTaken("module top; parameter type T = @; endmodule\n",
                       kSetToNoType);
  ExpectOnlyTypesTaken("module top; localparam type T = @; endmodule\n",
                       kSetToNoType);
  ExpectOnlyTypesTaken(
      "interface i; parameter type T = @; endinterface\n"
      "module top; i u(); endmodule\n",
      kSetToNoType);
  ExpectOnlyTypesTaken("program top; localparam type T = @; endprogram\n",
                       kSetToNoType);
  ExpectOnlyTypesTaken(
      "module top; if (1) begin : g localparam type T = @; end endmodule\n",
      kSetToNoType);
}

TEST(TypeParameterSetToNoType, DefaultOfAPackageOrTheCompilationUnit) {
  ExpectOnlyTypesTakenInAPackage(
      "package r; parameter type T = @; endpackage module top; endmodule\n",
      kSetToNoType);
  ExpectOnlyTypesTaken("localparam type T = @; module top; endmodule\n",
                       kSetToNoType);
}

TEST(TypeParameterSetToNoType, DefaultOfAClassBodyASubroutineOrABlock) {
  ExpectOnlyTypesTaken(
      "class W; localparam type T = @; endclass module top; endmodule\n",
      kSetToNoType);
  ExpectOnlyTypesTaken(
      "module top; initial begin localparam type T = @; end endmodule\n",
      kSetToNoType);
  ExpectOnlyTypesTaken(
      "module top; task a(); localparam type T = @; endtask endmodule\n",
      kSetToNoType);
  ExpectOnlyTypesTaken(
      "class W; function void f(); parameter type T = @; endfunction endclass"
      " module top; endmodule\n",
      kSetToNoType);
}

TEST(TypeParameterSetToNoType, DefaultOfAParameterPortList) {
  for (const char* form :
       {"module top #(type T = @) (); endmodule\n",
        "module top #(localparam type T = @) (); endmodule\n",
        ("interface i #(parameter type T = @) (); endinterface"
         " module top; i u(); endmodule\n"),
        "program top #(type T = @) (); endprogram\n",
        "class W #(type T = @); endclass module top; W w; endmodule\n"}) {
    ExpectOnlyPackageTypesTaken(form);
  }
}

TEST(TypeParameterSetToNoType, AssignmentOfAnInstance) {
  for (const char* form :
       {"module top; m #(@) u(); endmodule\n",
        "module top; m #(.W(2), .T(@)) u(); endmodule\n",
        "module top; m #(@, 2) u [1:0] (); endmodule\n",
        "module top; if (1) begin : g m #(@) u(); end endmodule\n",
        "module top; endmodule bind top m #(@) u();\n"}) {
    ExpectOnlyTypesTaken(form, AssignedNoType("m"));
  }
  ExpectOnlyTypesTaken("module top; b #(@) u(); endmodule\n",
                       AssignedNoType("b"));
  ExpectOnlyTypesTaken("module top; b #(.T(@)) u(); endmodule\n",
                       AssignedNoType("b"));
  ExpectOnlyTypesTaken("module top; ifc #(@) u(); endmodule\n",
                       AssignedNoType("ifc"));
  ExpectOnlyTypesTaken("module top; prg #(.T(@)) u(); endmodule\n",
                       AssignedNoType("prg"));
  ExpectOnlyTypesTaken(
      "module top; n #(@) u(); module n #(type T = int) (); endmodule"
      " endmodule\n",
      AssignedNoType("n"));
}

TEST(TypeParameterSetToNoType, AssignmentOnALineOfItsOwnIsReportedOnceThere) {
  for (const char* unit : {"m", "b", "ifc", "prg"}) {
    SCOPED_TRACE(unit);
    ElabFixture f;
    ElaborateSrc(std::string(kDeclarations) + "module top;\n  " + unit +
                     " #(\n    5) i();\nendmodule\n",
                 f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), AssignedNoType(unit),
                              kLineOfForm + 1, "6.20.3"));
    EXPECT_EQ(f.diag.Diagnostics().size(), 1U);
  }
}

TEST(TypeParameterSetToNoType, ArgumentOfAClassVariable) {
  for (const char* form :
       {"module top; X #(@) h; endmodule\n",
        "module top; X #(.W(2), .T(@)) h; endmodule\n",
        "module top; typedef X #(@, 2) x_t; endmodule\n",
        "module top; initial begin X #(@) h; end endmodule\n",
        "module top; function void f(X #(@) h); endfunction endmodule\n",
        "interface i; X #(@) h; endinterface module top; i u(); endmodule\n",
        "program top; X #(@) h; endprogram\n",
        "module top; if (1) begin : g X #(@) h; end endmodule\n",
        "X #(@) h; module top; endmodule\n",
        "class W; X #(@) h; endclass module top; endmodule\n",
        ("class W; function void f(); X #(@) h; endfunction endclass"
         " module top; endmodule\n")}) {
    ExpectOnlyTypesTaken(form, AssignedNoType("X"));
  }
  ExpectOnlyTypesTakenInAPackage(
      "package r; class Z #(type T = int); endclass Z #(@) h; endpackage"
      " module top; endmodule\n",
      AssignedNoType("Z"));
}

TEST(TypeParameterSetToNoType, ArgumentOfABaseClassOrAScopePrefix) {
  ExpectOnlyTypesTaken(
      "class Y extends X #(@); endclass module top; endmodule\n",
      AssignedNoType("X"));
  ExpectOnlyTypesTaken(
      "class Y implements IC #(@); endclass module top; endmodule\n",
      AssignedNoType("IC"));
  ExpectOnlyTypesTaken(
      "interface class Y extends IC #(.T(@)); endclass module top;"
      " endmodule\n",
      AssignedNoType("IC"));
  ExpectOnlyTypesTaken("module top; initial X #(@)::s = 3; endmodule\n",
                       AssignedNoType("X"));
  ExpectOnlyTypesTaken(
      "module top; initial $display(\"%0d\", X #(.T(@))::s); endmodule\n",
      AssignedNoType("X"));
}

TEST(TypeParameterSetToNoType, HierarchicalNameAndTypeReferenceToOne) {
  for (const char* value : {"u.w", "top.u.w", "type(top.u.w)", "type(u.w)"}) {
    ExpectReported(
        "module c; logic w; endmodule module top; c u(); parameter type T = @;"
        " endmodule\n",
        value, kSetToNoType);
    ExpectReported(
        "module c; logic w; endmodule module top; c u(); m #(@) i();"
        " endmodule\n",
        value, AssignedNoType("m"));
  }
  for (const char* form : {"module top; parameter type T = @; endmodule\n",
                           "module top; m #(@) i(); endmodule\n",
                           "module top; X #(@) h; endmodule\n"}) {
    for (const char* value : {"type(q)", "type(pk::v)", "type(pk::t)"})
      ExpectAccepted(form, value);
  }
}

TEST(TypeParameterSetToNoType, NamesThatAreNeitherValuesNorTypes) {
  for (const char* value : {"g", "k", "s", "p", "l", "cb", "u", "ifc", "m"}) {
    ExpectReported(
        "module top; genvar g; logic c; b u(); m #(@) i(); task k(); endtask"
        " sequence s; c; endsequence property p; c; endproperty let l = c;"
        " clocking cb @(posedge c); endclocking endmodule\n",
        value, AssignedNoType("m"));
  }
  ExpectReported("module top; nettype logic n; X #(@) h; endmodule\n", "n",
                 AssignedNoType("X"));
  ExpectReported("module top; module n; endmodule n a(); X #(@) h; endmodule\n",
                 "n", AssignedNoType("X"));
  ExpectReported("module top; specparam sp = 3; X #(@) h; endmodule\n", "sp",
                 AssignedNoType("X"));
}

TEST(TypeParameterSetToNoType, ValueIsTakenByTheValueParameterBesideIt) {
  ExpectAccepted("module top; X #(int, @) h; endmodule\n", "P");
  ExpectAccepted("module top; m #(int, @) u(); endmodule\n", "pk::N");
  ExpectAccepted("module top; b #(.W(@)) u(); endmodule\n", "pk::N + 1");
  ExpectAccepted("module top; localparam T = @; endmodule\n", "pk::N");
  ExpectAccepted("module top; m #(@) u(); endmodule\n", "");
  ExpectAccepted("module top; X #(int, @) h; endmodule\n", "P + 1");
  ExpectAccepted("module top; initial X #(.T(@), .W(2))::s = 3; endmodule\n",
                 "");
}

TEST(TypeParameterSetToNoType, TypesOfAPackageExportOrASpecializationAreTaken) {
  for (const char* value : {"r::zt", "r::cg"}) {
    ExpectAccepted(
        "package z; typedef int zt; endpackage package r; import z::*;"
        " export z::*; covergroup cg; endgroup endpackage"
        " module top; X #(@) h; endmodule\n",
        value);
  }
  ExpectAccepted(
      "package r; covergroup cg; endgroup endpackage module top;"
      " X #(@) h; endmodule\n",
      "r::cg");
  ExpectAccepted("module top; X #(@) h; endmodule\n", "X #(byte)::T");
}

}  // namespace
