#include <gtest/gtest.h>

#include <algorithm>
#include <array>
#include <cstdint>
#include <format>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

constexpr std::string_view kHierarchicalReport =
    "type operator argument uses a hierarchical reference, which the type "
    "operator does not accept";
constexpr std::string_view kDynamicElementReport =
    "type operator argument shall not reference elements of dynamic objects";

constexpr const char* kPreamble =
    "module sub;\n"
    "  int q;\n"
    "endmodule\n"
    "module m;\n"
    "  sub s();\n"
    "  typedef struct packed { bit [7:0] f; bit g; } st;\n"
    "  st p;\n"
    "  int d[];\n"
    "  logic r;\n";

constexpr uint32_t kCaseLine = 10;

std::string ModuleWriting(std::string_view line) {
  return kPreamble + std::string(line) + "\nendmodule\n";
}

bool ReportsTheOperand(const std::vector<Diagnostic>& diags) {
  return std::ranges::any_of(diags, [](const Diagnostic& diag) {
    return diag.severity == DiagSeverity::kError &&
           (diag.subclause == "6.23" ||
            diag.message.find("hierarchical") != std::string::npos);
  });
}

void ExpectReportedAtTheCase(std::string_view line, std::string_view report) {
  ElabFixture f;
  ElaborateSrc(ModuleWriting(line), f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), report, kCaseLine, "6.23"));
}

void ExpectStructureMemberAccepted(std::string_view line) {
  ElabFixture f;
  ElaborateSrc(ModuleWriting(line), f);
  EXPECT_FALSE(ReportsTheOperand(f.diag.Diagnostics()));
}

TEST(TypeOperatorConstantContexts, HierarchicalNameInALocalparamIsReported) {
  ExpectReportedAtTheCase("  localparam bit L = type(s.q) == type(int);",
                          kHierarchicalReport);
}

TEST(TypeOperatorConstantContexts, DynamicElementInALocalparamIsReported) {
  ExpectReportedAtTheCase("  localparam bit L = type(d[0]) == type(int);",
                          kDynamicElementReport);
}

TEST(TypeOperatorConstantContexts, StructureMemberInALocalparamIsAccepted) {
  EXPECT_TRUE(
      ElabOk(ModuleWriting("  localparam bit L = type(p.f) == type(byte);\n"
                           "  initial r = L;")));
}

TEST(TypeOperatorConstantContexts, HierarchicalNameInAParameterIsReported) {
  ExpectReportedAtTheCase("  parameter bit P = type(s.q + 1) == type(int);",
                          kHierarchicalReport);
}

TEST(TypeOperatorConstantContexts, DynamicElementInAParameterIsReported) {
  ExpectReportedAtTheCase("  parameter bit P = type(d[1]) != type(int);",
                          kDynamicElementReport);
}

TEST(TypeOperatorConstantContexts, StructureMemberInAParameterIsAccepted) {
  ExpectStructureMemberAccepted("  parameter bit P = type(p.g) == type(bit);");
}

TEST(TypeOperatorConstantContexts,
     HierarchicalNameInAHeaderParameterIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module sub;\n"
      "  int q;\n"
      "endmodule\n"
      "module m #(parameter bit P = type(top.s.q) == type(int));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), kHierarchicalReport, 4, "6.23"));
}

TEST(TypeOperatorConstantContexts, ParameterNameInAHeaderParameterIsAccepted) {
  ElabFixture f;
  ElaborateSrc(
      "module m #(parameter int W = 4,\n"
      "           parameter bit P = type(W + 1) == type(int));\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(ReportsTheOperand(f.diag.Diagnostics()));
}

TEST(TypeOperatorConstantContexts, HierarchicalNameInAPackedRangeIsReported) {
  ExpectReportedAtTheCase("  logic [$bits(type(s.q)) - 1:0] v;",
                          kHierarchicalReport);
}

TEST(TypeOperatorConstantContexts, DynamicElementInAPackedRangeIsReported) {
  ExpectReportedAtTheCase("  logic [$bits(type(d[0])) - 1:0] v;",
                          kDynamicElementReport);
}

TEST(TypeOperatorConstantContexts, StructureMemberInAPackedRangeIsAccepted) {
  ExpectStructureMemberAccepted("  logic [$bits(type(p.f)) - 1:0] v;");
}

TEST(TypeOperatorConstantContexts,
     HierarchicalNameInAnUnpackedRangeIsReported) {
  ExpectReportedAtTheCase("  int a [$bits(type(s.q))];", kHierarchicalReport);
}

TEST(TypeOperatorConstantContexts, StructureMemberInAnUnpackedRangeIsAccepted) {
  ExpectStructureMemberAccepted("  int a [$bits(type(p.f))];");
}

constexpr const char* kValuePreamble =
    "package pk;\n"
    "  typedef struct packed { bit [7:0] f; bit g; } pst;\n"
    "  typedef enum logic [1:0] {PE0, PE1, PE2} pe_t;\n"
    "  parameter pst PP = '{8'd3, 1'b1};\n"
    "  pst pv;\n"
    "endpackage\n"
    "typedef struct packed { bit [7:0] f; bit g; } ust;\n"
    "ust uv;\n"
    "module sub;\n"
    "  int q;\n"
    "endmodule\n"
    "module m(input pk::pst ip, input pk::pe_t ep, input string sp);\n"
    "  import pk::PP;\n"
    "  import pk::*;\n"
    "  sub s();\n"
    "  typedef struct packed { bit [7:0] f; bit g; } st;\n"
    "  typedef enum logic [1:0] {E0, E1, E2} e_t;\n"
    "  parameter st SP = '{8'd5, 1'b0};\n"
    "  localparam string LS = \"abc\";\n"
    "  st sa [2];\n"
    "  string ss [2];\n"
    "  string str;\n"
    "  function automatic st sf(); return '{8'd1, 1'b1}; endfunction\n";

constexpr uint32_t kValueCaseLine = 24;

constexpr std::array kValueOperands = {"E1.next()",
                                       "E1.name",
                                       "pk::PE1.next()",
                                       "PE2.prev()",
                                       "SP.f",
                                       "LS.len()",
                                       "pk::PP.g",
                                       "PP.f",
                                       "pv.f",
                                       "uv.f",
                                       "$unit::uv.g",
                                       "ip.f",
                                       "ep.next()",
                                       "sp.len()",
                                       "sa[1].f",
                                       "ss[0].len()",
                                       "str.tolower().len()",
                                       "sf().g"};

constexpr std::array kDeclarationPlaces = {
    "  var type({}) d;", "  initial begin var type({}) d; end",
    "  function automatic void fd(); var type({}) d; endfunction",
    "  if (1) begin : g var type({}) d; end"};

std::string ValueModuleWriting(std::string_view place,
                               std::string_view operand) {
  return std::string(kValuePreamble) +
         std::vformat(place, std::make_format_args(operand)) + "\nendmodule\n";
}

TEST(TypeOperatorMemberRoots, ADotOnAValueIsNoHierarchicalReference) {
  for (std::string_view place : kDeclarationPlaces) {
    for (std::string_view operand : kValueOperands) {
      SCOPED_TRACE(ValueModuleWriting(place, operand));
      ElabFixture f;
      ElaborateSrc(ValueModuleWriting(place, operand), f);
      EXPECT_FALSE(ReportsTheOperand(f.diag.Diagnostics()));
    }
  }
}

constexpr std::array kScopeOperands = {"s.q", "$root.str.len()"};

TEST(TypeOperatorMemberRoots, ADotOnAScopeIsAHierarchicalReference) {
  for (std::string_view place : kDeclarationPlaces) {
    for (std::string_view operand : kScopeOperands) {
      SCOPED_TRACE(ValueModuleWriting(place, operand));
      ElabFixture f;
      ElaborateSrc(ValueModuleWriting(place, operand), f);
      EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kHierarchicalReport,
                                kValueCaseLine, "6.23"));
    }
  }
}

constexpr std::array kLocalRoots = {
    "  initial for (string i = \"a\"; i.len() < 2; i = {i, \"a\"}) begin "
    "var type(i.len()) d; end",
    "  initial begin st b; var type(b.f) d; end",
    "  initial begin localparam st BP = '{8'd2, 1'b0}; var type(BP.g) d; end",
    "  function automatic void ff(st a); var type(a.f) d; endfunction",
    "  task automatic tt(string a); var type(a.len()) d; endtask",
    "  initial begin st s; var type(s.f) d; end"};

TEST(TypeOperatorMemberRoots, ADotOnAProceduralValueIsNoHierarchicalReference) {
  for (std::string_view line : kLocalRoots) {
    SCOPED_TRACE(line);
    ElabFixture f;
    ElaborateSrc(
        std::string(kValuePreamble) + std::string(line) + "\nendmodule\n", f);
    EXPECT_FALSE(ReportsTheOperand(f.diag.Diagnostics()));
  }
}

constexpr std::array kClassHandleRoots = {
    "  hc h;\n  var type(h.x) d;",
    "  hc h;\n  initial begin var type(h.f()) d; end",
    "  hc h;\n  localparam bit L = type(h.x) == type(byte);",
    "  initial begin hc b; var type(b.x) d; end",
    "  function automatic void ff(hc a); var type(a.f()) d; endfunction"};

TEST(TypeOperatorMemberRoots, ADotOnAClassHandleIsNoHierarchicalReference) {
  for (std::string_view line : kClassHandleRoots) {
    SCOPED_TRACE(line);
    ElabFixture f;
    ElaborateSrc(
        "class hc;\n"
        "  byte x;\n"
        "  function int f(); return 0; endfunction\n"
        "endclass\n" +
            std::string(kValuePreamble) + std::string(line) + "\nendmodule\n",
        f);
    EXPECT_FALSE(ReportsTheOperand(f.diag.Diagnostics()));
  }
}

}  // namespace
