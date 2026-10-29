#include <gtest/gtest.h>

#include <algorithm>
#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/diagnostic.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §6.23 (printed page 138): the expression a type reference names shall hold
// no hierarchical reference and no reference to an element of a dynamic
// object, wherever the type reference stands. A parameter's value (§6.20.2)
// and a declaration's range (§11.2.1) are constant expressions, which a type
// reference comparison is and a $bits of one is, and neither rule judges the
// operand of a type reference by a dot written in it: a member of a structure
// the module declares is no hierarchical name. The cases below write each form
// in a body localparam, a body parameter, a header parameter, a packed range
// and an unpacked range.

constexpr std::string_view kHierarchicalReport =
    "type operator argument uses a hierarchical reference, which the type "
    "operator does not accept";
constexpr std::string_view kDynamicElementReport =
    "type operator argument shall not reference elements of dynamic objects";

// The declarations every case reads, at lines 1 to 9, so that the line the
// case writes is line 10: an instance whose member is a hierarchical name, a
// packed structure, and a dynamic array.
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

// Whether the run reported an error under §6.23, or one that calls a name in
// the source hierarchical, as §6.20.2's and §11.2.1's reports do.
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

// The structure member is neither a hierarchical name by §6.23 nor by §6.20.2
// or §11.2.1.
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

// A header's parameter port list is read before the body declares anything,
// so the nearest allowed form names a parameter the list declares before it.
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

}  // namespace
