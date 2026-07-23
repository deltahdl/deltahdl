// §22.11 `pragma -- the "no effect on the interpretation of the source text"
// rule, observed past the preprocessor.
//
// The directive itself is handled in src/preprocessor/preprocessor.cpp, but its
// defining property is about what the rest of the pipeline sees. These tests
// build real source with pragmas interleaved between design constructs, drive
// it through preprocess -> parse -> elaborate, and compare the elaborated
// design against the same source with the pragmas removed.

#include <string>
#include <vector>

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// A flat, comparable summary of everything the elaborator produced for one
// module, so two elaborations can be checked for equality without depending on
// pointer identity.
struct ModuleShape {
  std::string name;
  std::vector<std::string> ports;
  std::vector<std::string> nets;
  std::vector<std::string> variables;
  std::vector<std::string> params;
  size_t assigns = 0;
  size_t processes = 0;
  size_t children = 0;

  bool operator==(const ModuleShape&) const = default;
};

ModuleShape ShapeOf(const RtlirModule& m) {
  ModuleShape shape;
  shape.name = std::string(m.name);
  for (const auto& p : m.ports) shape.ports.emplace_back(p.name);
  for (const auto& n : m.nets) shape.nets.emplace_back(n.name);
  for (const auto& v : m.variables) shape.variables.emplace_back(v.name);
  for (const auto& p : m.params) shape.params.emplace_back(p.name);
  shape.assigns = m.assigns.size();
  shape.processes = m.processes.size();
  shape.children = m.children.size();
  return shape;
}

std::vector<ModuleShape> ShapeOfDesign(const RtlirDesign& d) {
  std::vector<ModuleShape> shapes;
  for (const auto* top : d.top_modules) shapes.push_back(ShapeOf(*top));
  return shapes;
}

// The same design written twice: once with unrecognized pragmas sprinkled into
// every position a directive line can occupy, once without any.
const char* kWithPragmas =
    "`pragma unknown_outer_a\n"
    "module sub(input logic i, output logic o);\n"
    "  `pragma unknown_in_sub mode = fast\n"
    "  assign o = ~i;\n"
    "endmodule\n"
    "`pragma unknown_between_modules (a, b = 1)\n"
    "module top;\n"
    "  `pragma unknown_before_param\n"
    "  parameter P = 5;\n"
    "  `pragma unknown_before_net \"note\"\n"
    "  wire w;\n"
    "  logic [7:0] r;\n"
    "  `pragma unknown_before_inst k1 = 1, k2 = 2\n"
    "  sub u0(.i(w), .o());\n"
    "  `pragma unknown_before_process\n"
    "  initial r = 8'd9;\n"
    "  `pragma unknown_before_endmodule\n"
    "endmodule\n"
    "`pragma unknown_outer_b\n";

const char* kWithoutPragmas =
    "module sub(input logic i, output logic o);\n"
    "  assign o = ~i;\n"
    "endmodule\n"
    "module top;\n"
    "  parameter P = 5;\n"
    "  wire w;\n"
    "  logic [7:0] r;\n"
    "  sub u0(.i(w), .o());\n"
    "  initial r = 8'd9;\n"
    "endmodule\n";

// The defining property of the clause: an unrecognized pragma_name leaves the
// interpretation of the surrounding source text alone, so the elaborated
// design must be indistinguishable from the pragma-free one.
TEST(PragmaElaboration, ElaboratedDesignMatchesPragmaFreeSource) {
  ElabFixture with;
  auto* design_with = ElaborateWithPreprocessor(kWithPragmas, with, "top");
  ASSERT_NE(design_with, nullptr);
  ASSERT_FALSE(with.has_errors);

  ElabFixture without;
  auto* design_without =
      ElaborateWithPreprocessor(kWithoutPragmas, without, "top");
  ASSERT_NE(design_without, nullptr);
  ASSERT_FALSE(without.has_errors);

  EXPECT_EQ(ShapeOfDesign(*design_with), ShapeOfDesign(*design_without));
  EXPECT_EQ(design_with->all_modules.size(),
            design_without->all_modules.size());
}

// A pragma line standing between a declaration and its use does not break the
// binding, which would show up as an unresolved reference.
TEST(PragmaElaboration, DeclarationAndUseStillBindAcrossAPragma) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module top;\n"
      "  parameter WIDTH = 4;\n"
      "  `pragma unknown_between encoding = ( style = onehot )\n"
      "  logic [WIDTH-1:0] bus;\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  const auto& vars = design->top_modules[0]->variables;
  ASSERT_EQ(vars.size(), 1u);
  EXPECT_EQ(vars[0].name, "bus");
  EXPECT_EQ(vars[0].width, 4u);
}

// The module the pragma sits inside is still the module the elaborator sees;
// the directive does not terminate or reopen a design element.
TEST(PragmaElaboration, PragmaInsideModuleDoesNotSplitIt) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module top;\n"
      "  wire a;\n"
      "  `pragma unknown_mid\n"
      "  wire b;\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->nets.size(), 2u);
  EXPECT_EQ(design->all_modules.size(), 1u);
}

// A package is a syntactic position of its own; a pragma between its items
// leaves the package and its contents where the elaborator expects them.
TEST(PragmaElaboration, PragmaInsidePackageDoesNotDisturbIt) {
  const char* body =
      "package pkg;\n"
      "PRAGMA_SLOT"
      "  parameter DEPTH = 6;\n"
      "endpackage\n"
      "module top;\n"
      "  wire w;\n"
      "endmodule\n";
  std::string with = body;
  with.replace(with.find("PRAGMA_SLOT"), 11,
               "  `pragma unknown_in_package mode = fast\n");
  std::string without = body;
  without.replace(without.find("PRAGMA_SLOT"), 11, "");

  ElabFixture fw;
  auto* design_with = ElaborateWithPreprocessor(with, fw, "top");
  ASSERT_NE(design_with, nullptr);
  ASSERT_FALSE(fw.has_errors);
  EXPECT_EQ(design_with->packages.size(), 1u);

  ElabFixture fo;
  auto* design_without = ElaborateWithPreprocessor(without, fo, "top");
  ASSERT_NE(design_without, nullptr);
  ASSERT_FALSE(fo.has_errors);

  EXPECT_EQ(design_with->packages.size(), design_without->packages.size());
  EXPECT_EQ(ShapeOfDesign(*design_with), ShapeOfDesign(*design_without));
}

// A generate block is unrolled during elaboration, so a pragma written inside
// one must be gone well before the loop is expanded.
TEST(PragmaElaboration, PragmaInsideGenerateBlockDoesNotDisturbIt) {
  const char* body =
      "module top;\n"
      "  genvar i;\n"
      "  generate\n"
      "    for (i = 0; i < 3; i = i + 1) begin : g\n"
      "      PRAGMA_SLOT"
      "      wire w;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n";
  std::string with = body;
  with.replace(with.find("PRAGMA_SLOT"), 11,
               "`pragma unknown_in_generate k = 1\n");
  std::string without = body;
  without.replace(without.find("PRAGMA_SLOT"), 11, "");

  ElabFixture fw;
  auto* design_with = ElaborateWithPreprocessor(with, fw, "top");
  ASSERT_NE(design_with, nullptr);
  ASSERT_FALSE(fw.has_errors);

  ElabFixture fo;
  auto* design_without = ElaborateWithPreprocessor(without, fo, "top");
  ASSERT_NE(design_without, nullptr);
  ASSERT_FALSE(fo.has_errors);

  EXPECT_EQ(ShapeOfDesign(*design_with), ShapeOfDesign(*design_without));
}

// A malformed pragma is a syntax error at the preprocessor, so elaboration of
// the source it introduces is reported rather than silently accepted.
TEST(PragmaElaboration, MalformedPragmaIsDiagnosed) {
  ElabFixture f;
  ElaborateWithPreprocessor(
      "module top;\n"
      "  `pragma 42 = bad\n"
      "  wire a;\n"
      "endmodule\n",
      f, "top");
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
