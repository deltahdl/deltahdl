#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <string>
#include <utility>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(DriveStrengthElaboration, DriveStrengthOnVectorNetIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire [7:0] w;\n"
      "  assign (strong0, weak1) w = 8'd0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "drive strength on continuous assignment applies only to scalar nets", 3,
      "10.3.4"));
}

TEST(DriveStrengthElaboration, DriveStrengthOnScalarNetIsValid) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  assign (strong0, weak1) w = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(DriveStrengthElaboration, SupplyNetTypeHasNoStrengthError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  supply0 [7:0] s;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(DriveStrengthElaboration, DefaultStrengthIsZero) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  assign w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  EXPECT_EQ(mod->assigns[0].drive_strength0, 0u);
  EXPECT_EQ(mod->assigns[0].drive_strength1, 0u);
}

TEST(DriveStrengthElaboration, NetDeclStrengthOnScalarIsValid) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire (weak0, strong1) w = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(DriveStrengthElaboration, NetDeclStrengthOnVectorIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire (weak0, strong1) [3:0] w = 4'd0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "drive strength on continuous assignment applies only to scalar nets", 2,
      "10.3.4"));
}

TEST(DriveStrengthElaboration, DriveStrengthOnScalarVariableIsError) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  logic v;\n"
      "  assign (strong0, weak1) v = 1'b1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "drive strength not allowed on continuous assignment to a variable", 3,
      "10.3.4"));
}

TEST(DriveStrengthElaboration, DriveStrengthPropagatedToImplicitContAssign) {
  ElabFixture f;
  auto* design = Elaborate(
      "module t;\n"
      "  wire (supply0, strong1) w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->assigns.empty());
  EXPECT_EQ(mod->assigns[0].drive_strength0, 5u);
  EXPECT_EQ(mod->assigns[0].drive_strength1, 4u);
}

TEST(DriveStrengthElaboration, Supply1VectorNetTypeHasNoStrengthError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  supply1 [7:0] s;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(DriveStrengthElaboration, Highz0Highz1ContAssignIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  assign (highz0, highz1) w = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "drive strength (highz0, highz1) is illegal", 3,
                            "28.3.2"));
}

TEST(DriveStrengthElaboration, Highz1Highz0ContAssignIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  assign (highz1, highz0) w = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "drive strength (highz0, highz1) is illegal", 3,
                            "28.3.2"));
}

TEST(DriveStrengthElaboration, Highz0Highz1NetDeclIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  wire (highz0, highz1) w = 1'b0;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "drive strength (highz0, highz1) is illegal", 2,
                            "28.3.2"));
}

TEST(DriveStrengthElaboration, MultipleAssignsPreserveIndependentStrengths) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire a, b;\n"
      "  assign (supply0, supply1) a = 1'b1;\n"
      "  assign (weak0, weak1) b = 1'b0;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 2u);
  EXPECT_EQ(mod->assigns[0].drive_strength0, 5u);
  EXPECT_EQ(mod->assigns[0].drive_strength1, 5u);
  EXPECT_EQ(mod->assigns[1].drive_strength0, 2u);
  EXPECT_EQ(mod->assigns[1].drive_strength1, 2u);
}

TEST(DriveStrengthElaboration, DriveStrengthOnSelectOfVectorNetIsError) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  wire [7:0] w; wire a, b; supply1 [3:0] s;\n"
      "  assign (weak0, weak1) w[3:0] = 4'h0;\n"
      "  assign (weak0, weak1) {a, b} = 2'b0;\n"
      "  assign (weak0, weak1) s[1:0] = 2'b0;\n"
      "endmodule\n",
      f);
  for (uint32_t line : {3u, 4u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "drive strength on continuous assignment "
                              "applies only to scalar nets",
                              line, "10.3.4"));
  }
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "drive strength on continuous assignment does "
                            "not apply to supply0 or supply1 nets",
                            5, "10.3.4"));
}

TEST(DriveStrengthElaboration, DriveStrengthOnSupplyNetIsError) {
  ElabFixture f;
  Elaborate(
      "module t;\n"
      "  supply1 [3:0] s; supply0 z; wire w;\n"
      "  assign (weak0, weak1) s = 4'h0;\n"
      "  assign (weak0, weak1) z = 1'b1;\n"
      "  supply1 (weak0, weak1) v = 1'b0;\n"
      "  assign (weak0, weak1) w = 1'b1;\n"
      "endmodule\n",
      f);
  for (uint32_t line : {3u, 4u, 5u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "drive strength on continuous assignment does "
                              "not apply to supply0 or supply1 nets",
                              line, "10.3.4"));
  }
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "drive strength on continuous assignment "
                             "applies only to scalar nets",
                             3, "10.3.4"));
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "drive strength on continuous assignment does "
                             "not apply to supply0 or supply1 nets",
                             6, "10.3.4"));
}

TEST(DriveStrengthElaboration, DriveStrengthOnMemberOfStructureNetIsError) {
  ElabFixture f;
  Elaborate(
      "interface bus;\n"
      "  wire y;\n"
      "endinterface\n"
      "module m;\n"
      "  typedef struct packed { logic a; logic b; } s_t;\n"
      "  wire s_t n;\n"
      "  logic x;\n"
      "  bus b();\n"
      "  assign (weak0, weak1) n.a = x;\n"
      "  assign (weak0, weak1) b.y = x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "drive strength on continuous assignment applies only to scalar nets", 9,
      "10.3.4"));
  EXPECT_FALSE(ReportedError(
      f.diag.Diagnostics(),
      "drive strength on continuous assignment applies only to scalar nets", 10,
      "10.3.4"));
}

struct GenerateBlockForm {
  const char* open;
  const char* close;
};

constexpr GenerateBlockForm kGenerateBlockForms[] = {
    {"  if (1) begin : g\n", "  end\n"},
    {"  case (1) 1: begin : g\n", "  end endcase\n"},
    {"  for (genvar i = 0; i < 1; i++) begin : g\n", "  end\n"}};

std::string ModuleWithGenerateBlock(const char* module_items,
                                    const GenerateBlockForm& form,
                                    const std::string& block_items) {
  return std::string("module m;\n") + module_items + form.open + block_items +
         form.close + "endmodule\n";
}

void ExpectStrengthReportInEachBlock(const char* module_items,
                                     const std::string& block_items,
                                     const char* message, int line) {
  for (const auto& form : kGenerateBlockForms) {
    const std::string kSrc =
        ModuleWithGenerateBlock(module_items, form, block_items);
    ElabFixture f;
    ElaborateSrc(kSrc, f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, line, "10.3.4"))
        << kSrc;
  }
}

void ExpectNoReportInEachBlock(const char* module_items,
                               const std::string& block_items) {
  for (const auto& form : kGenerateBlockForms) {
    const std::string kSrc =
        ModuleWithGenerateBlock(module_items, form, block_items);
    ElabFixture f;
    ElaborateSrc(kSrc, f);
    EXPECT_FALSE(f.diag.HasErrors()) << kSrc;
  }
}

constexpr const char* kScalarNetsOnly =
    "drive strength on continuous assignment applies only to scalar nets";
constexpr const char* kNotSupplyNets =
    "drive strength on continuous assignment does not apply to supply0 or "
    "supply1 nets";
constexpr const char* kStrongAssignOfVector =
    "    assign (strong0, weak1) w = 4'd0;\n";
constexpr const char* kStrongAssignOfScalar =
    "    assign (strong0, weak1) w = 1'b0;\n";

TEST(DriveStrengthElaboration,
     DISABLED_DriveStrengthOnAVectorNetABlockDeclaresIsError) {
  ExpectStrengthReportInEachBlock(
      "", std::string("    wire [3:0] w;\n") + kStrongAssignOfVector,
      kScalarNetsOnly, 4);
}

TEST(DriveStrengthElaboration, DriveStrengthOnAScalarNetABlockDeclaresIsValid) {
  ExpectNoReportInEachBlock(
      "", std::string("    wire w;\n") + kStrongAssignOfScalar);
}

TEST(DriveStrengthElaboration,
     DISABLED_DriveStrengthOnASupplyNetABlockDeclaresIsError) {
  for (const char* decl : {"    supply0 w;\n", "    supply1 w;\n"}) {
    ExpectStrengthReportInEachBlock(
        "", std::string(decl) + kStrongAssignOfScalar, kNotSupplyNets, 4);
  }
}

TEST(DriveStrengthElaboration,
     DISABLED_DriveStrengthOnABlockVectorShadowingAModuleScalarIsError) {
  ExpectStrengthReportInEachBlock(
      "  wire w;\n", std::string("    wire [3:0] w;\n") + kStrongAssignOfVector,
      kScalarNetsOnly, 5);
}

TEST(DriveStrengthElaboration,
     DISABLED_DriveStrengthOnABlockScalarShadowingAModuleVectorIsValid) {
  ExpectNoReportInEachBlock("  wire [3:0] w;\n", std::string("    wire w;\n") +
                                                     kStrongAssignOfScalar);
}

TEST(DriveStrengthElaboration,
     DISABLED_DriveStrengthOnABlockScalarShadowingAModuleSupplyNetIsValid) {
  for (const char* decl : {"  supply0 w;\n", "  supply1 w;\n"}) {
    ExpectNoReportInEachBlock(
        decl, std::string("    wire w;\n") + kStrongAssignOfScalar);
  }
}

TEST(DriveStrengthElaboration, DriveStrengthInAnInterfaceOrProgramIsChecked) {
  for (const auto& [kind, instantiation] :
       {std::pair{"interface", "module top;\n  m u();\nendmodule\n"},
        std::pair{"program", ""}}) {
    const std::string kSrc = std::string(kind) +
                             " m;\n"
                             "  wire [3:0] w;\n"
                             "  supply0 s;\n"
                             "  wire n;\n"
                             "  assign (strong0, weak1) w = 4'd0;\n"
                             "  assign (strong0, weak1) s = 1'b1;\n"
                             "  assign (strong0, weak1) n = 1'b1;\n"
                             "end" +
                             kind + "\n" + instantiation;
    ElabFixture f;
    ElaborateSrc(kSrc, f);
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kScalarNetsOnly, 5, "10.3.4"))
        << kSrc;
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kNotSupplyNets, 6, "10.3.4"))
        << kSrc;
    EXPECT_EQ(f.diag.ErrorCount(), 2u) << kSrc;
  }
}

}  // namespace
