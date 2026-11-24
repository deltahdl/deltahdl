#include <gtest/gtest.h>

#include <cstddef>
#include <map>
#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_dpi_c_binding.h"
#include "simulator/dpi_runtime.h"
#include "simulator/svdpi.h"
#include "simulator/svdpi_sv31a.h"

using namespace delta;

namespace {

TEST(DpiCompatibility, TheVersionStringTellsTheLevel) {
  EXPECT_STREQ(svDpiVersion(), "1800-2005");
  EXPECT_EQ(DpiCompatibilityLevelOf(svDpiVersion()),
            DpiCompatibilityLevel::kIeee1800);
  EXPECT_EQ(DpiCompatibilityLevelOf("SV3.1a"), DpiCompatibilityLevel::kSv31a);
  EXPECT_FALSE(DpiOpaqueHandlesAreRequiredForAllPackedArguments(
      DpiCompatibilityLevel::kIeee1800));
  EXPECT_TRUE(DpiOpaqueHandlesAreRequiredForAllPackedArguments(
      DpiCompatibilityLevel::kSv31a));
}

TEST(DpiCompatibility, TheSpecStringSelectsThePassingSemantics) {
  EXPECT_EQ(DpiPassingSemanticsOfSpecString("DPI"),
            DpiPackedArgPassing::kSv31aReference);
  EXPECT_EQ(DpiPassingSemanticsOfSpecString("DPI-C"),
            DpiPackedArgPassing::kCanonical);
}

TEST(DpiCompatibility, TheSv31aDefinitionsAreOptionalAndBindingMayFail) {
  EXPECT_FALSE(DpiSv31aDefinitionsAreObligatoryInSvdpiH());
  EXPECT_TRUE(DpiCCodeMayFailToBind(false));
  EXPECT_FALSE(DpiCCodeMayFailToBind(true));
}

TEST(DpiCompatibility, ADesignsDeclarationsSelectTheirSemanticsPerFunction) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  import \"DPI\" function void legacy(input bit [7:0] v);\n"
      "  import \"DPI-C\" function void current(input bit [7:0] v);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* dpi = f.ctx.GetDpiRuntime();
  ASSERT_NE(dpi, nullptr);
  const DpiRtFunction* legacy = dpi->FindImport("legacy");
  ASSERT_NE(legacy, nullptr);
  EXPECT_EQ(legacy->packed_arg_passing, DpiPackedArgPassing::kSv31aReference);
  const DpiRtFunction* current = dpi->FindImport("current");
  ASSERT_NE(current, nullptr);
  EXPECT_EQ(current->packed_arg_passing, DpiPackedArgPassing::kCanonical);
}

void TakeLogicReferences(svLogicPackedArrRef in, svLogicPackedArrRef out,
                         svLogicPackedArrRef both) {
  svLogicVec32 value[SV_CANONICAL_SIZE(40)] = {};
  svGetLogicVec32(value, in, 40);
  SeeInC({value[0].c, value[0].d, value[1].c & 0xFFu, value[1].d & 0xFFu});
  svPutLogicVec32(out, value, 40);
  SeeInC({svGetSelectLogic(both, 0), svGetSelectLogic(both, 39)});
  svPutSelectLogic(both, 39, sv_1);
}

void TakeBitReferences(svBitPackedArrRef in, svBitPackedArrRef out,
                       svBitPackedArrRef both) {
  svBitVec32 value[SV_CANONICAL_SIZE(40)] = {};
  svGetBitVec32(value, in, 40);
  SeeInC({value[0], value[1] & 0xFFu});
  svPutBitVec32(out, value, 40);
  SeeInC({svGetBits(both, 28, 8)});
  svPutPartSelectBit(both, 0xA5u, 28, 8);
}

int TakeReferencesInATask(svBitPackedArrRef in, svLogicPackedArrRef out) {
  svLogicVec32 value[SV_CANONICAL_SIZE(40)] = {};
  value[0].c = svGet32Bits(in, 0);
  value[1].c = svGetBits(in, 32, 8);
  svPutLogicVec32(out, value, 40);
  return 0;
}

void SeeReference(svBitPackedArrRef in) { SeeInC({svGetBits(in, 4, 8)}); }

void SeeCanonical(const svBitVecVal* in) { SeeInC({in[0], in[1]}); }

void RunWithReferences(const std::string& src, SimFixture& f,
                       const std::map<std::string, void*>& functions,
                       const std::string& dir_name) {
  SeenInC().clear();
  RunWithImportsBound(src, f, functions, dir_name);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(DpiCompatibilityOfACall, LogicFormalsCrossAsReferences) {
  SimFixture f;
  RunWithReferences(
      "module t;\n"
      "  import \"DPI\" function void take(input logic [39:0] a,\n"
      "                                  output logic [39:0] b,\n"
      "                                  inout logic [39:0] c);\n"
      "  logic [39:0] a = 40'h8Z_1234_567X, b, c = 40'h00_0000_0001;\n"
      "  bit same;\n"
      "  initial begin\n"
      "    take(a, b, c);\n"
      "    same = a === b;\n"
      "  end\n"
      "endmodule\n",
      f, {{"take", CAddress(&TakeLogicReferences)}}, "annex_h_14_01_logic");
  EXPECT_EQ(SeenInC(),
            (std::vector<long long>{0x1234567F, 0xF, 0x80, 0xF, sv_1, sv_0}));
  EXPECT_EQ(DesignValue(f, "same"), 1u);
  EXPECT_EQ(DesignValue(f, "c"), 0x8000000001u);
}

TEST(DpiCompatibilityOfACall, BitFormalsCrossAsReferences) {
  SimFixture f;
  RunWithReferences(
      "module t;\n"
      "  import \"DPI\" function void take(input bit [39:0] a,\n"
      "                                  output bit [39:0] b,\n"
      "                                  inout bit [39:0] c);\n"
      "  bit [39:0] a = 40'h8F_1234_5678, b, c = 40'h03_C000_0001;\n"
      "  initial take(a, b, c);\n"
      "endmodule\n",
      f, {{"take", CAddress(&TakeBitReferences)}}, "annex_h_14_01_bit");
  EXPECT_EQ(SeenInC(), (std::vector<long long>{0x12345678, 0x8F, 0x3C}));
  EXPECT_EQ(DesignValue(f, "b"), 0x8F12345678u);
  EXPECT_EQ(DesignValue(f, "c"), 0x0A50000001u);
}

TEST(DpiCompatibilityOfACall, ATasksFormalsCrossAsReferences) {
  SimFixture f;
  RunWithReferences(
      "module t;\n"
      "  import \"DPI\" context task take(input bit [39:0] a,\n"
      "                                 output logic [39:0] b);\n"
      "  bit [39:0] a = 40'h8F_1234_5678;\n"
      "  logic [39:0] b;\n"
      "  initial take(a, b);\n"
      "endmodule\n",
      f, {{"take", CAddress(&TakeReferencesInATask)}}, "annex_h_14_01_task");
  EXPECT_EQ(DesignValue(f, "b"), 0x8F12345678u);
}

TEST(DpiCompatibilityOfACall, EachImportOfARunCrossesInItsOwnForm) {
  SimFixture f;
  RunWithReferences(
      "module t;\n"
      "  import \"DPI\" function void legacy(input bit [39:0] v);\n"
      "  import \"DPI-C\" function void current(input bit [39:0] v);\n"
      "  initial begin\n"
      "    legacy(40'h8F_1234_5678);\n"
      "    current(40'h8F_1234_5678);\n"
      "  end\n"
      "endmodule\n",
      f,
      {{"legacy", CAddress(&SeeReference)},
       {"current", CAddress(&SeeCanonical)}},
      "annex_h_14_01_both");
  EXPECT_EQ(SeenInC(), (std::vector<long long>{0x67, 0x12345678, 0x8F}));
}

std::vector<long long> ReferencesSeenInARunOf(const std::string& src) {
  SimFixture f;
  RunWithReferences(src, f, {{"legacy", CAddress(&SeeReference)}},
                    "annex_h_14_01_place");
  const auto* legacy = f.ctx.GetDpiRuntime()->FindImport("legacy");
  EXPECT_NE(legacy, nullptr);
  if (legacy != nullptr) {
    EXPECT_EQ(legacy->packed_arg_passing, DpiPackedArgPassing::kSv31aReference);
  }
  return SeenInC();
}

const char* const kLegacyImport =
    "import \"DPI\" function void legacy(input bit [39:0] v);\n";

TEST(DpiCompatibilityOfACall, APackagesImportCrossesAsAReference) {
  EXPECT_EQ(ReferencesSeenInARunOf(std::string("package p;\n") + kLegacyImport +
                                   "endpackage\n"
                                   "module t;\n"
                                   "  initial p::legacy(40'h8F_1234_5678);\n"
                                   "endmodule\n"),
            (std::vector<long long>{0x67}));
}

TEST(DpiCompatibilityOfACall, AnInterfacesImportCrossesAsAReference) {
  EXPECT_EQ(
      ReferencesSeenInARunOf(std::string("interface i;\n") + kLegacyImport +
                             "  initial legacy(40'h8F_1234_5678);\n"
                             "endinterface\n"
                             "module t;\n"
                             "  i u();\n"
                             "endmodule\n"),
      (std::vector<long long>{0x67}));
}

TEST(DpiCompatibilityOfACall, AProgramsImportCrossesAsAReference) {
  EXPECT_EQ(ReferencesSeenInARunOf(std::string("program p;\n") + kLegacyImport +
                                   "  initial legacy(40'h8F_1234_5678);\n"
                                   "endprogram\n"
                                   "module t;\n"
                                   "  p u();\n"
                                   "endmodule\n"),
            (std::vector<long long>{0x67}));
}

TEST(DpiCompatibilityOfACall, TheCompilationUnitsImportCrossesAsAReference) {
  EXPECT_EQ(ReferencesSeenInARunOf(std::string(kLegacyImport) +
                                   "module t;\n"
                                   "  initial legacy(40'h8F_1234_5678);\n"
                                   "endmodule\n"),
            (std::vector<long long>{0x67}));
}

using ExportOfReferences = void (*)(svBitPackedArrRef, svLogicPackedArrRef);
using ExportOfVectors = void (*)(const svBitVecVal*, svLogicVecVal*);

void CallBothExports() {
  auto legacy = NamedExport<ExportOfReferences>("legacy_export");
  auto current = NamedExport<ExportOfVectors>("current_export");
  if (legacy == nullptr || current == nullptr) return;
  const svBitVec32 kIn[SV_CANONICAL_SIZE(40)] = {0x12345678u, 0x8Fu};
  std::vector<char> in(static_cast<std::size_t>(svSizeOfBitPackedArr(40)));
  std::vector<char> out(static_cast<std::size_t>(svSizeOfLogicPackedArr(40)));
  svPutBitVec32(in.data(), kIn, 40);
  legacy(in.data(), out.data());
  svLogicVec32 value[SV_CANONICAL_SIZE(40)] = {};
  svGetLogicVec32(value, out.data(), 40);
  SeeInC({value[0].c, value[0].d, value[1].c & 0xFFu, value[1].d & 0xFFu});
  svLogicVecVal canonical[SV_PACKED_DATA_NELEMS(40)] = {};
  current(kIn, canonical);
  SeeInC({canonical[0].aval, canonical[0].bval});
}

int CallTheExportedTask() {
  auto legacy = NamedExport<int (*)(svBitPackedArrRef, svLogicPackedArrRef)>(
      "legacy_task");
  if (legacy == nullptr) return 0;
  svBitVec32 in[SV_CANONICAL_SIZE(40)] = {0x12345678u, 0x8Fu};
  svLogicVec32 out[SV_CANONICAL_SIZE(40)] = {};
  int result = legacy(in, out);
  svLogicVec32 value[SV_CANONICAL_SIZE(40)] = {};
  svGetLogicVec32(value, out, 40);
  SeeInC({value[0].c, value[0].d});
  return result;
}

TEST(DpiCompatibilityOfACall, EachExportOfARunCrossesInItsOwnForm) {
  SimFixture f;
  RunWithReferences(
      "module t;\n"
      "  import \"DPI-C\" context function void call_both();\n"
      "  export \"DPI\" function legacy_export;\n"
      "  export \"DPI-C\" function current_export;\n"
      "  bit [39:0] seen;\n"
      "  function void legacy_export(input bit [39:0] a,\n"
      "                              output logic [39:0] b);\n"
      "    seen = a;\n"
      "    b = 40'h8Z_1234_567X;\n"
      "  endfunction\n"
      "  function void current_export(input bit [39:0] a,\n"
      "                               output logic [39:0] b);\n"
      "    b = a + 1;\n"
      "  endfunction\n"
      "  initial call_both();\n"
      "endmodule\n",
      f, {{"call_both", CAddress(&CallBothExports)}}, "annex_h_14_01_exports");
  EXPECT_EQ(DesignValue(f, "seen"), 0x8F12345678u);
  EXPECT_EQ(SeenInC(), (std::vector<long long>{0x1234567F, 0xF, 0x80, 0xF,
                                               0x12345679, 0}));
}

TEST(DpiCompatibilityOfACall, AnExportedTaskTakesReferences) {
  SimFixture f;
  RunWithReferences(
      "module t;\n"
      "  import \"DPI-C\" context task call_task();\n"
      "  export \"DPI\" task legacy_task;\n"
      "  bit [39:0] seen;\n"
      "  task legacy_task(input bit [39:0] a, output logic [39:0] b);\n"
      "    seen = a;\n"
      "    b = 40'h8Z_1234_567X;\n"
      "  endtask\n"
      "  initial call_task();\n"
      "endmodule\n",
      f, {{"call_task", CAddress(&CallTheExportedTask)}},
      "annex_h_14_01_export_task");
  EXPECT_EQ(DesignValue(f, "seen"), 0x8F12345678u);
  EXPECT_EQ(SeenInC(), (std::vector<long long>{0x1234567F, 0xF}));
}

}  // namespace
