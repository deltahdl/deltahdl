#include <gtest/gtest.h>

#include <filesystem>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "fixture_scratch_dir.h"
#include "helpers_reported_error.h"
#include "helpers_rtlir_lookup.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/library_map.h"
#include "parser/single_pass_compile.h"

using namespace delta;
namespace fs = std::filesystem;

TEST(CompilationUnitElaboration, ElabModuleWithCuFunction) {
  EXPECT_TRUE(
      ElabOk("function int cu_func(int x); return x; endfunction\n"
             "module m;\n"
             "  logic [7:0] data;\n"
             "endmodule\n"));
}

TEST(CompilationUnitElaboration, CuScopeFunctionInDesign) {
  ElabFixture f;
  auto* design = Elaborate(
      "function int helper(int x); return x + 1; endfunction\n"
      "task auto_task; endtask\n"
      "module m; endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(design->cu_function_decls.size(), 2u);
  EXPECT_EQ(design->cu_function_decls[0]->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(design->cu_function_decls[0]->name, "helper");
  EXPECT_EQ(design->cu_function_decls[1]->kind, ModuleItemKind::kTaskDecl);
  EXPECT_EQ(design->cu_function_decls[1]->name, "auto_task");
}

TEST(CompilationUnitElaboration, CuScopeTypedefVisibleInModule) {
  ElabFixture f;
  auto* design = Elaborate(
      "typedef logic [15:0] word_t;\n"
      "module m;\n"
      "  word_t data;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].name, "data");
  EXPECT_EQ(mod->variables[0].width, 16u);
}

TEST(CompilationUnitElaboration, CuScopeTypedefTypeWidth) {
  ElabFixture f;
  auto* design = Elaborate(
      "typedef logic [7:0] byte_t;\n"
      "module m; endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto it = design->type_widths.find("byte_t");
  ASSERT_NE(it, design->type_widths.end());
  EXPECT_EQ(it->second, 8u);
}

TEST(CompilationUnitElaboration, CuScopeLocalparamElaborates) {
  EXPECT_TRUE(
      ElabOk("localparam int WIDTH = 8;\n"
             "module m;\n"
             "  logic [WIDTH-1:0] data;\n"
             "endmodule\n"));
}

TEST(CompilationUnitElaboration, CuScopeClassVisibleInModule) {
  EXPECT_TRUE(
      ElabOk("class my_class;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  my_class obj;\n"
             "endmodule\n"));
}

TEST(CompilationUnitElaboration, CuScopeItemsInSourceOrder) {
  ElabFixture f;
  auto* design = Elaborate(
      "typedef int first_t;\n"
      "function int second_func(int x); return x; endfunction\n"
      "localparam int THIRD = 3;\n"
      "module m; endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(CompilationUnitElaboration, MultipleCuScopeTypedefs) {
  ElabFixture f;
  auto* design = Elaborate(
      "typedef logic [7:0] byte_t;\n"
      "typedef logic [31:0] word_t;\n"
      "module m;\n"
      "  byte_t a;\n"
      "  word_t b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 2u);
  EXPECT_EQ(mod->variables[0].width, 8u);
  EXPECT_EQ(mod->variables[1].width, 32u);
}
TEST(CompilationUnitElaboration, CuScopeTaskElaboratesSuccessfully) {
  EXPECT_TRUE(
      ElabOk("task my_task;\n"
             "endtask\n"
             "module m; endmodule\n"));
}

TEST(CompilationUnitElaboration, LocalScopeShadowsCuScopeLocalparam) {
  EXPECT_TRUE(
      ElabOk("localparam int WIDTH = 8;\n"
             "module m;\n"
             "  localparam int WIDTH = 16;\n"
             "  logic [WIDTH-1:0] data;\n"
             "endmodule\n"));
}

TEST(CompilationUnitElaboration, CuScopeLocalparamVisibleInMultipleModules) {
  ElabFixture f;
  auto* design = Elaborate(
      "localparam int WIDTH = 8;\n"
      "module sub;\n"
      "  logic [WIDTH-1:0] b;\n"
      "endmodule\n"
      "module top;\n"
      "  logic [WIDTH-1:0] a;\n"
      "  sub u1();\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* a = FindVar(design, "top", "a");
  ASSERT_NE(a, nullptr);
  EXPECT_EQ(a->width, 8u);
  const auto* b = FindVar(design, "sub", "b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->width, 8u);
}

TEST(CompilationUnitElaboration, CuScopeLocalparamVisibleInASecondTopModule) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "localparam int WIDTH = 8;\n"
      "module first;\n"
      "  logic [WIDTH-1:0] a;\n"
      "endmodule\n"
      "module second;\n"
      "  logic [WIDTH-1:0] b;\n"
      "endmodule\n",
      f, "", true);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* b = FindVar(design, "second", "b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(b->width, 8u);
}

TEST(CompilationUnitElaboration, CuScopeVarDeclElaborates) {
  EXPECT_TRUE(
      ElabOk("int global_counter;\n"
             "module m;\n"
             "  logic sig;\n"
             "endmodule\n"));
}

TEST(CompilationUnitElaboration,
     DollarUnitPrefixResolvesToCompilationUnitScopeDespiteLocalShadow) {
  ElabFixture f;
  auto* design = Elaborate(
      "localparam int K = 8;\n"
      "module m;\n"
      "  localparam int K = 3;\n"
      "  logic [$unit::K-1:0] wide;\n"
      "  logic [K-1:0] narrow;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 2u);
  EXPECT_EQ(mod->variables[0].name, "wide");
  EXPECT_EQ(mod->variables[0].width, 8u);
  EXPECT_EQ(mod->variables[1].name, "narrow");
  EXPECT_EQ(mod->variables[1].width, 3u);
}

TEST(CompilationUnitElaboration,
     DollarUnitPrefixResolvesCompilationUnitParameterPastLocalShadow) {
  ElabFixture f;
  auto* design = Elaborate(
      "parameter int K = 8;\n"
      "module m;\n"
      "  localparam int K = 3;\n"
      "  logic [$unit::K-1:0] wide;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].name, "wide");
  EXPECT_EQ(mod->variables[0].width, 8u);
}

TEST(CompilationUnitElaboration,
     DollarUnitPrefixResolvesToCompilationUnitScopeInParameterInitializer) {
  ElabFixture f;
  auto* design = Elaborate(
      "localparam int K = 8;\n"
      "module m;\n"
      "  localparam int K = 3;\n"
      "  localparam int M = $unit::K + 1;\n"
      "  logic [M-1:0] wide;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].name, "wide");
  EXPECT_EQ(mod->variables[0].width, 9u);
}

TEST(CompilationUnitElaboration, ForwardReferenceToCuScopeFunctionAccepted) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  int observed;\n"
             "  initial observed = helper(5);\n"
             "endmodule\n"
             "function int helper(int x); return x + 1; endfunction\n"));
}

TEST(CompilationUnitElaboration, ForwardReferenceToCuScopeTaskAccepted) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  initial later_task();\n"
             "endmodule\n"
             "task later_task; endtask\n"));
}

namespace {

struct CommandLineHarness {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  LibraryMap libs;
  CompilationUnit unit;
  SinglePassCompiler compiler{libs, mgr, arena, diag};
};

constexpr const char* kLibMap = "library rtlLib src/*.sv;\n";

bool CompileCommandLineOnly(CommandLineHarness& h, const ScratchDir& tmp,
                            const std::vector<fs::path>& files) {
  if (!h.libs.LoadMapFile(tmp.dir / "lib.map")) return false;
  return h.compiler.CompileCommandLine(files, h.unit);
}

RtlirDesign* CompileCommandLineAndElaborate(CommandLineHarness& h,
                                            const ScratchDir& tmp,
                                            const std::vector<fs::path>& files,
                                            std::string_view top) {
  if (!CompileCommandLineOnly(h, tmp, files)) return nullptr;
  Elaborator elab(h.arena, h.diag, &h.unit);
  return elab.Elaborate(top);
}

const RtlirModule* SoleTopModule(RtlirDesign* design) {
  if (design == nullptr || design->top_modules.size() != 1u) return nullptr;
  return design->top_modules[0];
}

const ModuleItem* SoleUdpInstance(const CompilationUnit& unit,
                                  std::string_view module_name) {
  const ModuleItem* found = nullptr;
  for (const auto* decl : unit.modules) {
    if (decl->name != module_name) continue;
    for (const auto* item : decl->items) {
      if (item->kind != ModuleItemKind::kUdpInst) continue;
      if (found != nullptr) return nullptr;
      found = item;
    }
  }
  return found;
}

constexpr const char* kAndPrimitive =
    "primitive myudp(output q, input d, clk);\n"
    "  table\n"
    "    0 0 : 0;\n"
    "    0 1 : 0;\n"
    "    1 0 : 0;\n"
    "    1 1 : 1;\n"
    "  endtable\n"
    "endprimitive\n";

constexpr const char* kInverterPrimitive =
    "primitive myudp(output q, input d);\n"
    "  table\n"
    "    0 : 1;\n"
    "    1 : 0;\n"
    "  endtable\n"
    "endprimitive\n";

TEST(CompilationUnitScopeAcrossCommandLineFiles,
     PackageImportedInOneFileResolvesATypeDeclaredInAnother) {
  ScratchDir tmp;
  tmp.Write("lib.map", kLibMap);
  auto pkg = tmp.Write("src/pkg.sv",
                       "package p;\n"
                       "  typedef logic [7:0] byte_t;\n"
                       "endpackage\n");
  auto top = tmp.Write("src/top.sv",
                       "module top;\n"
                       "  import p::*;\n"
                       "  byte_t b;\n"
                       "endmodule\n");

  CommandLineHarness h;
  const auto* mod =
      SoleTopModule(CompileCommandLineAndElaborate(h, tmp, {pkg, top}, ""));
  EXPECT_FALSE(h.diag.HasErrors());
  ASSERT_NE(mod, nullptr);
  ASSERT_EQ(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 8u);
}

TEST(CompilationUnitScopeAcrossCommandLineFiles,
     ExplicitPackageImportResolvesATypeDeclaredInAnotherFile) {
  ScratchDir tmp;
  tmp.Write("lib.map", kLibMap);
  auto pkg = tmp.Write("src/pkg.sv",
                       "package p;\n"
                       "  typedef logic [7:0] byte_t;\n"
                       "endpackage\n");
  auto top = tmp.Write("src/top.sv",
                       "module top;\n"
                       "  import p::byte_t;\n"
                       "  byte_t b;\n"
                       "endmodule\n");

  CommandLineHarness h;
  const auto* mod =
      SoleTopModule(CompileCommandLineAndElaborate(h, tmp, {pkg, top}, ""));
  EXPECT_FALSE(h.diag.HasErrors());
  ASSERT_NE(mod, nullptr);
  ASSERT_EQ(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 8u);
}

TEST(CompilationUnitScopeAcrossCommandLineFiles,
     ScopedPackageTypeNameResolvesAcrossFiles) {
  ScratchDir tmp;
  tmp.Write("lib.map", kLibMap);
  auto pkg = tmp.Write("src/pkg.sv",
                       "package p;\n"
                       "  typedef logic [7:0] byte_t;\n"
                       "endpackage\n");
  auto top = tmp.Write("src/top.sv",
                       "module top;\n"
                       "  p::byte_t b;\n"
                       "endmodule\n");

  CommandLineHarness h;
  const auto* mod =
      SoleTopModule(CompileCommandLineAndElaborate(h, tmp, {pkg, top}, ""));
  EXPECT_FALSE(h.diag.HasErrors());
  ASSERT_NE(mod, nullptr);
  ASSERT_EQ(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 8u);
}

TEST(CompilationUnitScopeAcrossCommandLineFiles,
     ClassExtendedInOneFileTakesTheTypeNamesOfABaseInAnother) {
  ScratchDir tmp;
  tmp.Write("lib.map", kLibMap);
  auto base = tmp.Write("src/base.sv",
                        "class B;\n"
                        "  typedef int t;\n"
                        "endclass\n");
  auto derived = tmp.Write("src/derived.sv",
                           "class D extends B;\n"
                           "  t x;\n"
                           "endclass\n"
                           "module top;\n"
                           "endmodule\n");

  CommandLineHarness h;
  const auto* mod = SoleTopModule(
      CompileCommandLineAndElaborate(h, tmp, {base, derived}, ""));
  EXPECT_FALSE(h.diag.HasErrors());
  ASSERT_NE(mod, nullptr);
  EXPECT_EQ(mod->name, "top");
}

}  // namespace

TEST(CompilationUnitScopeAcrossCommandLineFiles,
     TypedefDeclaredInOneFileIsVisibleInAnother) {
  ScratchDir tmp;
  tmp.Write("lib.map", kLibMap);
  auto types = tmp.Write("src/types.sv", "typedef logic [7:0] byte_t;\n");
  auto top = tmp.Write("src/top.sv",
                       "module top;\n"
                       "  byte_t b;\n"
                       "endmodule\n");

  CommandLineHarness h;
  const auto* mod =
      SoleTopModule(CompileCommandLineAndElaborate(h, tmp, {types, top}, ""));
  EXPECT_FALSE(h.diag.HasErrors());
  ASSERT_NE(mod, nullptr);
  ASSERT_EQ(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].name, "b");
  EXPECT_EQ(mod->variables[0].width, 8u);
}

TEST(CompilationUnitScopeAcrossCommandLineFiles,
     TypedefIsVisibleInTheFileThatDeclaredIt) {
  ScratchDir tmp;
  tmp.Write("lib.map", kLibMap);
  auto only = tmp.Write("src/only.sv",
                        "typedef logic [7:0] byte_t;\n"
                        "module top;\n"
                        "  byte_t b;\n"
                        "endmodule\n");

  CommandLineHarness h;
  const auto* mod =
      SoleTopModule(CompileCommandLineAndElaborate(h, tmp, {only}, ""));
  EXPECT_FALSE(h.diag.HasErrors());
  ASSERT_NE(mod, nullptr);
  ASSERT_EQ(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].name, "b");
  EXPECT_EQ(mod->variables[0].width, 8u);
}

TEST(CompilationUnitScopeAcrossCommandLineFiles,
     CompilationUnitClassIsVisibleInAnotherFile) {
  ScratchDir tmp;
  tmp.Write("lib.map", kLibMap);
  auto cls = tmp.Write("src/cls.sv",
                       "class my_class;\n"
                       "  int x;\n"
                       "endclass\n");
  auto top = tmp.Write("src/top.sv",
                       "module top;\n"
                       "  my_class obj;\n"
                       "endmodule\n");

  CommandLineHarness h;
  const auto* mod =
      SoleTopModule(CompileCommandLineAndElaborate(h, tmp, {cls, top}, ""));
  EXPECT_FALSE(h.diag.HasErrors());
  ASSERT_NE(mod, nullptr);
  EXPECT_EQ(mod->name, "top");
}

TEST(CompilationUnitScopeAcrossCommandLineFiles,
     ExternalConstraintBlockCompletesAPrototypeInAnotherFile) {
  ScratchDir tmp;
  tmp.Write("lib.map", kLibMap);
  auto cls = tmp.Write("src/cls.sv",
                       "class my_class;\n"
                       "  rand int x;\n"
                       "  extern constraint c1;\n"
                       "endclass\n");
  auto block = tmp.Write("src/block.sv",
                         "constraint my_class::c1 { x >= 0; }\n"
                         "module top;\n"
                         "endmodule\n");

  CommandLineHarness h;
  ASSERT_NE(CompileCommandLineAndElaborate(h, tmp, {cls, block}, ""), nullptr);
  EXPECT_FALSE(h.diag.HasErrors());
  ASSERT_EQ(h.unit.classes.size(), 1u);
  const ClassMember* proto = nullptr;
  for (const auto* m : h.unit.classes[0]->members) {
    if (m->kind == ClassMemberKind::kConstraint && m->name == "c1") proto = m;
  }
  ASSERT_NE(proto, nullptr);
  EXPECT_EQ(proto->constraint_exprs.size(), 1u);
}

TEST(CompilationUnitScopeAcrossCommandLineFiles,
     CompilationUnitBindReachesTheDesign) {
  ScratchDir tmp;
  tmp.Write("lib.map", kLibMap);
  auto probe = tmp.Write("src/probe.sv",
                         "module probe;\n"
                         "endmodule\n"
                         "bind cpu probe p();\n");
  auto top = tmp.Write("src/top.sv",
                       "module cpu;\n"
                       "endmodule\n"
                       "module top;\n"
                       "  cpu c1();\n"
                       "endmodule\n");

  CommandLineHarness h;
  auto* design = CompileCommandLineAndElaborate(h, tmp, {probe, top}, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(h.diag.HasErrors());
  auto it = design->all_modules.find("cpu");
  ASSERT_NE(it, design->all_modules.end());
  bool found = false;
  for (const auto& child : it->second->children) {
    if (child.inst_name == "p" && child.module_name == "probe" &&
        child.is_bound) {
      found = true;
    }
  }
  EXPECT_TRUE(found);
}

TEST(CompilationUnitScopeAcrossCommandLineFiles,
     PrimitiveDeclaredInOneFileParsesAsAPrimitiveInstanceInAnother) {
  ScratchDir tmp;
  tmp.Write("lib.map", kLibMap);
  auto prim = tmp.Write("src/prim.sv", kAndPrimitive);
  auto top = tmp.Write("src/top.sv",
                       "module top;\n"
                       "  wire q, d, clk;\n"
                       "  myudp u (q, d, clk);\n"
                       "endmodule\n");

  CommandLineHarness h;
  ASSERT_TRUE(CompileCommandLineOnly(h, tmp, {prim, top}));
  EXPECT_FALSE(h.diag.HasErrors());
  const auto* inst = SoleUdpInstance(h.unit, "top");
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(inst->inst_module, "myudp");
  EXPECT_EQ(inst->gate_inst_name, "u");
  EXPECT_TRUE(inst->inst_name.empty());
  EXPECT_EQ(inst->gate_terminals.size(), 3u);
}

TEST(CompilationUnitScopeAcrossCommandLineFiles,
     UnnamedPrimitiveInstanceParsesInAFileAfterTheDeclaration) {
  ScratchDir tmp;
  tmp.Write("lib.map", kLibMap);
  auto prim = tmp.Write("src/prim.sv", kAndPrimitive);
  auto top = tmp.Write("src/top.sv",
                       "module top;\n"
                       "  wire q, d, clk;\n"
                       "  myudp (q, d, clk);\n"
                       "endmodule\n");

  CommandLineHarness h;
  const auto* mod =
      SoleTopModule(CompileCommandLineAndElaborate(h, tmp, {prim, top}, ""));
  EXPECT_FALSE(h.diag.HasErrors());
  ASSERT_NE(mod, nullptr);
  const auto* inst = SoleUdpInstance(h.unit, "top");
  ASSERT_NE(inst, nullptr);
  EXPECT_TRUE(inst->gate_inst_name.empty());
  EXPECT_EQ(inst->gate_terminals.size(), 3u);
}

TEST(CompilationUnitScopeAcrossCommandLineFiles,
     GateDelayOnAPrimitiveInstanceSurvivesTheFileThatDeclaredIt) {
  ScratchDir tmp;
  tmp.Write("lib.map", kLibMap);
  auto prim = tmp.Write("src/prim.sv", kAndPrimitive);
  auto top = tmp.Write("src/top.sv",
                       "module top;\n"
                       "  wire q, d, clk;\n"
                       "  myudp #5 u (q, d, clk);\n"
                       "endmodule\n");

  CommandLineHarness h;
  const auto* mod =
      SoleTopModule(CompileCommandLineAndElaborate(h, tmp, {prim, top}, ""));
  EXPECT_FALSE(h.diag.HasErrors());
  ASSERT_NE(mod, nullptr);
  const auto* inst = SoleUdpInstance(h.unit, "top");
  ASSERT_NE(inst, nullptr);
  EXPECT_TRUE(inst->inst_params.empty());
  ASSERT_NE(inst->gate_delay, nullptr);
  EXPECT_EQ(inst->gate_delay->kind, ExprKind::kIntegerLiteral);
  EXPECT_EQ(inst->gate_delay->int_val, 5u);
}

TEST(CompilationUnitScopeAcrossCommandLineFiles,
     DriveStrengthOnAPrimitiveInstanceParsesInAFileAfterTheDeclaration) {
  ScratchDir tmp;
  tmp.Write("lib.map", kLibMap);
  auto prim = tmp.Write("src/prim.sv", kInverterPrimitive);
  auto top = tmp.Write("src/top.sv",
                       "module top;\n"
                       "  wire q, d;\n"
                       "  myudp (strong1, weak0) u (q, d);\n"
                       "endmodule\n");

  CommandLineHarness h;
  const auto* mod =
      SoleTopModule(CompileCommandLineAndElaborate(h, tmp, {prim, top}, ""));
  EXPECT_FALSE(h.diag.HasErrors());
  ASSERT_NE(mod, nullptr);
  const auto* inst = SoleUdpInstance(h.unit, "top");
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(inst->gate_inst_name, "u");
  EXPECT_EQ(inst->gate_terminals.size(), 2u);
  EXPECT_EQ(inst->drive_strength1, 4);
  EXPECT_EQ(inst->drive_strength0, 2);
}

TEST(CompilationUnitScopeAcrossCommandLineFiles,
     PrimitiveNameDoesNotReachTheNextCommandLine) {
  ScratchDir tmp;
  tmp.Write("lib.map", kLibMap);
  auto prim = tmp.Write("src/prim.sv", kAndPrimitive);
  auto top = tmp.Write("src/top.sv",
                       "module top;\n"
                       "  wire q, d, clk;\n"
                       "  myudp (q, d, clk);\n"
                       "endmodule\n");

  CommandLineHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  ASSERT_TRUE(h.compiler.CompileCommandLine({prim}, h.unit));
  CompilationUnit second;
  EXPECT_TRUE(h.compiler.CompileCommandLine({top}, second));
  const auto* inst = SoleUdpInstance(second, "top");
  ASSERT_NE(inst, nullptr);
  EXPECT_TRUE(inst->udp_undeclared_at_parse);
}

TEST(CompilationUnitScopeAcrossCommandLineFiles,
     ASkippedRecompileCarriesTheCompilationUnitTimeunit) {
  ScratchDir tmp;
  tmp.Write("lib.map", kLibMap);
  auto only = tmp.Write("src/only.sv",
                        "timeunit 100ps / 10fs;\n"
                        "module top;\n"
                        "endmodule\n");

  CommandLineHarness h;
  ASSERT_TRUE(h.libs.LoadMapFile(tmp.dir / "lib.map"));
  ASSERT_TRUE(h.compiler.CompileCommandLine({only}, h.unit));
  Elaborator first_elab(h.arena, h.diag, &h.unit);
  auto* first = first_elab.Elaborate("top");
  ASSERT_NE(first, nullptr);
  const LibraryCell* compiled = h.libs.CellInLibrary("rtlLib", "top");
  ASSERT_NE(compiled, nullptr);
  auto compiled_file_id = compiled->loc.file_id;

  CompilationUnit second_unit;
  ASSERT_TRUE(h.compiler.CompileCommandLine({only}, second_unit));
  const LibraryCell* reused = h.libs.CellInLibrary("rtlLib", "top");
  ASSERT_NE(reused, nullptr);
  ASSERT_EQ(reused->loc.file_id, compiled_file_id);

  Elaborator second_elab(h.arena, h.diag, &second_unit);
  auto* second = second_elab.Elaborate("top");
  ASSERT_NE(second, nullptr);
  EXPECT_FALSE(h.diag.HasErrors());
  EXPECT_EQ(first->cu_timescale.unit, TimeUnit::kPs);
  EXPECT_EQ(first->cu_timescale.magnitude, 100);
  EXPECT_EQ(first->cu_timescale.precision, TimeUnit::kFs);
  EXPECT_EQ(first->cu_timescale.prec_magnitude, 10);
  EXPECT_EQ(second->cu_timescale.unit, TimeUnit::kPs);
  EXPECT_EQ(second->cu_timescale.magnitude, 100);
  EXPECT_EQ(second->cu_timescale.precision, TimeUnit::kFs);
  EXPECT_EQ(second->cu_timescale.prec_magnitude, 10);
}

TEST(CompilationUnitScopeAcrossCommandLineFiles,
     UnitVariableDeclaredInALaterFileIsOutOfReach) {
  ScratchDir tmp;
  tmp.Write("lib.map", kLibMap);
  auto top = tmp.Write("src/top.sv",
                       "module top;\n"
                       "  int y;\n"
                       "  initial y = g;\n"
                       "endmodule\n");
  auto unit = tmp.Write("src/unit.sv", "int g;\n");

  CommandLineHarness h;
  CompileCommandLineAndElaborate(h, tmp, {top, unit}, "");
  EXPECT_TRUE(ReportedError(h.diag.Diagnostics(), "'g'", 3, "23.9"));
}
