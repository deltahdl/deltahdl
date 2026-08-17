#include <filesystem>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "fixture_scratch_dir.h"
#include "helpers_rtlir_lookup.h"
#include "parser/ast.h"
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

// The declared widths are what say WIDTH reached both modules. A bound that
// folds to nothing is not reported: EvalRangeWidth in
// src/elaborator/type_eval.cpp answers 0 and the declaration falls through to
// one bit, so an assertion that elaboration succeeded holds whether WIDTH was
// visible or not.
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

// §3.12.1 puts a compilation-unit declaration in scope for every design element
// in the unit, and the two modules here are siblings rather than a module and
// its instance: neither is elaborated inside the other, so WIDTH has to survive
// the first module's elaboration to size the second one's declaration.
//
// Elaborator::ElaborateModule takes back what a module adds to the elaborator's
// typedef and parameter maps before the next module is elaborated, which is
// what keeps one module's package import out of the next (§26.3). This states
// the other half of that: what the compilation unit itself declared is written
// before any module is elaborated and is still there afterwards.
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
  // §3.12.1: the whole purpose of the $unit:: prefix is unambiguous access to
  // the outermost (compilation-unit-scope) declaration. Here a module-local
  // localparam K shadows a compilation-unit localparam K of a different value.
  // The bare reference must see the local (width 3) while the $unit::K
  // reference must reach past the shadow to the compilation-unit value
  // (width 8).
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
  // §3.12.1: the outermost declaration reached by $unit:: may be declared with
  // the `parameter` keyword rather than `localparam`. At compilation-unit scope
  // both name a constant, so a $unit:: reference must still bypass a same-named
  // module-local parameter (here local 3) and resolve to the outermost value 8.
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
  // §3.12.1: the $unit:: disambiguation applies wherever a constant expression
  // is evaluated, not only in a packed dimension. Here a module-local
  // localparam M is initialized from $unit::K while a same-named local K
  // shadows the compilation-unit K. M must be computed from the outermost K
  // (8 + 1 == 9), giving a 9-bit vector, not from the local K (which would be
  // 4 bits).
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

// §3.12.1 case a): "all files on a given compilation command line make a single
// compilation unit (in which case the declarations within those files are
// accessible following normal visibility rules throughout the entire set of
// files)". Every test above hands the elaborator one source description, which
// cannot tell that model from case b) -- "each file is a separate compilation
// unit" -- because with one file the two agree. These drive a command line of
// two files through SinglePassCompiler, which is the path that implements case
// a), and ask what a declaration written outside every design element in one
// file is worth in the other.
//
// The declaration kinds are the ones §3.12.1 names: "although the
// compilation-unit scope is not a package, it can contain any item that can be
// defined within a package (see 26.2) and bind constructs as well (see 23.11)".

// The infrastructure one command line is compiled and elaborated against.
struct CommandLineHarness {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  LibraryMap libs;
  CompilationUnit unit;
  SinglePassCompiler compiler{libs, mgr, arena, diag};
};

// The library map every test here compiles against. A compilation-unit
// declaration belongs to no library, so the map claims the sources only so that
// the design elements among them have somewhere to go.
constexpr const char* kLibMap = "library rtlLib src/*.sv;\n";

// Compiles `files` as one command line into `h` and elaborates the compilation
// unit that produced, returning the design or nullptr. The design outlives the
// elaborator because it is arena-allocated, and the arena is the harness's.
RtlirDesign* CompileCommandLineAndElaborate(CommandLineHarness& h,
                                            const ScratchDir& tmp,
                                            const std::vector<fs::path>& files,
                                            std::string_view top) {
  if (!h.libs.LoadMapFile(tmp.dir / "lib.map")) return nullptr;
  if (!h.compiler.CompileCommandLine(files, h.unit)) return nullptr;
  Elaborator elab(h.arena, h.diag, &h.unit);
  return elab.Elaborate(top);
}

// The module `top` of a design that came out as exactly one top module, or
// nullptr. Both typedef cases and the class case read the compilation-unit
// scope through it.
const RtlirModule* SoleTopModule(RtlirDesign* design) {
  if (design == nullptr || design->top_modules.size() != 1u) return nullptr;
  return design->top_modules[0];
}

}  // namespace

TEST(CompilationUnitScopeAcrossCommandLineFiles,
     TypedefDeclaredInOneFileIsVisibleInAnother) {
  // The typedef is in the file compiled first and the use is in the file
  // compiled second, so this is the visibility §3.12.1 case a) grants across
  // the set of files.
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
  // One file declares the typedef and uses it, so no visibility crosses a file
  // boundary at all. This separates a merge that drops the declaration from one
  // that merely orders the command line's files wrongly: the unit the compiler
  // builds is the only one the elaborator reads, so a declaration left behind
  // is lost to its own file too.
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
  // A class declared outside every design element is an item §26.2 allows in a
  // package, so §3.12.1 puts it in the compilation-unit scope. The parser keeps
  // it in CompilationUnit::classes rather than in cu_items, which is why this
  // case is here beside the typedef ones rather than folded into them.
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
  // §18.5.1 has an external constraint block complete the prototype of the
  // class it names, and §3.12.1 is what puts the two in one scope when they are
  // written in two files on one command line. The parser keeps the block in
  // CompilationUnit::external_constraints and the class in
  // CompilationUnit::classes, so this case turns on a different pair of lists
  // from the ones above.
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
  // §3.12.1 names bind constructs alongside the package items: the
  // compilation-unit scope "can contain any item that can be defined within a
  // package (see 26.2) and bind constructs as well (see 23.11)". The bind is
  // written in one file and its target `cpu` is declared in another, so this is
  // the same visibility the typedef cases ask about. It is here because losing
  // a bind changes the design rather than only a diagnostic: the bound instance
  // is simply absent, and nothing is reported about it.
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
