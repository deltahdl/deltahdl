#include <gtest/gtest.h>

#include <filesystem>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaborator/rtlir.h"
#include "elaborator/separate_compilation_bind.h"
#include "fixture_scratch_dir.h"
#include "helpers_reported_error.h"
#include "parser/precompiled_library.h"

using namespace delta;
namespace fs = std::filesystem;

namespace {

struct BindHarness {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  SeparateCompilationBinder binder{mgr, arena, diag};
};

void Precompile(const std::string& source, const std::string& library,
                const fs::path& path) {
  ASSERT_TRUE(PrecompiledLibrary::Save(source, library, path));
}

constexpr const char* kLeaf =
    "module leaf;\n"
    "endmodule\n";
constexpr const char* kMid =
    "module mid;\n"
    "  leaf l();\n"
    "endmodule\n";
constexpr const char* kTop =
    "module top;\n"
    "  mid m();\n"
    "endmodule\n";

constexpr const char* kOther =
    "module other;\n"
    "  leaf l();\n"
    "endmodule\n";
constexpr const char* kSpare =
    "module spare;\n"
    "endmodule\n";

constexpr const char* kTwice =
    "module twice;\n"
    "  leaf l1();\n"
    "  leaf l2();\n"
    "endmodule\n";

constexpr const char* kAdder =
    "module adder;\n"
    "endmodule\n";
constexpr const char* kAdderTop =
    "module adder_top;\n"
    "  adder a1();\n"
    "endmodule\n";

constexpr const char* kTwoMissing =
    "module two_missing;\n"
    "  gone_a a1();\n"
    "  gone_b b1();\n"
    "endmodule\n";

constexpr const char* kMissingBelowAnother =
    "module missing_below_another;\n"
    "\n"
    "  leaf l();\n"
    "  gone g();\n"
    "endmodule\n";

constexpr const char* kGenerateTop =
    "module generate_top;\n"
    "  if (1) begin : g\n"
    "    leaf l();\n"
    "  end\n"
    "endmodule\n";

constexpr const char* kDeclaresItsChild =
    "module declares_its_child;\n"
    "  module inner;\n"
    "  endmodule\n"
    "  inner i();\n"
    "endmodule\n";

constexpr const char* kInterface =
    "interface ifc;\n"
    "endinterface\n";
constexpr const char* kHoldsInterface =
    "module holds_interface;\n"
    "  ifc i();\n"
    "endmodule\n";

constexpr const char* kPrimitive =
    "primitive ubuf(output o, input i);\n"
    "  table\n"
    "    0 : 0;\n"
    "    1 : 1;\n"
    "  endtable\n"
    "endprimitive\n";
constexpr const char* kHoldsPrimitive =
    "module holds_primitive;\n"
    "  wire y;\n"
    "  wire a;\n"
    "  ubuf u1(y, a);\n"
    "endmodule\n";

TEST(SeparateCompilationBinding, TopIsBoundFromNothingButItsName) {
  ScratchDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  Precompile(kLeaf, "rtlLib", path);
  Precompile(kMid, "rtlLib", path);
  Precompile(kTop, "rtlLib", path);

  BindHarness h;
  ASSERT_TRUE(h.binder.LoadLibrary(path));
  auto* design = h.binder.Bind({"top"});
  ASSERT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "top");
}

TEST(SeparateCompilationBinding, TopNamedAsLibCellIsBoundFromThatLibrary) {
  ScratchDir tmp;
  auto rtl = tmp.dir / "rtlLib.dpl";
  auto gate = tmp.dir / "gateLib.dpl";
  Precompile("module adder;\nendmodule\n", "rtlLib", rtl);
  Precompile("module adder;\nendmodule\n", "gateLib", gate);

  BindHarness h;
  ASSERT_TRUE(h.binder.LoadLibrary(rtl));
  ASSERT_TRUE(h.binder.LoadLibrary(gate));
  auto* design = h.binder.Bind({"gateLib.adder"});
  ASSERT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->library, "gateLib");
}

TEST(SeparateCompilationBinding, ConfigNamedAsLibCellIsTakenFromThatLibrary) {
  ScratchDir tmp;
  auto rtl = tmp.dir / "rtlLib.dpl";
  auto gate = tmp.dir / "gateLib.dpl";
  Precompile(
      "module top;\nendmodule\n"
      "config cfg;\n  design rtlLib.top;\nendconfig\n",
      "rtlLib", rtl);
  Precompile(
      "module other;\nendmodule\n"
      "config cfg;\n  design gateLib.other;\nendconfig\n",
      "gateLib", gate);

  BindHarness h;
  ASSERT_TRUE(h.binder.LoadLibrary(rtl));
  ASSERT_TRUE(h.binder.LoadLibrary(gate));
  auto* design = h.binder.BindConfig("gateLib.cfg");
  ASSERT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "other");
}

TEST(SeparateCompilationBinding, EveryNamedTopRootsTheBoundDesign) {
  ScratchDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  Precompile(kLeaf, "rtlLib", path);
  Precompile(kMid, "rtlLib", path);
  Precompile(kTop, "rtlLib", path);
  Precompile(kOther, "rtlLib", path);

  BindHarness h;
  ASSERT_TRUE(h.binder.LoadLibrary(path));
  auto* design = h.binder.Bind({"top", "other"});
  ASSERT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 2u);
  EXPECT_EQ(design->top_modules[0]->name, "top");
  EXPECT_EQ(design->top_modules[1]->name, "other");
}

TEST(SeparateCompilationBinding, ATopNamedTwiceRootsOneHierarchy) {
  ScratchDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  Precompile(kLeaf, "rtlLib", path);
  Precompile(kMid, "rtlLib", path);
  Precompile(kTop, "rtlLib", path);

  BindHarness h;
  ASSERT_TRUE(h.binder.LoadLibrary(path));
  auto* design = h.binder.Bind({"top", "top"});
  ASSERT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "top");
}

TEST(SeparateCompilationBinding, NamingNoTopAtAllIsReported) {
  ScratchDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  Precompile(kLeaf, "rtlLib", path);
  Precompile(kMid, "rtlLib", path);
  Precompile(kTop, "rtlLib", path);

  BindHarness h;
  ASSERT_TRUE(h.binder.LoadLibrary(path));
  EXPECT_EQ(h.binder.Bind({}), nullptr);
  EXPECT_TRUE(ReportedError(h.diag.Diagnostics(),
                            "no top-level module was named to elaborate", 0,
                            ""));
}

TEST(SeparateCompilationBinding, SubinstancesComeOutOfThePrecompiledForm) {
  ScratchDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  Precompile(kLeaf, "rtlLib", path);
  Precompile(kMid, "rtlLib", path);
  Precompile(kTop, "rtlLib", path);

  BindHarness h;
  ASSERT_TRUE(h.binder.LoadLibrary(path));
  auto* design = h.binder.Bind({"top"});
  ASSERT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(design->all_modules.size(), 3u);
  EXPECT_TRUE(design->all_modules.contains("top"));
  EXPECT_TRUE(design->all_modules.contains("mid"));
  EXPECT_TRUE(design->all_modules.contains("leaf"));
}

TEST(SeparateCompilationBinding, EachInstanceMetIsBoundToItsPrecompiledCell) {
  ScratchDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  Precompile(kLeaf, "rtlLib", path);
  Precompile(kTwice, "rtlLib", path);

  BindHarness h;
  ASSERT_TRUE(h.binder.LoadLibrary(path));
  auto* design = h.binder.Bind({"twice"});
  ASSERT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  ASSERT_EQ(design->top_modules[0]->children.size(), 2u);
  EXPECT_EQ(design->top_modules[0]->children[0].inst_name, "l1");
  EXPECT_NE(design->top_modules[0]->children[0].resolved, nullptr);
  EXPECT_EQ(design->top_modules[0]->children[1].inst_name, "l2");
  EXPECT_NE(design->top_modules[0]->children[1].resolved, nullptr);
}

TEST(SeparateCompilationBinding, CellInAGenerateIsBoundAsItIsLocated) {
  ScratchDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  Precompile(kLeaf, "rtlLib", path);
  Precompile(kGenerateTop, "rtlLib", path);

  BindHarness h;
  ASSERT_TRUE(h.binder.LoadLibrary(path));
  auto* design = h.binder.Bind({"generate_top"});
  ASSERT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(design->all_modules.contains("leaf"));
}

TEST(SeparateCompilationBinding, CellNoNamedTopReachesIsNotBound) {
  ScratchDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  Precompile(kLeaf, "rtlLib", path);
  Precompile(kMid, "rtlLib", path);
  Precompile(kTop, "rtlLib", path);
  Precompile(kSpare, "rtlLib", path);

  BindHarness h;
  ASSERT_TRUE(h.binder.LoadLibrary(path));
  auto* design = h.binder.Bind({"top"});
  ASSERT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_FALSE(design->all_modules.contains("spare"));
}

TEST(SeparateCompilationBinding, DescentCrossesFromOneCompiledFormToAnother) {
  ScratchDir tmp;
  auto rtl = tmp.dir / "rtlLib.dpl";
  auto gate = tmp.dir / "gateLib.dpl";
  Precompile(kAdder, "gateLib", gate);
  Precompile(kAdderTop, "rtlLib", rtl);

  BindHarness h;
  ASSERT_TRUE(h.binder.LoadLibrary(rtl));
  ASSERT_TRUE(h.binder.LoadLibrary(gate));
  auto* design = h.binder.Bind({"adder_top"});
  ASSERT_FALSE(h.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  ASSERT_TRUE(design->all_modules.contains("adder"));
  EXPECT_EQ(design->all_modules.at("adder")->library, "gateLib");
}

TEST(SeparateCompilationBinding, CellBelowATopNeverCompiledStopsTheBind) {
  ScratchDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  Precompile(kMid, "rtlLib", path);
  Precompile(kTop, "rtlLib", path);

  BindHarness h;
  ASSERT_TRUE(h.binder.LoadLibrary(path));
  EXPECT_EQ(h.binder.Bind({"top"}), nullptr);
  EXPECT_TRUE(ReportedError(h.diag.Diagnostics(),
                            "cell 'leaf' was not precompiled", 2, "33.5.3"));
}

TEST(SeparateCompilationBinding, TwoCellsMissingUnderOneTopAreBothNamed) {
  ScratchDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  Precompile(kTwoMissing, "rtlLib", path);

  BindHarness h;
  ASSERT_TRUE(h.binder.LoadLibrary(path));
  EXPECT_EQ(h.binder.Bind({"two_missing"}), nullptr);
  ASSERT_EQ(h.binder.CellsNotPrecompiled().size(), 2u);
  EXPECT_EQ(h.binder.CellsNotPrecompiled()[0].name, "gone_a");
  EXPECT_EQ(h.binder.CellsNotPrecompiled()[1].name, "gone_b");
}

TEST(SeparateCompilationBinding, CellInAGenerateIsCheckedBeforeBinding) {
  ScratchDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  Precompile(kGenerateTop, "rtlLib", path);

  BindHarness h;
  ASSERT_TRUE(h.binder.LoadLibrary(path));
  EXPECT_EQ(h.binder.Bind({"generate_top"}), nullptr);
  ASSERT_EQ(h.binder.CellsNotPrecompiled().size(), 1u);
  EXPECT_EQ(h.binder.CellsNotPrecompiled()[0].name, "leaf");
}

TEST(SeparateCompilationBinding, CellDeclaredInsideItsParentNeedsNoLibrary) {
  ScratchDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  Precompile(kDeclaresItsChild, "rtlLib", path);

  BindHarness h;
  ASSERT_TRUE(h.binder.LoadLibrary(path));
  h.binder.Bind({"declares_its_child"});
  EXPECT_TRUE(h.binder.CellsNotPrecompiled().empty());
}

TEST(SeparateCompilationBinding, InterfaceHeldInALibraryCountsAsPrecompiled) {
  ScratchDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  Precompile(kInterface, "rtlLib", path);
  Precompile(kHoldsInterface, "rtlLib", path);

  BindHarness h;
  ASSERT_TRUE(h.binder.LoadLibrary(path));
  h.binder.Bind({"holds_interface"});
  EXPECT_TRUE(h.binder.CellsNotPrecompiled().empty());
}

TEST(SeparateCompilationBinding, TopNamedButNeverCompiledIsReportedByName) {
  ScratchDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  Precompile(kLeaf, "rtlLib", path);

  BindHarness h;
  ASSERT_TRUE(h.binder.LoadLibrary(path));
  EXPECT_EQ(h.binder.Bind({"top"}), nullptr);
  ASSERT_EQ(h.binder.CellsNotPrecompiled().size(), 1u);
  EXPECT_EQ(h.binder.CellsNotPrecompiled()[0].name, "top");
}

TEST(SeparateCompilationBinding, PrimitiveHeldInALibraryCountsAsPrecompiled) {
  ScratchDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  Precompile(kPrimitive, "rtlLib", path);
  Precompile(kHoldsPrimitive, "rtlLib", path);

  BindHarness h;
  ASSERT_TRUE(h.binder.LoadLibrary(path));
  h.binder.Bind({"holds_primitive"});
  EXPECT_TRUE(h.binder.CellsNotPrecompiled().empty());
}

TEST(SeparateCompilationBinding, OneCompiledFormServesBindAfterBind) {
  ScratchDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  Precompile(kLeaf, "rtlLib", path);
  Precompile(kMid, "rtlLib", path);
  Precompile(kTop, "rtlLib", path);

  BindHarness first;
  ASSERT_TRUE(first.binder.LoadLibrary(path));
  ASSERT_NE(first.binder.Bind({"top"}), nullptr);

  BindHarness second;
  ASSERT_TRUE(second.binder.LoadLibrary(path));
  auto* design = second.binder.Bind({"top"});
  ASSERT_FALSE(second.diag.HasErrors());
  ASSERT_NE(design, nullptr);
  EXPECT_EQ(design->all_modules.size(), 3u);
}

TEST(SeparateCompilationBinding, LoadingAFileThatIsNoCompiledFormIsReported) {
  ScratchDir tmp;
  auto path = tmp.Write("rtlLib.dpl", "this file was written by someone else");

  BindHarness h;
  EXPECT_FALSE(h.binder.LoadLibrary(path));
  EXPECT_TRUE(
      ReportedError(h.diag.Diagnostics(), "no cells read from library", 0, ""));
}

TEST(SeparateCompilationBinding, CellNotPrecompiledNames33_5_3) {
  ScratchDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  Precompile(kTwoMissing, "rtlLib", path);

  BindHarness h;
  ASSERT_TRUE(h.binder.LoadLibrary(path));
  EXPECT_EQ(h.binder.Bind({"two_missing"}), nullptr);
  EXPECT_TRUE(ReportedError(h.diag.Diagnostics(),
                            "cell 'gone_a' was not precompiled", 2, "33.5.3"));
}

TEST(SeparateCompilationBinding, CellNotPrecompiledStandsAtItsInstantiation) {
  ScratchDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  Precompile(kLeaf, "rtlLib", path);
  Precompile(kMissingBelowAnother, "rtlLib", path);

  BindHarness h;
  ASSERT_TRUE(h.binder.LoadLibrary(path));
  EXPECT_EQ(h.binder.Bind({"missing_below_another"}), nullptr);
  EXPECT_TRUE(ReportedError(h.diag.Diagnostics(),
                            "cell 'gone' was not precompiled", 4, "33.5.3"));
}

constexpr const char* kLeafBesideACuTypedef =
    "typedef logic [7:0] byte_t;\n"
    "module leaf;\n"
    "endmodule\n";

TEST(SeparateCompilationBinding,
     CompilationUnitDeclarationDoesNotCrossAPrecompiledRecord) {
  ScratchDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  Precompile(kLeafBesideACuTypedef, "rtlLib", path);

  BindHarness h;
  CompilationUnit target;
  ASSERT_TRUE(PrecompiledLibrary::Load(path, target, h.mgr, h.arena, h.diag));
  ASSERT_EQ(target.modules.size(), 1u);
  EXPECT_EQ(target.modules[0]->name, "leaf");
  EXPECT_TRUE(target.cu_items.empty());
}

constexpr const char* kAdderUser =
    "module user;\n"
    "  adder a1();\n"
    "endmodule\n";

std::string BoundAdderLibrary(const std::vector<std::string>& order) {
  ScratchDir tmp;
  auto rtl = tmp.dir / "rtl.dpl";
  auto gate = tmp.dir / "gate.dpl";
  Precompile(kAdderUser, "rtlLib", rtl);
  Precompile(kAdder, "rtlLib", rtl);
  Precompile(kAdder, "gateLib", gate);

  BindHarness h;
  EXPECT_TRUE(h.binder.LoadLibrary(rtl));
  EXPECT_TRUE(h.binder.LoadLibrary(gate));
  h.binder.SetLibrarySearchOrder(order);
  auto* design = h.binder.Bind({"user"});
  EXPECT_FALSE(h.diag.HasErrors());
  if (design == nullptr || design->top_modules.size() != 1 ||
      design->top_modules[0]->children.size() != 1 ||
      design->top_modules[0]->children[0].resolved == nullptr) {
    return "";
  }
  return std::string(design->top_modules[0]->children[0].resolved->library);
}

TEST(SeparateCompilationBinding, SearchOrderNamingGateLibFirstBindsItsAdder) {
  EXPECT_EQ(BoundAdderLibrary({"gateLib", "rtlLib"}), "gateLib");
}

TEST(SeparateCompilationBinding, SearchOrderNamingRtlLibFirstBindsItsAdder) {
  EXPECT_EQ(BoundAdderLibrary({"rtlLib", "gateLib"}), "rtlLib");
}

bool BindsWithItsCellPrecompiled(const char* cell, const char* holder,
                                 const char* top, std::string_view bound) {
  ScratchDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  Precompile(cell, "rtlLib", path);
  Precompile(holder, "rtlLib", path);
  BindHarness h;
  EXPECT_TRUE(h.binder.LoadLibrary(path));
  auto* design = h.binder.Bind({top});
  if (design == nullptr || h.diag.HasErrors()) return false;
  if (!h.binder.CellsNotPrecompiled().empty()) return false;
  return bound.empty() || design->all_modules.contains(bound);
}

std::vector<Diagnostic> BindWithItsCellMissing(const char* holder,
                                               const char* top) {
  ScratchDir tmp;
  auto path = tmp.dir / "rtlLib.dpl";
  Precompile(holder, "rtlLib", path);
  BindHarness h;
  EXPECT_TRUE(h.binder.LoadLibrary(path));
  EXPECT_EQ(h.binder.Bind({top}), nullptr);
  return h.diag.Diagnostics();
}

TEST(SeparateCompilationBinding, InterfaceNeverCompiledStopsTheBind) {
  EXPECT_TRUE(
      ReportedError(BindWithItsCellMissing(kHoldsInterface, "holds_interface"),
                    "cell 'ifc' was not precompiled", 2, "33.5.3"));
}

TEST(SeparateCompilationBinding, PrimitiveNeverCompiledStopsTheBind) {
  EXPECT_TRUE(
      ReportedError(BindWithItsCellMissing(kHoldsPrimitive, "holds_primitive"),
                    "cell 'ubuf' was not precompiled", 4, "33.5.3"));
}

constexpr const char* kProgram =
    "program pgm;\n"
    "endprogram\n";
constexpr const char* kHoldsProgram =
    "module holds_program;\n"
    "  pgm p();\n"
    "endmodule\n";

TEST(SeparateCompilationBinding, ProgramNeverCompiledStopsTheBind) {
  EXPECT_TRUE(
      ReportedError(BindWithItsCellMissing(kHoldsProgram, "holds_program"),
                    "cell 'pgm' was not precompiled", 2, "33.5.3"));
}

TEST(SeparateCompilationBinding, ProgramHeldInALibraryCountsAsPrecompiled) {
  EXPECT_TRUE(BindsWithItsCellPrecompiled(kProgram, kHoldsProgram,
                                          "holds_program", ""));
}

constexpr const char* kChecker =
    "checker chk;\n"
    "endchecker\n";
constexpr const char* kHoldsChecker =
    "module holds_checker;\n"
    "  chk c();\n"
    "endmodule\n";

TEST(SeparateCompilationBinding, CheckerNeverCompiledStopsTheBind) {
  EXPECT_TRUE(
      ReportedError(BindWithItsCellMissing(kHoldsChecker, "holds_checker"),
                    "cell 'chk' was not precompiled", 2, "33.5.3"));
}

TEST(SeparateCompilationBinding, CheckerHeldInALibraryCountsAsPrecompiled) {
  EXPECT_TRUE(BindsWithItsCellPrecompiled(kChecker, kHoldsChecker,
                                          "holds_checker", ""));
}

constexpr const char* kLoopGenerateTop =
    "module loop_top;\n"
    "  for (genvar i = 0; i < 2; i++) begin : g\n"
    "    leaf l();\n"
    "  end\n"
    "endmodule\n";

TEST(SeparateCompilationBinding, CellInALoopGenerateIsBound) {
  EXPECT_TRUE(
      BindsWithItsCellPrecompiled(kLeaf, kLoopGenerateTop, "loop_top", "leaf"));
}

TEST(SeparateCompilationBinding, CellInALoopGenerateIsCheckedBeforeBinding) {
  EXPECT_TRUE(
      ReportedError(BindWithItsCellMissing(kLoopGenerateTop, "loop_top"),
                    "cell 'leaf' was not precompiled", 3, "33.5.3"));
}

constexpr const char* kCaseGenerateTop =
    "module case_top;\n"
    "  case (1)\n"
    "    1: begin : g\n"
    "      leaf l();\n"
    "    end\n"
    "  endcase\n"
    "endmodule\n";

TEST(SeparateCompilationBinding, CellInACaseGenerateIsBound) {
  EXPECT_TRUE(
      BindsWithItsCellPrecompiled(kLeaf, kCaseGenerateTop, "case_top", "leaf"));
}

TEST(SeparateCompilationBinding, CellInACaseGenerateIsCheckedBeforeBinding) {
  EXPECT_TRUE(
      ReportedError(BindWithItsCellMissing(kCaseGenerateTop, "case_top"),
                    "cell 'leaf' was not precompiled", 4, "33.5.3"));
}

constexpr const char* kNestedGenerateTop =
    "module nested_top;\n"
    "  if (1) begin : outer\n"
    "    if (1) begin : inner\n"
    "      leaf l();\n"
    "    end\n"
    "  end\n"
    "endmodule\n";

TEST(SeparateCompilationBinding, CellInANestedGenerateIsBound) {
  EXPECT_TRUE(BindsWithItsCellPrecompiled(kLeaf, kNestedGenerateTop,
                                          "nested_top", "leaf"));
}

TEST(SeparateCompilationBinding, CellInANestedGenerateIsCheckedBeforeBinding) {
  EXPECT_TRUE(
      ReportedError(BindWithItsCellMissing(kNestedGenerateTop, "nested_top"),
                    "cell 'leaf' was not precompiled", 4, "33.5.3"));
}

}  // namespace
