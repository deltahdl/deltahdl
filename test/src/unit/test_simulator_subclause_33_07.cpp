#include <gtest/gtest.h>

#include <filesystem>
#include <fstream>
#include <iterator>
#include <string>
#include <string_view>
#include <vector>

#include "common/types.h"
#include "elaborator/elaborator.h"
#include "fixture_config_run.h"
#include "fixture_scratch_dir.h"
#include "fixture_simulator.h"
#include "fixture_vpi_run.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/sim_context.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

using namespace delta;

namespace {

constexpr const char* kMapText =
    "library rtlLib top.v;\n"
    "library aLib adder.*;\n"
    "library gateLib\n"
    "    adder.vg;\n";

constexpr const char* kTopSource =
    "module top;\n"
    "  adder a1();\n"
    "  adder a2();\n"
    "  initial $display(\"[t %m %l]\");\n"
    "endmodule\n";

constexpr const char* kAdderSource =
    "module adder;\n"
    "  m f1();\n"
    "  initial begin\n"
    "    $display(\"[l %m %l]\");\n"
    "    $display(\"[L %m %L]\");\n"
    "  end\n"
    "endmodule\n"
    "module m;\n"
    "  initial $display(\"[m %m %l]\");\n"
    "endmodule\n";

constexpr const char* kSelectingConfig =
    "config cfg1;\n"
    "  design rtlLib.top;\n"
    "  default liblist aLib rtlLib;\n"
    "  instance top.a2 liblist gateLib;\n"
    "endconfig\n";

constexpr const char* kPlainConfig =
    "config cfg2;\n"
    "  design rtlLib.top;\n"
    "  default liblist aLib rtlLib;\n"
    "endconfig\n";

bool BuildExampleDesign(ScratchDir& tmp, BoundDesign& design) {
  auto map_path = tmp.Write("lib.map", kMapText);
  if (!design.map.LoadMapFile(map_path)) return false;
  if (!design.Add(tmp, "adder.v", kAdderSource)) return false;
  if (!design.Add(tmp, "adder.vg", kAdderSource)) return false;
  return design.Add(tmp, "top.v", kTopSource);
}

std::string FileContents(const std::filesystem::path& path) {
  std::ifstream ifs(path);
  return std::string((std::istreambuf_iterator<char>(ifs)),
                     std::istreambuf_iterator<char>());
}

TEST(LibraryBindingDisplay, TopInstanceReportsItsDesignStatementBinding) {
  ScratchDir tmp;
  BoundDesign design;
  ASSERT_TRUE(BuildExampleDesign(tmp, design));

  auto out = RunConfiguredDesign(tmp, design, kSelectingConfig, "cfg1");
  ASSERT_FALSE(design.diag.HasErrors());
  EXPECT_TRUE(ReportsLine(out, "[t top rtlLib.top]"));
}

TEST(LibraryBindingDisplay, ChildBoundByTheDefaultClauseReportsThatLibrary) {
  ScratchDir tmp;
  BoundDesign design;
  ASSERT_TRUE(BuildExampleDesign(tmp, design));

  auto out = RunConfiguredDesign(tmp, design, kSelectingConfig, "cfg1");
  ASSERT_FALSE(design.diag.HasErrors());
  EXPECT_TRUE(ReportsLine(out, "[l top.a1 aLib.adder]"));
}

TEST(LibraryBindingDisplay, ChildBoundByAnInstanceClauseReportsThatLibrary) {
  ScratchDir tmp;
  BoundDesign design;
  ASSERT_TRUE(BuildExampleDesign(tmp, design));

  auto out = RunConfiguredDesign(tmp, design, kSelectingConfig, "cfg1");
  ASSERT_FALSE(design.diag.HasErrors());
  EXPECT_TRUE(ReportsLine(out, "[l top.a2 gateLib.adder]"));
}

TEST(LibraryBindingDisplay, WithoutTheClauseThatChildReportsTheDefault) {
  ScratchDir tmp;
  BoundDesign design;
  ASSERT_TRUE(BuildExampleDesign(tmp, design));

  auto out = RunConfiguredDesign(tmp, design, kPlainConfig, "cfg2");
  ASSERT_FALSE(design.diag.HasErrors());
  EXPECT_TRUE(ReportsLine(out, "[l top.a2 aLib.adder]"));
  EXPECT_FALSE(ReportsLine(out, "gateLib"));
}

TEST(LibraryBindingDisplay, UppercaseSpecifierReportsTheSameBinding) {
  ScratchDir tmp;
  BoundDesign design;
  ASSERT_TRUE(BuildExampleDesign(tmp, design));

  auto out = RunConfiguredDesign(tmp, design, kSelectingConfig, "cfg1");
  ASSERT_FALSE(design.diag.HasErrors());
  EXPECT_TRUE(ReportsLine(out, "[L top.a2 gateLib.adder]"));
  EXPECT_TRUE(ReportsLine(out, "[L top.a1 aLib.adder]"));
}

TEST(LibraryBindingDisplay, DescendantsReportTheirOwnBinding) {
  ScratchDir tmp;
  BoundDesign design;
  ASSERT_TRUE(BuildExampleDesign(tmp, design));

  auto out = RunConfiguredDesign(tmp, design, kSelectingConfig, "cfg1");
  ASSERT_FALSE(design.diag.HasErrors());
  EXPECT_TRUE(ReportsLine(out, "[m top.a1.f1 aLib.m]"));
  EXPECT_TRUE(ReportsLine(out, "[m top.a2.f1 gateLib.m]"));
}

TEST(LibraryBindingDisplay, WithNoLibraryMapTheDefaultLibraryIsReported) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  initial $display(\"[%l]\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[work.t]\n");
}

TEST(LibraryBindingDisplay, WriteTaskExpandsTheSpecifierToo) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  initial $write(\"[%l]\\n\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[work.t]\n");
}

TEST(LibraryBindingDisplay, FormattingFunctionCarriesTheBindingIntoAString) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  string s;\n"
      "  initial begin\n"
      "    s = $sformatf(\"[%l]\");\n"
      "    $display(s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[work.t]\n");
}

TEST(LibraryBindingDisplay, FormatIntoVariableTaskExpandsTheSpecifier) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  string s;\n"
      "  initial begin\n"
      "    $sformat(s, \"[%l]\");\n"
      "    $display(s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[work.t]\n");
}

TEST(LibraryBindingDisplay, WriteIntoVariableTaskExpandsTheSpecifier) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  string s;\n"
      "  initial begin\n"
      "    $swrite(s, \"[%l]\");\n"
      "    $display(s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[work.t]\n");
}

TEST(LibraryBindingDisplay, StrobedCommandExpandsTheSpecifier) {
  SimFixture f;
  auto out = RunCapture(
      "module leaf;\n"
      "  initial $strobe(\"[%l]\");\n"
      "endmodule\n"
      "module t;\n"
      "  leaf u();\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[work.leaf]\n");
}

TEST(LibraryBindingDisplay, FunctionCalledFromAStrobedArgumentNamesItsOwn) {
  SimFixture f;
  auto out = RunCapture(
      "module leaf;\n"
      "  function string who(); return $sformatf(\"%l\"); endfunction\n"
      "endmodule\n"
      "module t;\n"
      "  leaf u();\n"
      "  initial $strobe(\"[%s]\", u.who());\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[work.leaf]\n");
}

TEST(LibraryBindingDisplay, ChildStaticInitializerNamesTheChild) {
  SimFixture f;
  auto out = RunCapture(
      "module leaf;\n"
      "  string s = $sformatf(\"[%l]\");\n"
      "  initial $display(s);\n"
      "endmodule\n"
      "module t;\n"
      "  leaf u();\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[work.leaf]\n");
}

TEST(LibraryBindingDisplay, MonitoringCommandExpandsTheSpecifier) {
  SimFixture f;
  auto out = RunCapture(
      "module leaf;\n"
      "  initial $monitor(\"[%l]\");\n"
      "endmodule\n"
      "module t;\n"
      "  leaf u();\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[work.leaf]\n");
}

TEST(LibraryBindingDisplay, SeverityTaskExpandsTheSpecifier) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  initial $info(\"<%l>\");\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportsLine(out, "<work.t>"));
}

TEST(LibraryBindingDisplay, FileOutputTaskExpandsTheSpecifier) {
  ScratchDir tmp;
  auto path = tmp.dir / "binding.log";
  std::string src =
      "module t;\n"
      "  integer fd;\n"
      "  initial begin\n"
      "    fd = $fopen(\"" +
      path.string() +
      "\", \"w\");\n"
      "    $fdisplay(fd, \"[%l]\");\n"
      "    $fclose(fd);\n"
      "  end\n"
      "endmodule\n";
  SimFixture f;
  auto out = RunCapture(src, f);
  EXPECT_EQ(FileContents(path), "[work.t]\n");
  EXPECT_TRUE(out.empty());
}

TEST(LibraryBindingDisplay, ARunTimeFormatStringExpandsTheSpecifier) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  string fmt;\n"
      "  string s;\n"
      "  initial begin\n"
      "    fmt = \"[%l]\";\n"
      "    s = $sformatf(fmt);\n"
      "    $display(s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[work.t]\n");
}

TEST(LibraryBindingDisplay, AFieldWidthBeforeTheLetterIsConsumed) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  initial $display(\"[%0l]\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[work.t]\n");
}

TEST(LibraryBindingDisplay, SpecifierTakesNoArgumentFromTheCall) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  initial $display(\"[%l][%0d]\", 8'd42);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[work.t][42]\n");
}

TEST(LibraryBindingDisplay, AnEscapedPercentLeavesTheLetterLiteral) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  initial $display(\"[%%l]\");\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[%l]\n");
}

TEST(LibraryBindingDisplay, BlockScopesStayOutOfTheReportedBinding) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  initial begin : blk\n"
      "    $display(\"[%m][%l]\");\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[t.blk][work.t]\n");
}

TEST(LibraryBindingDisplay, TaskScopeStaysOutOfTheReportedBinding) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  task show;\n"
      "    $display(\"[%m][%l]\");\n"
      "  endtask\n"
      "  initial show;\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[t.show][work.t]\n");
}

TEST(LibraryBindingDisplay, FunctionScopeStaysOutOfTheReportedBinding) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  function int get;\n"
      "    $display(\"[%m][%l]\");\n"
      "    return 1;\n"
      "  endfunction\n"
      "  int y;\n"
      "  initial y = get();\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[t.get][work.t]\n");
}

TEST(LibraryBindingDisplay, AGenerateBlockDoesNotPerturbTheBinding) {
  SimFixture f;
  auto out = RunCapture(
      "module t;\n"
      "  generate\n"
      "    for (genvar i = 0; i < 1; i = i + 1) begin : g\n"
      "      initial $display(\"[%l]\");\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[work.t]\n");
}

TEST(LibraryBindingDisplay, AnInterfaceInstanceReportsItsOwnBinding) {
  SimFixture f;
  auto out = RunCapture(
      "interface bus;\n"
      "  initial $display(\"[%l]\");\n"
      "endinterface\n"
      "module t;\n"
      "  bus u();\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[work.bus]\n");
}

TEST(LibraryBindingDisplay, AProgramInstanceReportsItsOwnBinding) {
  SimFixture f;
  auto out = RunCapture(
      "program pgm;\n"
      "  initial $display(\"[%l]\");\n"
      "endprogram\n"
      "module t;\n"
      "  pgm u();\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "[work.pgm]\n");
}

TEST(LibraryBindingDisplay, AnUnrecordedBindingStillSubstitutesAToken) {
  SimFixture f;
  std::vector<Logic4Vec> vals;
  auto out = FormatDisplay("x%ly", vals, {.ctx = &f.ctx, .loc = {}});
  EXPECT_EQ(out.front(), 'x');
  EXPECT_EQ(out.back(), 'y');
  EXPECT_NE(out.find('.'), std::string::npos);
  EXPECT_GT(out.size(), 2u);
}

TEST(LibraryBindingDisplay, VpiBindingPropertyConstantsAreDistinct) {
  EXPECT_NE(kVpiLibrary, kVpiCell);
  EXPECT_NE(kVpiLibrary, kVpiConfig);
  EXPECT_NE(kVpiCell, kVpiConfig);
  EXPECT_NE(kVpiLibrary, kVpiName);
  EXPECT_NE(kVpiCell, kVpiName);
  EXPECT_NE(kVpiConfig, kVpiName);
}

TEST(LibraryBindingDisplay, VpiGetStrReturnsLibraryNameForModule) {
  VpiContext ctx;
  VpiHandle mod = ctx.CreateModule("adder", "top.a2");
  mod->library_name = "gateLib";
  const char* lib = ctx.GetStr(kVpiLibrary, mod);
  ASSERT_NE(lib, nullptr);
  EXPECT_STREQ(lib, "gateLib");
}

TEST(LibraryBindingDisplay, VpiGetStrReturnsCellNameForModule) {
  VpiContext ctx;
  VpiHandle mod = ctx.CreateModule("adder", "top.a2");
  mod->cell_name = "adder";
  const char* cell = ctx.GetStr(kVpiCell, mod);
  ASSERT_NE(cell, nullptr);
  EXPECT_STREQ(cell, "adder");
}

TEST(LibraryBindingDisplay, VpiCellFallsBackToTheDefinitionName) {
  VpiContext ctx;
  VpiHandle mod = ctx.CreateModule("a2", "top.a2");
  mod->def_name = "adder";
  const char* cell = ctx.GetStr(kVpiCell, mod);
  ASSERT_NE(cell, nullptr);
  EXPECT_STREQ(cell, "adder");
}

TEST(LibraryBindingDisplay, VpiGetStrReturnsConfigNameForModule) {
  VpiContext ctx;
  VpiHandle mod = ctx.CreateModule("adder", "top.a2");
  mod->config_name = "work.cfg5";
  const char* cfg = ctx.GetStr(kVpiConfig, mod);
  ASSERT_NE(cfg, nullptr);
  EXPECT_STREQ(cfg, "work.cfg5");
}

TEST(LibraryBindingDisplay, VpiBindingPropertiesReturnStringWhenUnset) {
  VpiContext ctx;
  VpiHandle mod = ctx.CreateModule("m", "m");
  EXPECT_NE(ctx.GetStr(kVpiLibrary, mod), nullptr);
  EXPECT_NE(ctx.GetStr(kVpiConfig, mod), nullptr);
}

TEST(LibraryBindingDisplay, VpiBindingPropertiesAreModuleScoped) {
  VpiContext ctx;
  VpiHandle mod = ctx.CreateModule("top", "top");
  VpiHandle port = ctx.CreatePort("p", kVpiInput, mod);
  EXPECT_EQ(ctx.GetStr(kVpiLibrary, port), nullptr);
  EXPECT_EQ(ctx.GetStr(kVpiCell, port), nullptr);
  EXPECT_EQ(ctx.GetStr(kVpiConfig, port), nullptr);
}

TEST(LibraryBindingDisplay, VpiBindingPropertiesAreNullSafe) {
  VpiContext ctx;
  EXPECT_EQ(ctx.GetStr(kVpiLibrary, nullptr), nullptr);
  EXPECT_EQ(ctx.GetStr(kVpiCell, nullptr), nullptr);
  EXPECT_EQ(ctx.GetStr(kVpiConfig, nullptr), nullptr);
}

TEST(LibraryBindingDisplay, VpiGetStrCApiReadsBindingProperties) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);
  VpiHandle mod = ctx.CreateModule("adder", "top.a1");
  mod->library_name = "rtlLib";
  mod->cell_name = "adder";
  mod->config_name = "work.cfg1";
  EXPECT_STREQ(vpi_get_str(vpiLibrary, VpiHandleOf(mod)), "rtlLib");
  EXPECT_STREQ(vpi_get_str(vpiCell, VpiHandleOf(mod)), "adder");
  EXPECT_STREQ(vpi_get_str(vpiConfig, VpiHandleOf(mod)), "work.cfg1");
  SetGlobalVpiContext(nullptr);
}

class LibraryBindingVpiRun : public VpiDesignRun {
 protected:
  void RunUnderConfig(const std::string& src) {
    auto fid = f_.mgr.AddFile("<test>", src);
    Lexer lexer(f_.mgr.FileContent(fid), fid, f_.diag);
    Parser parser(lexer, f_.arena, f_.diag);
    auto* cu = parser.Parse();
    ASSERT_NE(cu, nullptr);
    ASSERT_FALSE(cu->configs.empty());
    Elaborator elab(f_.arena, f_.diag, cu);
    RtlirDesign* design = elab.Elaborate(cu->configs[0]);
    ASSERT_NE(design, nullptr);
    ASSERT_FALSE(f_.diag.HasErrors());
    LowerAndRun(design, f_);
  }
};

TEST_F(LibraryBindingVpiRun, InstanceReportsItsLibraryAndCell) {
  Run("module adder; endmodule\n"
      "module top; adder a2(); endmodule\n");
  vpiHandle a2 = By("top.a2");
  ASSERT_NE(a2, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiLibrary, a2), "work");
  EXPECT_STREQ(vpi_get_str(vpiCell, a2), "adder");
  EXPECT_STREQ(vpi_get_str(vpiConfig, a2), "");
}

TEST_F(LibraryBindingVpiRun, InstanceBoundUnderAConfigReportsTheConfig) {
  RunUnderConfig(
      "module adder; endmodule\n"
      "module top; adder a1(); endmodule\n"
      "config cfg1; design work.top; endconfig\n");
  vpiHandle a1 = By("top.a1");
  ASSERT_NE(a1, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiConfig, a1), "work.cfg1");
}

}  // namespace
