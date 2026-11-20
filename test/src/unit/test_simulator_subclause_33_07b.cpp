#include <gtest/gtest.h>

#include <string>
#include <string_view>

#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_config_run.h"
#include "fixture_scratch_dir.h"
#include "fixture_simulator.h"
#include "fixture_vpi_run.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "simulator/vpi_user.h"

using namespace delta;

namespace {

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

  static std::string StrOf(int property, const std::string& path) {
    vpiHandle obj = By(path);
    if (obj == nullptr) return "<no instance>";
    const char* text = vpi_get_str(property, obj);
    return text == nullptr ? "<null>" : text;
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

TEST_F(LibraryBindingVpiRun,
       DISABLED_TopInstanceReportsTheConfigOfItsDesignStatement) {
  RunUnderConfig(
      "module adder; endmodule\n"
      "module top; adder a1(); endmodule\n"
      "config cfg1; design work.top; endconfig\n");
  EXPECT_EQ(StrOf(vpiConfig, "top"), "work.cfg1");
}

TEST_F(LibraryBindingVpiRun, UseClauseBindingReportsTheCellItNames) {
  RunUnderConfig(
      "module adder; endmodule\n"
      "module fast; endmodule\n"
      "module top; adder a2(); endmodule\n"
      "config cfg1;\n"
      "  design work.top;\n"
      "  instance top.a2 use work.fast;\n"
      "endconfig\n");
  EXPECT_EQ(StrOf(vpiCell, "top.a2"), "fast");
  EXPECT_EQ(StrOf(vpiLibrary, "top.a2"), "work");
}

TEST_F(LibraryBindingVpiRun, DelegatedSubtreeReportsTheNestedConfig) {
  RunUnderConfig(
      "module m; endmodule\n"
      "module adder; m f1(); endmodule\n"
      "module top; adder a1(); adder a2(); endmodule\n"
      "config cfg6;\n"
      "  design work.top;\n"
      "  instance top.a2 use work.cfg5:config;\n"
      "endconfig\n"
      "config cfg5;\n"
      "  design work.adder;\n"
      "endconfig\n");
  EXPECT_EQ(StrOf(vpiConfig, "top.a1"), "work.cfg6");
  EXPECT_EQ(StrOf(vpiConfig, "top.a1.f1"), "work.cfg6");
  EXPECT_EQ(StrOf(vpiConfig, "top.a2"), "work.cfg5");
  EXPECT_EQ(StrOf(vpiConfig, "top.a2.f1"), "work.cfg5");
}

constexpr const char* kExampleMap =
    "library rtlLib top.v;\n"
    "library aLib adder.*;\n"
    "library gateLib adder.vg;\n";

constexpr const char* kSelectingRules =
    "config cfg1;\n"
    "  design rtlLib.top;\n"
    "  default liblist aLib rtlLib;\n"
    "  instance top.a2 liblist gateLib;\n"
    "endconfig\n";

class LibraryMapVpiRun : public LibraryBindingVpiRun {
 protected:
  void RunMapped(const std::string& map_text) {
    ASSERT_TRUE(design_.map.LoadMapFile(tmp_.Write("lib.map", map_text)));
    const std::string kAdder =
        "module adder; m f1(); endmodule\n"
        "module m; endmodule\n";
    ASSERT_TRUE(design_.Add(tmp_, "adder.v", kAdder));
    ASSERT_TRUE(design_.Add(tmp_, "adder.vg", kAdder));
    ASSERT_TRUE(design_.Add(tmp_, "top.v",
                            "module top; adder a1(); adder a2(); "
                            "endmodule\n"));
    RunConfiguredDesign(tmp_, design_, kSelectingRules, "cfg1");
    ASSERT_FALSE(design_.diag.HasErrors());
  }

  ScratchDir tmp_;
  BoundDesign design_;
};

TEST_F(LibraryMapVpiRun, ChildrenReportTheLibrariesTheirClausesChose) {
  RunMapped(kExampleMap);
  EXPECT_EQ(StrOf(vpiLibrary, "top.a1"), "aLib");
  EXPECT_EQ(StrOf(vpiLibrary, "top.a1.f1"), "aLib");
  EXPECT_EQ(StrOf(vpiLibrary, "top.a2"), "gateLib");
  EXPECT_EQ(StrOf(vpiLibrary, "top.a2.f1"), "gateLib");
}

TEST_F(LibraryMapVpiRun, DISABLED_TopReportsTheLibraryItsDesignStatementNamed) {
  RunMapped(kExampleMap);
  EXPECT_EQ(StrOf(vpiLibrary, "top"), "rtlLib");
  EXPECT_EQ(StrOf(vpiCell, "top"), "top");
}

TEST_F(LibraryMapVpiRun, ConfigMappedIntoALibraryReportsThatLibrary) {
  RunMapped(std::string(kExampleMap) + "library cfgLib cfg.sv;\n");
  EXPECT_EQ(StrOf(vpiConfig, "top.a2"), "cfgLib.cfg1");
}

TEST_F(LibraryMapVpiRun, ConfigLeftUnmappedReportsTheDefaultLibrary) {
  RunMapped(kExampleMap);
  EXPECT_EQ(StrOf(vpiConfig, "top.a2"), "work.cfg1");
}

}  // namespace
