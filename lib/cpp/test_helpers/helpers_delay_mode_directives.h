#pragma once

#include <gtest/gtest.h>

#include <string>
#include <string_view>
#include <utility>

#include "common/types.h"
#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "fixture_parser.h"
#include "fixture_preprocessor.h"
#include "helpers_include_test_dir.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

struct DelayModeDirectiveSpec {
  std::string_view name;
  DelayModeDirective mode;
  std::string_view subclause;
};

inline constexpr DelayModeDirectiveSpec kDistributedDirective{
    "delay_mode_distributed", DelayModeDirective::kDistributed, "E.4"};
inline constexpr DelayModeDirectiveSpec kPathDirective{
    "delay_mode_path", DelayModeDirective::kPath, "E.5"};
inline constexpr DelayModeDirectiveSpec kUnitDirective{
    "delay_mode_unit", DelayModeDirective::kUnit, "E.6"};
inline constexpr DelayModeDirectiveSpec kZeroDirective{
    "delay_mode_zero", DelayModeDirective::kZero, "E.7"};

inline std::string Written(const DelayModeDirectiveSpec& d) {
  return "`" + std::string(d.name);
}

inline void ExpectTrailingTextStaysSourceText(const DelayModeDirectiveSpec& d) {
  for (const char* trailer : {"extra", "(1)", "3"}) {
    auto r = ParseWithPreprocessor(Written(d) + " " + trailer +
                                   "\nmodule m; endmodule\n");
    EXPECT_TRUE(
        ReportedError(r.diags, "expected top-level declaration", 1, "3.12.1"))
        << trailer;
  }
}

inline void ExpectDeclarationAfterItStaysSourceText(
    const DelayModeDirectiveSpec& d) {
  auto r =
      ParseWithPreprocessor(Written(d) + " wire w;\nmodule m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->delay_mode_directive, d.mode);
  ASSERT_EQ(r.cu->cu_items.size(), 1u);
  EXPECT_EQ(r.cu->cu_items[0]->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(r.cu->cu_items[0]->name, "w");
}

inline void ExpectModuleAfterItOnItsLineIsDeclared(
    const DelayModeDirectiveSpec& d) {
  auto r = ParseWithPreprocessor(Written(d) + " module m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->delay_mode_directive, d.mode);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
}

inline DelayModeDirective RecordedDelayMode(const Preprocessor& pp,
                                            std::string_view module) {
  for (const auto& entry : pp.ModuleDirectivesList()) {
    if (entry.module == module) return entry.delay_mode;
  }
  return DelayModeDirective::kNone;
}

struct PreprocessedDelayModes {
  PreprocFixture f;
  Preprocessor pp{f.mgr, f.diag, {}};
  explicit PreprocessedDelayModes(const std::string& src) {
    pp.Preprocess(f.mgr.AddFile("<test>", src));
  }
};

inline void ExpectCommentAfterItIsNoArgument(const DelayModeDirectiveSpec& d) {
  for (const char* comment : {" // delays", " /* delays */", "// delays"}) {
    PreprocessedDelayModes run(Written(d) + comment +
                               "\nmodule m;\nendmodule\n");
    EXPECT_TRUE(run.f.diag.Diagnostics().empty()) << comment;
    EXPECT_EQ(RecordedDelayMode(run.pp, "m"), d.mode) << comment;
  }
}

inline void ExpectALongerNameIsAMacroUse(const DelayModeDirectiveSpec& d) {
  PreprocessedDelayModes run(Written(d) + "x\nmodule m;\nendmodule\n");
  EXPECT_TRUE(ReportedError(run.f.diag.Diagnostics(),
                            "undefined macro '" + std::string(d.name) + "x'", 1,
                            "22.5.1"));
  EXPECT_EQ(RecordedDelayMode(run.pp, "m"), DelayModeDirective::kNone);
}

inline void ExpectRecordedForAMacromodule(const DelayModeDirectiveSpec& d) {
  PreprocessedDelayModes run(Written(d) + "\nmacromodule m;\nendmodule\n");
  EXPECT_FALSE(run.f.diag.HasErrors());
  ASSERT_EQ(run.pp.ModuleDirectivesList().size(), 1u);
  EXPECT_EQ(RecordedDelayMode(run.pp, "m"), d.mode);
}

inline void ExpectReadFromAnIncludedHeader(const DelayModeDirectiveSpec& d) {
  IncludeTestDir tmp;
  tmp.WriteFile("mode.svh", Written(d) + "\n");
  std::string src =
      "module a;\n"
      "endmodule\n"
      "`include \"mode.svh\"\n"
      "module b;\n"
      "endmodule\n";
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  pp.Preprocess(f.mgr.AddFile(tmp.WriteFile("main.sv", src).string(), src));
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(RecordedDelayMode(pp, "a"), DelayModeDirective::kNone);
  EXPECT_EQ(RecordedDelayMode(pp, "b"), d.mode);
}

inline void ExpectCarriedIntoALaterFile(const DelayModeDirectiveSpec& d) {
  PreprocFixture f;
  Preprocessor pp(f.mgr, f.diag, {});
  pp.Preprocess(
      f.mgr.AddFile("<file1>", "module a;\nendmodule\n" + Written(d) + "\n"));
  pp.Preprocess(f.mgr.AddFile("<file2>", "module b;\nendmodule\n"));
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_EQ(RecordedDelayMode(pp, "a"), DelayModeDirective::kNone);
  EXPECT_EQ(RecordedDelayMode(pp, "b"), d.mode);
}

inline void ExpectReportedAnywhereInAModuleDeclaration(
    const DelayModeDirectiveSpec& d) {
  std::string w = Written(d);
  std::pair<std::string, int> cases[] = {
      {"module t(\n" + w + "\n  input a);\nendmodule\n", 2},
      {"module t; " + w + " endmodule\n", 1},
      {"module o;\n  module n;\n" + w + "\n  endmodule\nendmodule\n", 3},
      {"module o;\n" + w + "\n  module n;\n  endmodule\nendmodule\n", 2},
      {"module o;\n  module n;\n  endmodule\n" + w + "\nendmodule\n", 4},
      {"macromodule t;\n" + w + "\nendmodule\n", 2},
      {"module t;\n  task k;\n" + w + "\n  endtask\nendmodule\n", 3},
      {"module t;\n  function void g;\n" + w + "\n  endfunction\nendmodule\n",
       3},
      {"module t;\n  if (1) begin : b\n" + w + "\n  end\nendmodule\n", 3},
      {"`define D " + w + "\nmodule t;\n`D\nendmodule\n", 3},
  };
  for (const auto& [src, line] : cases) {
    PreprocessedDelayModes run(src);
    EXPECT_TRUE(ReportedError(run.f.diag.Diagnostics(),
                              w + " illegal inside a design element", line,
                              d.subclause))
        << src;
  }
}

inline std::string InsideAnElementAheadOfAModule(
    const DelayModeDirectiveSpec& d, const std::string& element) {
  return element + " e;\n" + Written(d) + "\nend" + element +
         "\nmodule m;\nendmodule\n";
}

inline void ExpectAcceptedInsideAnInterfaceProgramOrPackage(
    const DelayModeDirectiveSpec& d) {
  for (const char* element : {"interface", "program", "package"}) {
    PreprocessedDelayModes run(InsideAnElementAheadOfAModule(d, element));
    EXPECT_TRUE(run.f.diag.Diagnostics().empty()) << element;
    EXPECT_EQ(RecordedDelayMode(run.pp, "m"), d.mode) << element;
  }
}

inline void ExpectAcceptedInsideAClass(const DelayModeDirectiveSpec& d) {
  PreprocessedDelayModes run(InsideAnElementAheadOfAModule(d, "class"));
  EXPECT_TRUE(run.f.diag.Diagnostics().empty());
  EXPECT_EQ(RecordedDelayMode(run.pp, "m"), d.mode);
}

inline void ExpectAfterTheLastModuleSetsNoModule(
    const DelayModeDirectiveSpec& d) {
  PreprocessedDelayModes run("module m;\nendmodule\n" + Written(d) + "\n");
  EXPECT_TRUE(run.f.diag.Diagnostics().empty());
  ASSERT_EQ(run.pp.ModuleDirectivesList().size(), 1u);
  EXPECT_EQ(RecordedDelayMode(run.pp, "m"), DelayModeDirective::kNone);
}

inline DelayModeDirective ElaboratedDelayMode(const RtlirDesign* design,
                                              std::string_view module) {
  for (const auto* mod : design->top_modules) {
    if (mod->name == module) return mod->delay_mode;
  }
  return DelayModeDirective::kNone;
}

inline void ExpectPropagatedToAMacromodule(const DelayModeDirectiveSpec& d) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      Written(d) + "\nmacromodule t;\nendmodule\n", f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(ElaboratedDelayMode(design, "t"), d.mode);
}

inline void ExpectSetInsideAnInterfaceProgramOrPackage(
    const DelayModeDirectiveSpec& d) {
  for (const char* element : {"interface", "program", "package"}) {
    ElabFixture f;
    auto* design = ElaborateWithPreprocessor(
        InsideAnElementAheadOfAModule(d, element), f, "m");
    ASSERT_NE(design, nullptr) << element;
    EXPECT_FALSE(f.has_errors) << element;
    EXPECT_EQ(ElaboratedDelayMode(design, "m"), d.mode) << element;
  }
}

inline void ExpectReachesEveryLaterModuleAndItsNestedModule(
    const DelayModeDirectiveSpec& d) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(Written(d) +
                                               "\nmodule child;\nendmodule\n"
                                               "module parent;\n"
                                               "  module inner;\n"
                                               "  endmodule\n"
                                               "  inner i();\n"
                                               "  child c();\n"
                                               "endmodule\n",
                                           f, "parent");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  const auto* parent = design->top_modules[0];
  EXPECT_EQ(parent->delay_mode, d.mode);
  ASSERT_EQ(parent->children.size(), 2u);
  for (const auto& child : parent->children) {
    ASSERT_NE(child.resolved, nullptr);
    EXPECT_EQ(child.resolved->delay_mode, d.mode) << child.resolved->name;
  }
}

inline void ExpectAnInterfaceAfterItTakesNoMode(
    const DelayModeDirectiveSpec& d) {
  ElabFixture f;
  auto* design =
      ElaborateWithPreprocessor(Written(d) +
                                    "\ninterface ifc;\nendinterface\n"
                                    "module top;\n"
                                    "  ifc i();\n"
                                    "endmodule\n",
                                f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  const auto* top = design->top_modules[0];
  EXPECT_EQ(top->delay_mode, d.mode);
  ASSERT_EQ(top->children.size(), 1u);
  ASSERT_NE(top->children[0].resolved, nullptr);
  EXPECT_EQ(top->children[0].resolved->delay_mode, DelayModeDirective::kNone);
}
