#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaborator/elaborator.h"
#include "elaborator/separate_compilation_bind.h"
#include "fixture_scratch_dir.h"
#include "helpers_bound_from_library.h"
#include "helpers_reported_error.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

namespace {

constexpr std::string_view kKey = "viewport-exchange-key";

constexpr std::string_view kContainsNothing =
    "which is not an object contained within its envelope";

std::string ViewportLine(std::string_view object) {
  return "`pragma protect viewport = (object = \"" + std::string(object) +
         "\", access = \"r\")\n";
}

std::string Sealed(const std::string& authored) {
  return EncryptEnvelopes(authored, kKey);
}

struct CompiledDesign {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Arena arena;

  explicit CompiledDesign(const std::string& source) {
    PreprocConfig config;
    config.protect_key = std::string(kKey);
    Preprocessor pp(mgr, diag, config);
    std::string text = pp.Preprocess(mgr.AddFile("<test>", source));
    uint32_t fid = mgr.AddPreprocessedFile("<test>", text, pp.LineOrigins());
    Lexer lexer(mgr.FileContent(fid), fid, diag,
                TextOrigin::kPreprocessorOutput);
    Parser parser(lexer, arena, diag);
    Elaborator elab(arena, diag, parser.Parse());
    elab.Elaborate("t");
  }
};

struct BoundDesign {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Arena arena;

  explicit BoundDesign(const std::vector<std::string>& sources) {
    ScratchDir tmp;
    SeparateCompilationBinder binder(mgr, arena, diag);
    BoundFromALibrary(tmp, sources, kKey, binder);
  }
};

bool ContainsNothingReported(const DiagEngine& diag) {
  for (const auto& d : diag.Diagnostics()) {
    if (d.message.find(kContainsNothing) != std::string::npos) return true;
  }
  return false;
}

std::string ModuleEnvelopeNaming(std::string_view object) {
  return "`pragma protect begin\n" + ViewportLine(object) +
         "module secret(input a, output y);\n"
         "  wire inner;\n"
         "  leaf u();\n"
         "  assign y = a;\n"
         "endmodule\n"
         "module leaf;\n"
         "  logic q;\n"
         "endmodule\n"
         "`pragma protect end\n"
         "module other;\n"
         "  logic q;\n"
         "endmodule\n"
         "module t;\n"
         "  wire a, y;\n"
         "  secret s(.a(a), .y(y));\n"
         "  other o();\n"
         "endmodule\n";
}

std::string EnvelopeInsideModuleNaming(std::string_view object) {
  return "module secret;\n"
         "  wire outer;\n"
         "`pragma protect begin\n" +
         ViewportLine(object) +
         "  wire inner;\n"
         "`pragma protect end\n"
         "endmodule\n"
         "module t;\n"
         "  secret s();\n"
         "endmodule\n";
}

TEST(ViewportContainment, AnItemOfASealedElementIsContained) {
  CompiledDesign design(Sealed(ModuleEnvelopeNaming("secret.inner")));
  EXPECT_FALSE(ContainsNothingReported(design.diag));
}

TEST(ViewportContainment, APortOfASealedElementIsContained) {
  CompiledDesign design(Sealed(ModuleEnvelopeNaming("secret.y")));
  EXPECT_FALSE(ContainsNothingReported(design.diag));
}

TEST(ViewportContainment, AnItemReachedThroughASealedInstanceIsContained) {
  CompiledDesign design(Sealed(ModuleEnvelopeNaming("secret.u.q")));
  EXPECT_FALSE(ContainsNothingReported(design.diag));
}

TEST(ViewportContainment, ANameTheSealedElementDoesNotDeclareIsReported) {
  CompiledDesign design(Sealed(ModuleEnvelopeNaming("secret.missing")));
  EXPECT_TRUE(ReportedError(design.diag.Diagnostics(), kContainsNothing, 1,
                            "34.5.32.2"));
}

TEST(ViewportContainment, APathToACleartextObjectIsReported) {
  CompiledDesign design(Sealed(ModuleEnvelopeNaming("t.o.q")));
  EXPECT_TRUE(ReportedError(design.diag.Diagnostics(), kContainsNothing, 1,
                            "34.5.32.2"));
}

TEST(ViewportContainment, AnItemOfACleartextElementIsReported) {
  CompiledDesign design(Sealed(ModuleEnvelopeNaming("other.q")));
  EXPECT_TRUE(ContainsNothingReported(design.diag));
}

TEST(ViewportContainment, ABareNameOfAnItemTheEnvelopeDeclaresIsContained) {
  CompiledDesign design(Sealed(EnvelopeInsideModuleNaming("inner")));
  EXPECT_FALSE(ContainsNothingReported(design.diag));
}

TEST(ViewportContainment, ABareNameOfAnItemOutsideTheEnvelopeIsReported) {
  CompiledDesign design(Sealed(EnvelopeInsideModuleNaming("outer")));
  EXPECT_TRUE(ReportedError(design.diag.Diagnostics(), kContainsNothing, 1,
                            "34.5.32.2"));
}

TEST(ViewportContainment,
     AnItemOfAnElementACleartextEnvelopeDeclaresIsContained) {
  CompiledDesign design(ModuleEnvelopeNaming("secret.inner"));
  EXPECT_FALSE(ContainsNothingReported(design.diag));
}

TEST(ViewportContainment, ANameACleartextEnvelopeDoesNotDeclareIsReported) {
  CompiledDesign design(ModuleEnvelopeNaming("secret.missing"));
  EXPECT_TRUE(ReportedError(design.diag.Diagnostics(), kContainsNothing, 2,
                            "34.5.32.2"));
}

TEST(ViewportContainment, AnElementAfterACleartextEnvelopeIsNotContained) {
  CompiledDesign design(ModuleEnvelopeNaming("other.q"));
  EXPECT_TRUE(ReportedError(design.diag.Diagnostics(), kContainsNothing, 2,
                            "34.5.32.2"));
}

TEST(ViewportContainment,
     ABareNameOfAnItemACleartextEnvelopeDeclaresIsContained) {
  CompiledDesign design(EnvelopeInsideModuleNaming("inner"));
  EXPECT_FALSE(ContainsNothingReported(design.diag));
}

TEST(ViewportContainment, ABareNameOfAnItemBeforeACleartextEnvelopeIsReported) {
  CompiledDesign design(EnvelopeInsideModuleNaming("outer"));
  EXPECT_TRUE(ReportedError(design.diag.Diagnostics(), kContainsNothing, 4,
                            "34.5.32.2"));
}

TEST(ViewportContainment,
     AnItemACleartextEnvelopeDeclaresIsContainedWhenBound) {
  BoundDesign design({ModuleEnvelopeNaming("secret.inner")});
  EXPECT_FALSE(ContainsNothingReported(design.diag));
}

TEST(ViewportContainment,
     ANameACleartextEnvelopeDoesNotDeclareIsReportedWhenBound) {
  BoundDesign design({ModuleEnvelopeNaming("secret.missing")});
  EXPECT_TRUE(ReportedError(design.diag.Diagnostics(), kContainsNothing, 2,
                            "34.5.32.2"));
}

TEST(ViewportContainment, AnItemOfASealedElementIsContainedWhenBound) {
  BoundDesign design({Sealed(ModuleEnvelopeNaming("secret.u.q"))});
  EXPECT_FALSE(ContainsNothingReported(design.diag));
}

constexpr std::string_view kSecretRewritten =
    "module secret(input a, output y);\n"
    "  assign y = a;\n"
    "endmodule\n";

TEST(ViewportContainment, AViewportOfAReplacedElementIsNotReportedWhenBound) {
  BoundDesign design(
      {ModuleEnvelopeNaming("secret.inner"), std::string(kSecretRewritten)});
  EXPECT_FALSE(ContainsNothingReported(design.diag));
}

TEST(ViewportContainment,
     AViewportInsideAReplacedElementIsNotReportedWhenBound) {
  BoundDesign design(
      {EnvelopeInsideModuleNaming("inner"), "module secret;\nendmodule\n"});
  EXPECT_FALSE(ContainsNothingReported(design.diag));
}

TEST(ViewportContainment,
     AViewportNamingNothingIsReportedWhenAnotherElementIsReplaced) {
  BoundDesign design({ModuleEnvelopeNaming("secret.missing"),
                      "module other;\n  logic q;\nendmodule\n"});
  EXPECT_TRUE(ReportedError(design.diag.Diagnostics(), kContainsNothing, 2,
                            "34.5.32.2"));
}

}  // namespace
