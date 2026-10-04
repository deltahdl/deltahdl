#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaborator/elaborator.h"
#include "helpers_reported_error.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"
#include "preprocessor/protect_processing.h"

using namespace delta;

// §34.5.32.2 Description, for the viewport protect pragma keyword: the object
// name a viewport specifies shall be contained within the current envelope.
// §34.4 makes the envelope a lexical region, so the name is resolved against
// the declarations of the envelope's own text, from the scope the envelope
// stands in: a name led by a design element the envelope declares names an
// item of that element, and where the envelope stands inside a design element
// a bare name names an item the envelope declares there. The preprocessor
// keeps each decryption envelope's viewports in the SourceManager where the
// envelope closes, and ReportViewportsContainingNothing in
// src/elaborator/viewport_resolution.cpp reports a name that resolves to no
// declaration contained within the envelope, whether or not a PLI application
// is registered.

namespace {

constexpr std::string_view kKey = "viewport-exchange-key";

// The message a viewport naming nothing its envelope contains is reported with.
constexpr std::string_view kContainsNothing =
    "which is not an object contained within its envelope";

// The viewport pragma directive naming `object`.
std::string ViewportLine(std::string_view object) {
  return "`pragma protect viewport = (object = \"" + std::string(object) +
         "\", access = \"r\")\n";
}

// A text encrypted by this tool under kKey and compiled back: preprocessed
// under the key, which decrypts each envelope and records its viewports,
// parsed and elaborated from `t`.
struct CompiledSealedDesign {
  SourceManager mgr;
  DiagEngine diag{mgr};
  Arena arena;

  explicit CompiledSealedDesign(const std::string& authored) {
    PreprocConfig config;
    config.protect_key = std::string(kKey);
    Preprocessor pp(mgr, diag, config);
    std::string text =
        pp.Preprocess(mgr.AddFile("<test>", EncryptEnvelopes(authored, kKey)));
    uint32_t fid = mgr.AddPreprocessedFile("<test>", text, pp.LineOrigins());
    Lexer lexer(mgr.FileContent(fid), fid, diag,
                TextOrigin::kPreprocessorOutput);
    Parser parser(lexer, arena, diag);
    Elaborator elab(arena, diag, parser.Parse());
    elab.Elaborate("t");
  }

  bool Reported() const {
    for (const auto& d : diag.Diagnostics()) {
      if (d.message.find(kContainsNothing) != std::string::npos) return true;
    }
    return false;
  }
};

// An envelope sealing module `secret` whole, whose first line is a viewport
// naming `object`. The line the viewport stands on in the text the envelope
// recovers to is the first.
std::string SealedModuleNaming(std::string_view object) {
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

// An envelope standing inside module `secret`, declaring `inner` there, whose
// first line is a viewport naming `object`. `outer` is declared in the clear.
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

// An item of a design element the envelope declares is named through the
// element, and is contained within the envelope.
TEST(ViewportContainment, AnItemOfASealedElementIsContained) {
  CompiledSealedDesign design(SealedModuleNaming("secret.inner"));
  EXPECT_FALSE(design.Reported());
}

// A port of the element is one of its declarations too.
TEST(ViewportContainment, APortOfASealedElementIsContained) {
  CompiledSealedDesign design(SealedModuleNaming("secret.y"));
  EXPECT_FALSE(design.Reported());
}

// An instance the element declares leads on into the element it instantiates,
// which the envelope declares as well.
TEST(ViewportContainment, AnItemReachedThroughASealedInstanceIsContained) {
  CompiledSealedDesign design(SealedModuleNaming("secret.u.q"));
  EXPECT_FALSE(design.Reported());
}

// A name of something the element does not declare names nothing the envelope
// contains, and is reported where the viewport stands.
TEST(ViewportContainment, ANameTheSealedElementDoesNotDeclareIsReported) {
  CompiledSealedDesign design(SealedModuleNaming("secret.missing"));
  EXPECT_TRUE(ReportedError(design.diag.Diagnostics(), kContainsNothing, 1,
                            "34.5.32.2"));
}

// A path through the instances of the design, to an object of a module written
// in the clear, names an object outside the envelope: the instance it starts
// from is made by elaboration, not declared in the envelope's text.
TEST(ViewportContainment, APathToACleartextObjectIsReported) {
  CompiledSealedDesign design(SealedModuleNaming("t.o.q"));
  EXPECT_TRUE(ReportedError(design.diag.Diagnostics(), kContainsNothing, 1,
                            "34.5.32.2"));
}

// Nor is an element written in the clear one the envelope declares, though it
// declares an item of the same name.
TEST(ViewportContainment, AnItemOfACleartextElementIsReported) {
  CompiledSealedDesign design(SealedModuleNaming("other.q"));
  EXPECT_TRUE(design.Reported());
}

// Where the envelope stands inside a design element, an item it declares there
// is named bare.
TEST(ViewportContainment, ABareNameOfAnItemTheEnvelopeDeclaresIsContained) {
  CompiledSealedDesign design(EnvelopeInsideModuleNaming("inner"));
  EXPECT_FALSE(design.Reported());
}

// An item of the same element declared outside the envelope is not contained
// within it.
TEST(ViewportContainment, ABareNameOfAnItemOutsideTheEnvelopeIsReported) {
  CompiledSealedDesign design(EnvelopeInsideModuleNaming("outer"));
  EXPECT_TRUE(ReportedError(design.diag.Diagnostics(), kContainsNothing, 1,
                            "34.5.32.2"));
}

}  // namespace
